#![feature(lazy_cell)]

pub mod caching;
pub mod serialization;

// use internment::ArcIntern;
use siphasher::sip128::{Hasher128, SipHasher};
use std::borrow::Borrow;
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::ops::Deref;
use std::ptr;
use std::sync::{Arc, Weak};

/****************************************************
                Type definitions
****************************************************/

/// Like Arc<T> but it's interned and always compares eq/ord/etc by its hash,
/// especially intended for things that would otherwise get exponential in naive size
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Hash, PartialOrd, Ord)]
pub struct HashCapsule<T: CapsuleContents>(Arc<HashCapsuleInner<T>>);

pub trait CapsuleContents: HashCapsuleIntern + Eq + Hash + Debug + Send + Sync + 'static {
    type Caches: Default + Send + Sync + 'static;
    #[allow(unused_variables)]
    fn cleanup(&self, caches: &Self::Caches) {}
}

impl<T: CapsuleContents> Clone for HashCapsule<T> {
    fn clone(&self) -> Self {
        HashCapsule(self.0.clone())
    }
}

pub struct HashCapsuleInner<T: CapsuleContents> {
    pub hash: u128,
    pub value: T,
    pub caches: T::Caches,
}

/****************************************************
                    Hashing
****************************************************/

fn compute_hash<T: Hash>(t: &T) -> u128 {
    // random values that I generated to hardcode here
    let mut hasher = SipHasher::new_with_keys(0xcdcf8354ea3a1528, 0x5319c22d8152c3bd);
    t.hash(&mut hasher);
    hasher.finish128().as_u128()
}

#[derive(Clone, Default)]
pub struct TrivialHasherForHashCapsules {
    state: u64,
}

impl Hasher for TrivialHasherForHashCapsules {
    fn finish(&self) -> u64 {
        self.state
    }
    fn write(&mut self, _bytes: &[u8]) {
        panic!("TrivialHasherForHashCapsules received something that wasn't u128 (and therefore not a HashCapsule)")
    }
    // fn write_u64(&mut self, i: u64) {
    //     self.state = i;
    // }
    fn write_u128(&mut self, i: u128) {
        self.state = i as u64;
    }
}

// impl<T: CapsuleContents> HashCapsule<T> {
//     pub fn get_hash(&self) -> u128 {
//         self.0.hash
//     }
// }

pub type BuildHasherForHashCapsules = BuildHasherDefault<TrivialHasherForHashCapsules>;

/****************************************************
                   Interning
****************************************************/

pub trait HashCapsuleIntern {
    fn with_intern_map<R>(
        callback: impl FnOnce(
            &mut HashMap<u128, Weak<HashCapsuleInner<Self>>, BuildHasherForHashCapsules>,
        ) -> R,
    ) -> R;
}

#[macro_export]
macro_rules! hash_capsule_intern {
    ($T:ident) => {
        mod hash_capsule_intern {
            use std::collections::HashMap;
            use std::sync::{LazyLock, Mutex, Weak};
            use $crate::{HashCapsuleInner, HashCapsuleIntern, BuildHasherForHashCapsules};
            use super::$T as T;

            static INTERN: LazyLock<
                Mutex<
                    HashMap<
                        u128,
                        std::sync::Weak<HashCapsuleInner<T>>,
                        BuildHasherForHashCapsules,
                    >,
                >,
            > = LazyLock::new(|| Mutex::default());

            impl HashCapsuleIntern for T {
                fn with_intern_map<R>(
                    callback: impl FnOnce(
                        &mut HashMap<
                            u128,
                            Weak<HashCapsuleInner<Self>>,
                            BuildHasherForHashCapsules,
                        >,
                    ) -> R,
                ) -> R {
                    callback(&mut INTERN.lock().unwrap())
                }
            }
        }
    };
}

impl<T: CapsuleContents> HashCapsule<T> {
    pub fn new(value: T) -> HashCapsule<T> {
        let hash = compute_hash(&value);
        T::with_intern_map(|map| {
            match map.entry(hash) {
                Entry::Occupied(mut entry) => {
                    if let Some(arc) = entry.get().upgrade() {
                        // Security: if someone were to hypothetically find collisions in Siphash128, we don't want to let them leverage that into also violating correctness of HashCapsule
                        assert_eq!(arc.value, value, "Apparent hash collision in a HashCapsule");
                        HashCapsule(arc)
                    } else {
                        let caches = Default::default();
                        let arc = Arc::new(HashCapsuleInner {
                            hash,
                            value,
                            caches,
                        });
                        entry.insert(Arc::downgrade(&arc));
                        HashCapsule(arc)
                    }
                }
                Entry::Vacant(entry) => {
                    let caches = Default::default();
                    let arc = Arc::new(HashCapsuleInner {
                        hash,
                        value,
                        caches,
                    });
                    entry.insert(Arc::downgrade(&arc));
                    HashCapsule(arc)
                }
            }
        })
    }
}

impl<T: CapsuleContents> Drop for HashCapsuleInner<T> {
    fn drop(&mut self) {
        // When we drop the last reference to an object, we also want to clean up the memory usage in the map
        self.value.cleanup(&self.caches);
        T::with_intern_map(|map| {
            match map.entry(self.hash) {
                Entry::Occupied(entry) => {
                    // With multithreading, it's possible that while the strong count was 0, some other thread created a new copy of the same object. In that case, we don't have anything that needs doing here
                    if entry.get().strong_count() == 0 {
                        entry.remove();
                    }
                }
                Entry::Vacant(_entry) => {
                    // This case is even weirder – you'd have to have created a new object, AND fully deleted it, before we finished dropping the old one – but it's hypothetically possible, and doesn't require any additional action here
                }
            }
        })
    }
}

/****************************************************
             Interesting trait impls
****************************************************/

impl<T: CapsuleContents + Debug> Debug for HashCapsule<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        thread_local! {static RECURSION_LEVELS: Cell<usize> = Cell::new(0);}
        RECURSION_LEVELS.with(|levels| {
            let level = levels.get();
            if level < 3 {
                levels.set(level + 1);
                let result = self.0.value.fmt(f);
                levels.set(level);
                result
            } else {
                write!(f, "HashCapsule#{:x}", self.hash)
            }
        })
    }
}

/****************************************************
             Boilerplate trait impls
****************************************************/

impl<T: CapsuleContents> Eq for HashCapsuleInner<T> {}
impl<T: CapsuleContents> PartialEq for HashCapsuleInner<T> {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
}
// HashCapsule itself can implement equality even more efficiently by comparing pointers rather than following them to the hashes
impl<T: CapsuleContents> Eq for HashCapsule<T> {}
impl<T: CapsuleContents> PartialEq for HashCapsule<T> {
    fn eq(&self, other: &Self) -> bool {
        let a: &T = self;
        let b: &T = other;
        ptr::eq(a, b)
    }
}
impl<T: CapsuleContents> PartialOrd for HashCapsuleInner<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: CapsuleContents> Ord for HashCapsuleInner<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.hash.cmp(&other.hash)
    }
}
impl<T: CapsuleContents> Hash for HashCapsuleInner<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}

impl<T: CapsuleContents> Deref for HashCapsule<T> {
    type Target = HashCapsuleInner<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: CapsuleContents> Deref for HashCapsuleInner<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T: CapsuleContents> AsRef<T> for HashCapsule<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T: CapsuleContents> Borrow<u128> for HashCapsule<T> {
    fn borrow(&self) -> &u128 {
        &self.0.hash
    }
}

impl<T: CapsuleContents + Clone + Debug + Default> Default for HashCapsule<T> {
    fn default() -> Self {
        HashCapsule::new(T::default())
    }
}

/****************************************************
                     Tests
****************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[derive(Clone, Eq, PartialEq, Hash, Debug)]
    struct TestContents(Vec<HashCapsule<TestContents>>);

    hash_capsule_intern!(TestContents);
    impl CapsuleContents for TestContents {
        type Caches = ();
    }

    #[test]
    fn reuse() {
        let a = HashCapsule::new(TestContents(vec![]));
        let b = HashCapsule::new(TestContents(vec![]));
        let c = HashCapsule::new(TestContents(vec![a.clone()]));
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(ptr::eq(&*a, &*b));
        assert!(!ptr::eq(&*a, &*c));
    }

    #[test]
    fn efficiency() {
        let mut expansion_bomb = HashCapsule::new(TestContents(vec![]));
        for _ in 0..100 {
            expansion_bomb =
                HashCapsule::new(TestContents(vec![expansion_bomb.clone(), expansion_bomb]));
        }
    }

    #[test]
    fn hashset() {
        let mut set = HashSet::with_hasher(BuildHasherForHashCapsules::default());
        let a = HashCapsule::new(TestContents(vec![]));
        let b = HashCapsule::new(TestContents(vec![a.clone()]));
        let c = HashCapsule::new(TestContents(vec![b.clone()]));
        set.insert(a.clone());
        set.insert(a.clone());
        set.insert(b.clone());
        assert!(set.contains(&a));
        assert!(set.contains(&b));
        assert!(!set.contains(&c));
    }
}
