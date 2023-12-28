pub mod serialization;

use internment::ArcIntern;
use siphasher::sip128::{Hasher128, SipHasher};
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::ops::Deref;
use std::ptr;

/// Like Arc<T> but it's interned and always compares eq/ord/etc by its hash,
/// especially intended for things that would otherwise get exponential in naive size
pub struct HashCapsule<T: Eq + Hash + Send + Sync + 'static>(ArcIntern<HashCapsuleInner<T>>);

impl<T: Eq + Hash + Send + Sync + 'static> Clone for HashCapsule<T> {
    fn clone(&self) -> Self {
        HashCapsule(self.0.clone())
    }
}

pub struct HashCapsuleInner<T> {
    hash: u128,
    value: T,
}

fn compute_hash<T: Hash>(t: &T) -> u128 {
    // random values generated to hardcode here
    let mut hasher = SipHasher::new_with_keys(0xcdcf8354ea3a1528, 0x5319c22d8152c3bd);
    t.hash(&mut hasher);
    hasher.finish128().as_u128()
}

impl<T: Eq + Hash + Send + Sync + 'static> PartialEq for HashCapsule<T> {
    fn eq(&self, other: &Self) -> bool {
        let a: &T = self;
        let b: &T = other;
        ptr::eq(a, b)
    }
}
impl<T> PartialEq for HashCapsuleInner<T> {
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash
    }
}
impl<T: Eq + Hash + Send + Sync + 'static> PartialOrd for HashCapsule<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: Eq + Hash + Send + Sync + 'static> Ord for HashCapsule<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.hash().cmp(&other.hash())
    }
}
impl<T: Eq + Hash + Send + Sync + 'static> Eq for HashCapsule<T> {}
impl<T> Eq for HashCapsuleInner<T> {}
impl<T: Eq + Hash + Send + Sync + 'static> Hash for HashCapsule<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash.hash(state)
    }
}
impl<T> Hash for HashCapsuleInner<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state)
    }
}
impl<T: Eq + Hash + Send + Sync + 'static + Debug> Debug for HashCapsule<T> {
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
                write!(f, "HashCapsule#{:x}", self.hash())
            }
        })
    }
}

impl<T: Eq + Hash + Send + Sync + 'static> Deref for HashCapsule<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0.value
    }
}

impl<T: Eq + Hash + Send + Sync + 'static> AsRef<T> for HashCapsule<T> {
    fn as_ref(&self) -> &T {
        self
    }
}
impl<T: Eq + Hash + Send + Sync + 'static> HashCapsule<T> {
    pub fn hash(&self) -> u128 {
        self.0.hash
    }
}
impl<T: Eq + Hash + Send + Sync + 'static + Clone + Debug + Default> Default for HashCapsule<T> {
    fn default() -> Self {
        HashCapsule::new(T::default())
    }
}
impl<T: Eq + Hash + Send + Sync + 'static + Clone + Debug> HashCapsule<T> {
    pub fn new(value: T) -> HashCapsule<T> {
        let hash = compute_hash(&value);
        let arc = ArcIntern::new(HashCapsuleInner {
            hash,
            value: value.clone(),
        });
        // Security: if someone were to hypothetically find collisions in Siphash128, we don't want to let them leverage that into also violating correctness of HashCapsule
        assert_eq!(
            arc.value, value,
            "Apparent hash collision in HashCapsule::new()"
        );
        HashCapsule(arc)
    }
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

pub type BuildHasherForHashCapsules = BuildHasherDefault<TrivialHasherForHashCapsules>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn reuse() {
        let a = HashCapsule::new(2);
        let b = HashCapsule::new(2);
        let c = HashCapsule::new(3);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(std::ptr::eq(&*a, &*b));
        assert!(!std::ptr::eq(&*a, &*c));
    }

    #[test]
    fn efficiency() {
        #[derive(Clone, Eq, PartialEq, Hash, Debug)]
        struct ExpansionBomb(Vec<HashCapsule<ExpansionBomb>>);
        let mut latest = HashCapsule::new(ExpansionBomb(vec![]));
        for _ in 0..100 {
            latest = HashCapsule::new(ExpansionBomb(vec![latest.clone(), latest]));
        }
    }

    #[test]
    fn hashset() {
        let mut set = HashSet::with_hasher(BuildHasherForHashCapsules::default());
        set.insert(HashCapsule::new(2));
        set.insert(HashCapsule::new(2));
        set.insert(HashCapsule::new(3));
        assert!(set.contains(&HashCapsule::new(2)));
        assert!(set.contains(&HashCapsule::new(3)));
        assert!(!set.contains(&HashCapsule::new(4)));
    }
}
