use crate::{CapsuleContents, HashCapsule, HashCapsuleWeak};
use std::collections::hash_map::RandomState;
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hash};
use std::sync::{Arc, Mutex};

impl<T: CapsuleContents> Downgrade<HashCapsuleWeak<T>> for HashCapsule<T> {
    fn downgrade(&self) -> HashCapsuleWeak<T> {
        HashCapsuleWeak {
            hash: self.hash,
            pointer: Arc::downgrade(&self.0),
        }
    }

    fn upgrade(weak: &HashCapsuleWeak<T>) -> Option<Self> {
        weak.pointer.upgrade().map(HashCapsule)
    }
}

pub trait Downgrade<T>: Sized {
    fn downgrade(&self) -> T;
    fn upgrade(weak: &T) -> Option<Self>;
}

impl<T: Clone> Downgrade<T> for T {
    fn downgrade(&self) -> T {
        self.clone()
    }

    fn upgrade(weak: &T) -> Option<Self> {
        Some(weak.clone())
    }
}

pub struct SingleCache<T> {
    value: Mutex<Option<T>>,
}

impl<T> Default for SingleCache<T> {
    fn default() -> Self {
        SingleCache {
            value: Mutex::new(None),
        }
    }
}

impl<T> SingleCache<T> {
    pub fn get<X: Downgrade<T>>(&self, compute: impl FnOnce() -> X) -> X {
        let guard = self.value.lock().unwrap();
        if let Some(value) = &*guard {
            if let Some(value) = X::upgrade(value) {
                return value;
            }
        }

        drop(guard);
        let value = compute();
        (*self.value.lock().unwrap()) = Some(value.downgrade());
        value
    }

    pub fn cleanup(&mut self, callback: impl FnOnce(T)) {
        self.value.get_mut().unwrap().take().map(callback);
    }
}

pub struct CacheMap<K, V, S = RandomState> {
    value: Mutex<HashMap<K, V, S>>,
}

impl<K, V, S: Default> Default for CacheMap<K, V, S> {
    fn default() -> Self {
        CacheMap {
            value: Default::default(),
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> CacheMap<K, V, S> {
    pub fn get<X: Downgrade<V>>(&self, key: K, compute: impl FnOnce() -> X) -> X {
        let guard = self.value.lock().unwrap();
        if let Some(value) = guard.get(&key) {
            if let Some(value) = X::upgrade(value) {
                return value;
            }
        }

        drop(guard);
        let value = compute();
        self.value.lock().unwrap().insert(key, value.downgrade());
        value
    }

    pub fn forget(&self, key: &K) {
        let result = self.value.lock().unwrap().remove(key);
        assert!(result.is_some(), "forget() should only be called when cleaning up back references, and I don't think there should be any weird cases with cleaning up back references, so let's fail hard here to make sure my expectations aren't violated");
    }

    pub fn cleanup(&mut self, mut callback: impl FnMut(K, V)) {
        for (k, v) in self.value.get_mut().unwrap().drain() {
            callback(k, v);
        }
    }
}

pub struct BackrefSet<K, S = RandomState> {
    value: Mutex<HashSet<K, S>>,
}

impl<K, S: Default> Default for BackrefSet<K, S> {
    fn default() -> Self {
        BackrefSet {
            value: Default::default(),
        }
    }
}

impl<K: Eq + Hash, S: BuildHasher> BackrefSet<K, S> {
    pub fn insert(&self, key: K) {
        self.value.lock().unwrap().insert(key);
    }

    pub fn forget(&self, key: &K) {
        let result = self.value.lock().unwrap().remove(key);
        assert!(result, "forget() should only be called when cleaning up back references, and I don't think there should be any weird cases with cleaning up back references, so let's fail hard here to make sure my expectations aren't violated");
    }

    pub fn cleanup(&mut self, mut callback: impl FnMut(K)) {
        for k in self.value.get_mut().unwrap().drain() {
            callback(k);
        }
    }
}

// pub trait Relationship {
//     type Counterpart: Relationship;
// }
//
// pub struct RelationshipCache<R: Relationship> {}
//
// impl<R: Relationship> Drop for RelationshipCache<R> {
//     fn drop(&mut self) {
//         todo!()
//     }
// }
