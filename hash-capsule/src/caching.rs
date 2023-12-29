use std::sync::Mutex;

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

impl<T: Clone> SingleCache<T> {
    pub fn get(&self, compute: impl FnOnce() -> T) -> T {
        let guard = self.value.lock().unwrap();
        if let Some(value) = &*guard {
            value.clone()
        } else {
            drop(guard);
            let value = compute();
            (*self.value.lock().unwrap()) = Some(value.clone());
            value
        }
    }
}
