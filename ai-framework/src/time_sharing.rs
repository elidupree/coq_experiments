use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::hash::Hash;
use std::time::Instant;

type Task<Context, R> = Box<dyn FnMut(&mut Context) -> WorkResult<R> + Send + Sync>;
struct ActiveWorker<Key, Context, R> {
    time_used: f64,
    key: Key,
    task: Task<Context, R>,
}

impl<Key, Context, R> Eq for ActiveWorker<Key, Context, R> {}

impl<Key, Context, R> PartialEq<Self> for ActiveWorker<Key, Context, R> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<Key, Context, R> PartialOrd<Self> for ActiveWorker<Key, Context, R> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<Key, Context, R> Ord for ActiveWorker<Key, Context, R> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time_used.total_cmp(&other.time_used)
    }
}

pub struct TimeSharer<Key, Context, R> {
    active_workers: BinaryHeap<ActiveWorker<Key, Context, R>>,
    idle_workers: HashMap<Key, Task<Context, R>>,

    idle_worker_test_queue: VecDeque<Key>,
}

impl<Key, Context, R> Default for TimeSharer<Key, Context, R> {
    fn default() -> Self {
        TimeSharer {
            active_workers: Default::default(),
            idle_workers: Default::default(),
            idle_worker_test_queue: Default::default(),
        }
    }
}

pub enum WorkResult<R> {
    NothingToDo,
    StillWorking(R),
}

impl<Key: Hash + Eq + Clone, Context, R> TimeSharer<Key, Context, R> {
    fn now_time(&self) -> f64 {
        match self.active_workers.peek() {
            None => 0.0,
            Some(w) => w.time_used,
        }
    }

    pub fn add_worker(
        &mut self,
        key: Key,
        worker: impl FnMut(&mut Context) -> WorkResult<R> + Send + Sync + 'static,
    ) {
        self.idle_worker_test_queue.push_back(key.clone());
        self.active_workers.push(ActiveWorker {
            time_used: self.now_time(),
            key,
            task: Box::new(worker),
        })
    }

    pub fn wake<Q: Eq + Hash>(&mut self, key: &Q)
    where
        Key: Borrow<Q>,
    {
        if let Some((key, task)) = self.idle_workers.remove_entry(key) {
            self.active_workers.push(ActiveWorker {
                time_used: self.now_time(),
                key,
                task,
            });
        }
    }

    pub fn wake_all(&mut self) {
        let time_used = self.now_time();
        for (key, task) in self.idle_workers.drain() {
            self.active_workers.push(ActiveWorker {
                time_used,
                key,
                task,
            });
        }
    }

    pub fn do_some_work(&mut self, context: &mut Context) -> WorkResult<R> {
        if let Some(k) = self.idle_worker_test_queue.pop_front() {
            if let Some(task) = self.idle_workers.get_mut(&k) {
                if !matches!((task)(context), WorkResult::NothingToDo) {
                    panic!("Task should have been woken!")
                }
            }
            self.idle_worker_test_queue.push_back(k);
        }

        if let Some(mut worker) = self.active_workers.pop() {
            let start = Instant::now();
            let result = (worker.task)(context);
            worker.time_used += start.elapsed().as_secs_f64();
            match result {
                WorkResult::NothingToDo => {
                    self.idle_workers.insert(worker.key, worker.task);
                }
                WorkResult::StillWorking(_) => {
                    self.active_workers.push(worker);
                }
            }

            result
        } else {
            WorkResult::NothingToDo
        }
    }
}

#[derive(Default)]
pub struct TimeSharerOwned<Key, Context, R> {
    context: Context,
    sharer: TimeSharer<Key, Context, R>,
}

impl<Key: Hash + Eq + Clone, Context, R> TimeSharerOwned<Key, Context, R> {
    pub fn new(context: Context) -> Self {
        TimeSharerOwned {
            context,
            sharer: TimeSharer::default(),
        }
    }

    pub fn inner(&self) -> &Context {
        &self.context
    }
    pub fn inner_mut(&mut self) -> &mut Context {
        &mut self.context
    }
    pub fn into_inner(self) -> Context {
        self.context
    }

    pub fn add_worker(
        &mut self,
        key: Key,
        worker: impl FnMut(&mut Context) -> WorkResult<R> + Send + Sync + 'static,
    ) {
        self.sharer.add_worker(key, worker);
    }

    pub fn wake<Q: Eq + Hash>(&mut self, key: &Q)
    where
        Key: Borrow<Q>,
    {
        self.sharer.wake(key);
    }

    pub fn do_some_work(&mut self) -> WorkResult<R> {
        self.sharer.do_some_work(&mut self.context)
    }
}
