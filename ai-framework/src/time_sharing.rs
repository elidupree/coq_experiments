use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::time::Instant;

pub trait Worker: Send + Sync {
    type Key: Eq + Hash + Clone;
    type Workpiece;
    type Output;

    fn do_some_work(
        &mut self,
        workpiece: &mut Self::Workpiece,
        context: &mut WorkContext,
    ) -> WorkResult<Self::Output>;
}

struct ActiveWorker<W: Worker> {
    time_used: f64,
    key: W::Key,
}

impl<W: Worker> Eq for ActiveWorker<W> {}

impl<W: Worker> PartialEq<Self> for ActiveWorker<W> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl<W: Worker> PartialOrd<Self> for ActiveWorker<W> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<W: Worker> Ord for ActiveWorker<W> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.time_used.total_cmp(&other.time_used)
    }
}

pub struct TimeSharer<W: Worker> {
    workers: HashMap<W::Key, W>,
    active_workers: BinaryHeap<ActiveWorker<W>>,
    idle_workers: HashSet<W::Key>,

    idle_worker_test_queue: VecDeque<W::Key>,
}

impl<W: Worker> Default for TimeSharer<W> {
    fn default() -> Self {
        TimeSharer {
            workers: Default::default(),
            active_workers: Default::default(),
            idle_workers: Default::default(),
            idle_worker_test_queue: Default::default(),
        }
    }
}

pub enum WorkResult<R> {
    Idle,
    StillWorking,
    ProducedOutput(R),
}

#[derive(Default)]
pub struct WorkContext {
    going_idle: bool,
    completely_done: bool,
}

impl WorkContext {
    pub fn go_idle(&mut self) {
        self.going_idle = true
    }
    pub fn completely_done(&mut self) {
        self.completely_done = true
    }
}

impl<W: Worker> TimeSharer<W> {
    fn now_time(&self) -> f64 {
        match self.active_workers.peek() {
            None => 0.0,
            Some(w) => w.time_used,
        }
    }

    pub fn add_worker(&mut self, key: W::Key, worker: W) {
        self.idle_worker_test_queue.push_back(key.clone());
        self.workers.insert(key.clone(), worker);
        self.active_workers.push(ActiveWorker {
            time_used: self.now_time(),
            key,
        })
    }

    pub fn get<Q: Eq + Hash>(&self, key: &Q) -> Option<&W>
    where
        W::Key: Borrow<Q>,
    {
        self.workers.get(key)
    }

    pub fn get_mut<Q: Eq + Hash>(&mut self, key: &Q) -> Option<&mut W>
    where
        W::Key: Borrow<Q>,
    {
        self.workers.get_mut(key)
    }

    pub fn wake<Q: Eq + Hash>(&mut self, key: &Q)
    where
        W::Key: Borrow<Q>,
    {
        if let Some(key) = self.idle_workers.take(key) {
            self.active_workers.push(ActiveWorker {
                time_used: self.now_time(),
                key,
            });
        }
    }

    pub fn wake_all(&mut self) {
        let time_used = self.now_time();
        for key in self.idle_workers.drain() {
            self.active_workers.push(ActiveWorker { time_used, key });
        }
    }

    pub fn do_some_work(&mut self, workpiece: &mut W::Workpiece) -> WorkResult<W::Output> {
        if let Some(k) = self.idle_worker_test_queue.pop_front() {
            if self.idle_workers.contains(&k) {
                let mut context = WorkContext::default();
                if matches!(
                    self.workers
                        .get_mut(&k)
                        .unwrap()
                        .do_some_work(workpiece, &mut context),
                    WorkResult::Idle
                ) {
                    panic!("Task should have been woken!")
                }
            }
            self.idle_worker_test_queue.push_back(k);
        }

        if let Some(mut worker) = self.active_workers.pop() {
            let start = Instant::now();
            let mut context = WorkContext::default();
            let result = self
                .workers
                .get_mut(&worker.key)
                .unwrap()
                .do_some_work(workpiece, &mut context);
            worker.time_used += start.elapsed().as_secs_f64();
            if context.completely_done {
                self.workers.remove(&worker.key);
            } else {
                if context.going_idle || matches!(result, WorkResult::Idle) {
                    self.idle_workers.insert(worker.key);
                } else {
                    self.active_workers.push(worker);
                }
            }

            if matches!(result, WorkResult::Idle) {
                WorkResult::StillWorking
            } else {
                result
            }
        } else {
            WorkResult::Idle
        }
    }
}

pub struct TimeSharerOwned<W: Worker> {
    workpiece: W::Workpiece,
    sharer: TimeSharer<W>,
}

impl<W: Worker> Default for TimeSharerOwned<W>
where
    W::Workpiece: Default,
{
    fn default() -> Self {
        TimeSharerOwned {
            workpiece: Default::default(),
            sharer: Default::default(),
        }
    }
}

impl<W: Worker> TimeSharerOwned<W> {
    pub fn new(workpiece: W::Workpiece) -> Self {
        TimeSharerOwned {
            workpiece,
            sharer: TimeSharer::default(),
        }
    }

    pub fn get<Q: Eq + Hash>(&self, key: &Q) -> Option<&W>
    where
        W::Key: Borrow<Q>,
    {
        self.sharer.get(key)
    }

    pub fn get_mut<Q: Eq + Hash>(&mut self, key: &Q) -> Option<&mut W>
    where
        W::Key: Borrow<Q>,
    {
        self.sharer.get_mut(key)
    }

    pub fn inner(&self) -> &W::Workpiece {
        &self.workpiece
    }
    pub fn inner_mut(&mut self) -> &mut W::Workpiece {
        &mut self.workpiece
    }
    pub fn into_inner(self) -> W::Workpiece {
        self.workpiece
    }

    pub fn add_worker(&mut self, key: W::Key, worker: W) {
        self.sharer.add_worker(key, worker);
    }

    pub fn wake<Q: Eq + Hash>(&mut self, key: &Q)
    where
        W::Key: Borrow<Q>,
    {
        self.sharer.wake(key);
    }

    pub fn do_some_work(&mut self) -> WorkResult<W::Output> {
        self.sharer.do_some_work(&mut self.workpiece)
    }
}
