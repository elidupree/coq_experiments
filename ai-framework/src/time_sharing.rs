use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::time::Instant;

pub trait Worker: Send + Sync {
    type Key: Eq + Hash + Clone + Debug;
    type Workpiece;
    type Output;

    fn do_some_work(
        &mut self,
        workpiece: &mut Self::Workpiece,
        context: &mut WorkContext,
    ) -> WorkResult<Self::Output>;
}
pub type WorkerFn<Workpiece, Output> =
    Box<dyn (FnMut(&mut Workpiece, &mut WorkContext) -> WorkResult<Output>) + Send + Sync>;

impl<Workpiece, Output> Worker for WorkerFn<Workpiece, Output> {
    type Key = usize;
    type Workpiece = Workpiece;
    type Output = Output;

    fn do_some_work(
        &mut self,
        workpiece: &mut Self::Workpiece,
        context: &mut WorkContext,
    ) -> WorkResult<Self::Output> {
        (self)(workpiece, context)
    }
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

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
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

    pub fn remove<Q: Eq + Hash>(&mut self, key: &Q) -> Option<(W::Key, W)>
    where
        W::Key: Borrow<Q>,
    {
        self.workers.remove_entry(key)
    }

    pub fn workers(&self) -> impl Iterator<Item = &W> + '_ {
        self.workers.values()
    }

    pub fn workers_mut(&mut self) -> impl Iterator<Item = &mut W> + '_ {
        self.workers.values_mut()
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
                if !matches!(
                    self.workers
                        .get_mut(&k)
                        .unwrap()
                        .do_some_work(workpiece, &mut context),
                    WorkResult::Idle
                ) {
                    panic!("Task `{k:?}` should have been woken!")
                }
            }
            if self.workers.contains_key(&k) {
                self.idle_worker_test_queue.push_back(k);
            }
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

pub struct TimeSharerKeyless<W: Worker> {
    sharer: TimeSharer<W>,
    next_id: usize,
}

impl<W: Worker> Deref for TimeSharerKeyless<W> {
    type Target = TimeSharer<W>;
    fn deref(&self) -> &Self::Target {
        &self.sharer
    }
}
impl<W: Worker> DerefMut for TimeSharerKeyless<W> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.sharer
    }
}

impl<W: Worker> Default for TimeSharerKeyless<W> {
    fn default() -> Self {
        TimeSharerKeyless {
            sharer: Default::default(),
            next_id: 0,
        }
    }
}

impl<W: Worker<Key = usize>> TimeSharerKeyless<W> {
    pub fn add_worker(&mut self, worker: W) {
        self.sharer.add_worker(self.next_id, worker);
        self.next_id += 1;
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

    pub fn workers(&self) -> impl Iterator<Item = &W> + '_ {
        self.sharer.workers()
    }

    pub fn workers_mut(&mut self) -> impl Iterator<Item = &mut W> + '_ {
        self.sharer.workers_mut()
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
