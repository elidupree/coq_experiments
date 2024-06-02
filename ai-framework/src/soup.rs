//TODO remove these:
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::model_shared::{id_type, Array, InputOutputSampleBatch};
use ordered_float::OrderedFloat;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Instant;

id_type!(QuestionFamilyId);
id_type!(EnsembleId);
id_type!(StrategyId);
id_type!(OptimizerId);

/// The interface a strategy uses to delegate to other strategies during its evaluation.
///
/// Strategies can be arbitrary functions of the inputs, but aren't generally allowed to depend on the rest of the soup. However, they can explicitly query other strategies, by giving a strategy id and inputs. Thus, there needs to be a type allowing access to query strategies, and nothing else. That is StrategyEvaluationContext.
pub struct StrategyEvaluationContext<'a> {
    soup: &'a mut Soup,
}

impl<'a> StrategyEvaluationContext<'a> {
    /// Query an existing strategy, returning that strategy's outputs for the given input.
    ///
    /// Outputs may be cached, so the other strategy's evaluation function won't necessarily be run the second time. This function is also responsible for tracking time used, to attribute it to strategies and optimizers appropriately. However, those things are invisible to the strategy calling `query`.
    pub fn query(&mut self, strategy: StrategyId, inputs: Array) -> Array {
        todo!()
    }
}

/// A strategy for answering questions that belong to a particular question family.
#[enum_delegate::register]
pub trait Strategy {
    /// Evaluate this strategy's outputs for the given input.
    ///
    /// The implementor may assume that the inputs are the correct array-size for the question family it gives answers for. (We would like to enforce this on the type level, but Rust's type system isn't powerful enough.)
    ///
    /// `context` allows this strategy to query other strategies. (See the documentation for StrategyEvaluationContext.)
    fn evaluate(&self, context: &mut StrategyEvaluationContext, input: Array) -> Array;

    // fn gradient()
}

/// An enum hard-coding all Strategy implementors.
///
/// We use this instead of `dyn Strategy` because we need them to be serializable and downcastable.
#[derive(Serialize, Deserialize)]
#[enum_delegate::implement(Strategy)]
pub enum DynStrategy {
    SparseMatrix(SparseMatrix),
}
type Index = Vec<ndarray::Ix>;
#[derive(Serialize, Deserialize)]
pub struct SparseMatrix {
    entries: Vec<SparseMatrixEntry>,
    bias: Array,
}
#[derive(Serialize, Deserialize)]
pub struct SparseMatrixEntry {
    in_index: Index,
    out_index: Index,
    weight: f32,
}
impl Strategy for SparseMatrix {
    fn evaluate(&self, context: &mut StrategyEvaluationContext, input: Array) -> Array {
        let mut result = self.bias.to_owned();
        for entry in &self.entries {
            result[&*entry.out_index] += input[&*entry.in_index] * entry.weight;
        }
        result.into_shared()
    }
}
/// An optimizer along with a measure of how much CPU time it has used.
struct TrackedOptimizer {
    expenditures: f64,
    behavior: Arc<dyn Optimizer>,
}

/// A process for improving the soup in some way.
///
/// Optimizers are basically opaque function objects that modify a Soup. Their only requirement is that they are supposed to "probably improve the soup in the long run". This isn't rigorously defined, and is only enforced by the good intentions of the implementor.
///
/// If a particular Optimizer has a chance of worsening something about the soup, it should pay attention to whether that thing is worsening in practice (TODO: how?); and if it is, the optimizer should exercise more caution in the future (for example, by using lower learning rates).
pub trait Optimizer {
    /// Perform one step of improving the soup.
    ///
    /// There no hard requirements on what a Optimizer may do in this function. Steps are free to be either cheap or expensive; the soup will distribute CPU time fairly between the optimizers.
    ///
    /// Implementors access the soup through `context` (see the documentation for SoupOptimizationStepContext).
    fn step(&self, context: &mut SoupOptimizationStepContext);
}

pub struct Ensemble {
    // current_cost: f64,
    // question_family: QuestionFamilyId,
    /// The strategies that are members of this ensemble.
    ///
    /// These members are all different strategies for answering the same question family. An ensemble is rewarded for having a representative sample of strategies, where, for any query, there should be at least one member that gives a good answer to that query; but no member necessarily needs to be able to give good answers to *all* possible queries.
    ///
    /// The ensemble also has a cost, proportional to the cost of evaluating all members (including their transitive dependencies).
    members: Vec<StrategyId>,
}

/// A soup's data for a particular "question family" – a kind of inputs, corresponding kind of outputs, and purpose of those outputs.
///
/// This includes:
/// * Strategies (essentially functions from input to output)
/// * Ensembles (collections of strategies, which for me function from a single input to a collection of outputs)
/// * Evaluators (approaches for deciding how good a strategy or ensemble is)
/// * Records of past evaluations that the evaluators have made of strategies and ensembles.
///
/// Currently, the only kind of evaluator is a corpus of training samples.
struct QuestionFamily {
    ensembles: HashMap<EnsembleId, Ensemble>,
    strategies: HashMap<StrategyId, DynStrategy>,
    training_samples: Option<InputOutputSampleBatch>,
}
fn evaluate_strategy(samples: InputOutputSampleBatch, strategy: impl Strategy) -> f64 {
    todo!("eli is gonna do this")
}

pub enum CachedQuery {}

/// The information about a query that has been run.
///
/// In addition to the answer, we keep a list of all of the optimizers that made this query.
/// Because the query is cached, the CPU time is only paid once; naïvely, the most fair attribution is to distribute the cost equally among those optimizers. So each time a new optimizer makes the same query, we will retroactively adjust the amount attributed to each of the earlier optimizers.
struct QueryResult {
    value: Arc<dyn Any>,
    askers: HashSet<OptimizerId>,
}

pub struct Soup {
    question_families: HashMap<QuestionFamilyId, QuestionFamily>,
    query_cache: HashMap<CachedQuery, QueryResult>,
    optimizers: HashMap<OptimizerId, TrackedOptimizer>,
}

/// The interface an Optimizer uses to access and modify the soup.
///
/// Optimizers are allowed to make arbitrary changes to strategies and ensembles, but they aren't allowed to touch the query cache or optimizers, and the cache needs to remember which strategies were changed. So optimizers need to access the soup through an interface, instead of just taking an `&mut Soup`.
pub struct SoupOptimizationStepContext<'a> {
    soup: &'a mut Soup,

    /// The ID of the optimizer that's currently running, so that the context knows which optimizer to attribute costs to.
    optimizer: OptimizerId,

    /// The amount of time the current step has spent in cached queries.
    ///
    /// Normally, we attribute all of the CPU time used by a step to that optimizer. But cached queries have their own way of attributing time spent, so the duration spent on cached queries will be omitted.
    cache_query_durations: f64,
}

impl Soup {
    /// Do one step of optimization.
    ///
    /// The basic idea of a Soup is to call `step` over and over again, making it slowly get better and better.
    ///
    /// This function's main effect is to delegate to the `step` function of one of the stored optimizers. To make sure each optimizer gets approximately equal shares of CPU time, we choose the optimizer with the lowest expenditures so far.
    ///
    /// The function also tracks the amount of time spent by the step, and attributes it to the optimizer appropriately.
    pub fn step(&mut self) {
        let (chosen_id, chosen_optimizer) = self
            .optimizers
            .iter()
            .min_by_key(|(_, o)| OrderedFloat(o.expenditures))
            .unwrap();
        let chosen_id = *chosen_id;
        let chosen_behavior = chosen_optimizer.behavior.clone();
        let start = Instant::now();
        let mut context = SoupOptimizationStepContext {
            soup: self,
            optimizer: chosen_id,
            cache_query_durations: 0.0,
        };
        chosen_behavior.step(&mut context);
        let total_duration = start.elapsed().as_secs_f64();
        let unaccounted_expenditure = total_duration - context.cache_query_durations;
        self.optimizers.get_mut(&chosen_id).unwrap().expenditures += unaccounted_expenditure;
    }
}

impl<'a> SoupOptimizationStepContext<'a> {}

struct AllEnsemblesGradientDescentOptimizer;
impl Optimizer for AllEnsemblesGradientDescentOptimizer {
    fn step(&self, context: &mut SoupOptimizationStepContext) {
        todo!()
    }
}
