use crate::differentiable_operations::{
    get_only_value, AnyDifferentiableOperation as Operation, DifferentiableOperation,
};
use ndarray::{arr0, stack, ArcArray, Axis, IxDyn, Slice};
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::zip;
use std::ops::{Deref, DerefMut};
use uuid::Uuid;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
pub struct NodeId(pub Uuid);

impl NodeId {
    pub fn new_random() -> Self {
        NodeId(Uuid::new_v4())
    }
}

pub type Array = ArcArray<f32, IxDyn>;
pub trait ArrayExt {
    fn from_scalar(x: f32) -> Self;
    fn as_scalar(&self) -> f32;
}
impl ArrayExt for Array {
    fn from_scalar(x: f32) -> Self {
        arr0(x).into_dyn().into_shared()
    }
    fn as_scalar(&self) -> f32 {
        *get_only_value(self)
    }
}

pub type VariableId = String;
pub type OutputId = VariableId;

// pub fn merge<K: Eq + Hash, V>(a: HashMap<K, V>, b: HashMap<K, V>) -> HashMap<K, V> {
//     let mut a = a;
//     a.extend(b.into_iter());
//     a
// }

#[derive(Clone, Debug, Default)]
pub struct Graph {
    // variables: HashSet<VariableId>,
    nodes: HashMap<NodeId, Node>,
    outputs: HashMap<OutputId, NodeId>,
}

#[derive(Clone, Debug)]
pub enum NodeInput {
    Variable(VariableId),
    Node(NodeId),
}

impl<'a> From<&'a str> for NodeInput {
    fn from(value: &'a str) -> Self {
        Self::Variable(value.into())
    }
}
impl From<VariableId> for NodeInput {
    fn from(value: VariableId) -> Self {
        Self::Variable(value)
    }
}
impl From<NodeId> for NodeInput {
    fn from(value: NodeId) -> Self {
        Self::Node(value)
    }
}

#[derive(Clone, Debug)]
pub struct Node {
    pub inputs: Vec<NodeInput>,
    pub operation: Operation,
}

pub trait ParametersOptimizer {
    fn step(
        &mut self,
        parameters: &mut VariableValues,
        training_batch: &BatchValues,
        loss_graph: &Graph,
    );
}

#[derive(Clone, Debug, Default)]
pub struct VariableValues {
    values: HashMap<VariableId, Array>,
}
#[derive(Clone, Debug)]
pub struct BatchValues {
    values: VariableValues,
    batch_size: usize,
}

impl Deref for VariableValues {
    type Target = HashMap<VariableId, Array>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}
impl DerefMut for VariableValues {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl Deref for BatchValues {
    type Target = VariableValues;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}
impl DerefMut for BatchValues {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

pub trait Merge<Other> {
    fn merge(&self, other: &Other) -> Self;
}

impl VariableValues {
    pub fn new(values: impl IntoIterator<Item = (VariableId, Array)>) -> VariableValues {
        let values = values.into_iter().collect();
        VariableValues { values }
    }

    pub fn get<Q>(&self, id: &Q) -> Array
    where
        VariableId: Borrow<Q>,
        Q: Hash + Eq + Debug + ?Sized,
    {
        self.values
            .get(id)
            .unwrap_or_else(|| {
                panic!("Tried to get value of variable {id:?} in a batch without that variable")
            })
            .clone()
    }

    pub fn get_mut<Q: Debug>(&mut self, id: &Q) -> &mut Array
    where
        VariableId: Borrow<Q>,
        Q: Hash + Eq + Debug + ?Sized,
    {
        self.values.get_mut(id).unwrap_or_else(|| {
            panic!("Tried to get value of variable {id:?} in a batch without that variable")
        })
    }

    pub fn merge(&self, other: &VariableValues) -> VariableValues {
        let mut values = self.values.clone();
        values.extend(other.values.iter().map(|(i, v)| (i.clone(), v.clone())));
        VariableValues { values }
    }

    pub fn update(&mut self, other: &VariableValues, factor: f32) {
        for (id, value) in &mut self.values {
            *value = (other[id].clone() * factor) + value.view();
        }
    }
}

impl Merge<BatchValues> for VariableValues {
    fn merge(&self, other: &BatchValues) -> Self {
        self.merge(other)
    }
}

impl Merge<BatchValues> for BatchValues {
    fn merge(&self, other: &BatchValues) -> Self {
        assert_eq!(self.batch_size, other.batch_size);
        BatchValues {
            batch_size: self.batch_size,
            values: self.values.merge(&other.values),
        }
    }
}

impl BatchValues {
    pub fn new(values: impl IntoIterator<Item = (VariableId, Array)>) -> BatchValues {
        let values = VariableValues::new(values);
        let mut iter = values.values.values();
        let first = iter.next().unwrap();
        let batch_size = first.len_of(Axis(0));
        for a in iter {
            assert_eq!(a.len_of(Axis(0)), batch_size);
        }
        BatchValues { values, batch_size }
    }

    pub fn batch_size(&self) -> usize {
        self.batch_size
    }

    pub fn slice_batch(&self, slice: Slice) -> BatchValues {
        let values: HashMap<VariableId, Array> = self
            .values
            .values
            .iter()
            .map(|(id, value)| {
                (id.clone(), {
                    let mut value = value.clone();
                    value.slice_axis_inplace(Axis(0), slice);
                    value
                })
            })
            .collect();
        let batch_size = values.values().next().unwrap().len_of(Axis(0));
        BatchValues {
            batch_size,
            values: VariableValues { values },
        }
    }

    pub fn sample_batch(&self, samples: &[usize]) -> BatchValues {
        let values = self
            .values
            .values
            .iter()
            .map(|(id, value)| {
                (
                    id.clone(),
                    stack(
                        Axis(0),
                        &samples
                            .iter()
                            .map(|&i| value.index_axis(Axis(0), i))
                            .collect::<Vec<_>>(),
                    )
                    .unwrap()
                    .into_shared(),
                )
            })
            .collect();
        let batch_size = samples.len();
        BatchValues {
            batch_size,
            values: VariableValues { values },
        }
    }

    pub fn merge<Other: Merge<BatchValues>>(&self, other: &Other) -> Other {
        other.merge(self)
    }
}

pub struct InputOutputSampleBatch {
    pub inputs: BatchValues,
    pub outputs: BatchValues,
}

impl InputOutputSampleBatch {
    pub fn variable_values_including_observed_outputs(&self) -> BatchValues {
        let mut result = (**self.inputs).clone();
        result.extend(
            self.outputs
                .iter()
                .map(|(id, value)| (loss_graph_observed_output_variable_id(id), value.clone())),
        );
        BatchValues::new(result)
    }
}

impl Graph {
    // pub fn new_variable(&mut self, variable_id: impl Into<VariableId>) {
    //     self.new_node_impl(Node::Variable(variable_id))
    // }
    pub fn new_output(&mut self, output_id: impl Into<OutputId>, node_id: NodeId) {
        self.outputs.insert(output_id.into(), node_id);
    }
    pub fn new_node(&mut self, node: Node) -> NodeId {
        let node_id = NodeId::new_random();
        self.nodes.insert(node_id, node);
        node_id
    }
    pub fn backward_topological_order(&self) -> Vec<(NodeId, &Node)> {
        let mut num_out_edges: HashMap<NodeId, usize> =
            self.nodes.keys().map(|&id| (id, 0)).collect();
        let mut ready_stack = Vec::new();
        let mut result = Vec::with_capacity(self.nodes.len());
        for node in self.nodes.values() {
            for neighbor in &node.inputs {
                if let NodeInput::Node(neighbor) = neighbor {
                    *num_out_edges.get_mut(neighbor).unwrap() += 1;
                }
            }
        }
        for (&id, &num) in &num_out_edges {
            if num == 0 {
                ready_stack.push(id);
            }
        }
        while let Some(id) = ready_stack.pop() {
            let node = self.nodes.get(&id).unwrap();
            result.push((id, node));
            for neighbor in &node.inputs {
                if let NodeInput::Node(neighbor) = neighbor {
                    let count = num_out_edges.get_mut(neighbor).unwrap();
                    *count -= 1;
                    if *count == 0 {
                        ready_stack.push(*neighbor);
                    }
                }
            }
        }
        result
    }
    pub fn forward_topological_order(&self) -> Vec<(NodeId, &Node)> {
        let mut result = self.backward_topological_order();
        result.reverse();
        result
    }

    pub fn compose(&self, other: &Graph) -> Graph {
        let mut result = Graph {
            // variables: self.variables.clone(),
            nodes: self.nodes.clone(),
            outputs: other.outputs.clone(),
        };
        // let mut replacements = HashMap::new();
        for (&id, node) in &other.nodes {
            let mut new_node = node.clone();
            for input in &mut new_node.inputs {
                if let NodeInput::Variable(vi) = input {
                    if let Some(&repl) = self.outputs.get(vi) {
                        *input = NodeInput::Node(repl);
                    }
                }
            }
            result.nodes.insert(id, new_node);
        }
        result
    }
}

#[macro_export]
macro_rules! graph {
    ($([$($line:tt)*];)*) => {
        {
            let mut g = $crate::model_1::Graph::default();
            $($crate::graph!(@line g: $($line)*);)*
            g
        }
    };
    (@line $g:ident: let $binding:ident $($rest:tt)*) => {
        let $binding = $crate::graph!(@name $g: $($rest)*);
    };
    (@line $g:ident: $($rest:tt)*) => {
        let _ = $crate::graph!(@name $g: $($rest)*);
    };
    (@name $g:ident: @($name:expr) = $($rest:tt)*) => {
        {
            let node_id = $crate::graph!(@node $g: $($rest)*);
            $g.new_output($name, node_id);
            node_id
        }
    };
    (@name $g:ident: = $($rest:tt)*) => {
        $crate::graph!(@node $g: $($rest)*)
    };
    (@node $g:ident: ($operation:expr)($($args:expr),*$(,)*)) => {
        $g.new_node($crate::model_1::Node {
            inputs: vec![$(($args).into()),*],
            operation: $operation,
        })
    };
}

#[derive(Debug)]
pub struct InferenceResult {
    pub outputs: VariableValues,
    pub internal_values: HashMap<NodeId, Array>,
}
#[derive(Debug)]
pub struct LossGradients {
    pub variables: VariableValues,
    pub internal_values: HashMap<NodeId, Array>,
}

impl InferenceResult {
    pub fn loss(&self) -> f32 {
        self.outputs[&loss_output_id()].as_scalar()
    }
}

#[derive(Debug)]
struct InferenceContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a VariableValues,
    result_so_far: InferenceResult,
}
#[derive(Debug)]
struct BackpropContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a VariableValues,
    inference_result: &'a InferenceResult,
    result_so_far: LossGradients,
}

impl InferenceContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<Array> {
        node.inputs
            .iter()
            .map(|i| match i {
                NodeInput::Variable(variable_id) => self.variable_values.get(variable_id),
                NodeInput::Node(node_id) => self.result_so_far.internal_values[node_id].clone(),
            })
            .collect()
    }
}
impl BackpropContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<Array> {
        node.inputs
            .iter()
            .map(|i| match i {
                NodeInput::Variable(variable_id) => self.variable_values.get(variable_id),
                NodeInput::Node(node_id) => self.inference_result.internal_values[node_id].clone(),
            })
            .collect()
    }
    fn output_gradient(&self, id: NodeId) -> Array {
        self.result_so_far.internal_values[&id].clone()
    }
}

pub fn do_inference(graph: &Graph, variable_values: &VariableValues) -> InferenceResult {
    let mut context = InferenceContext {
        // graph,
        variable_values,
        result_so_far: InferenceResult {
            outputs: Default::default(),
            internal_values: Default::default(),
        },
    };
    for (id, node) in graph.forward_topological_order() {
        let node_output = node.operation.forward(&context.node_input_values(node));
        context
            .result_so_far
            .internal_values
            .insert(id, node_output);
    }
    for (output_id, node_id) in &graph.outputs {
        context.result_so_far.outputs.insert(
            output_id.clone(),
            context.result_so_far.internal_values[node_id].clone(),
        );
    }
    context.result_so_far
}

pub fn backprop(
    graph: &Graph,
    variable_values: &VariableValues,
    inference_result: &InferenceResult,
) -> LossGradients {
    let mut context = BackpropContext {
        // graph,
        variable_values,
        inference_result,
        result_so_far: LossGradients {
            variables: Default::default(),
            internal_values: Default::default(),
        },
    };
    context
        .result_so_far
        .internal_values
        .insert(graph.outputs[&loss_output_id()], Array::from_scalar(1.0));
    for (id, node) in graph.backward_topological_order() {
        let node_input_gradients = node.operation.gradient(
            &context.node_input_values(node),
            context.output_gradient(id),
        );
        for (i, g) in zip(&node.inputs, node_input_gradients) {
            //dbg!(i, g.shape());
            match i {
                NodeInput::Variable(i) => {
                    *context
                        .result_so_far
                        .variables
                        .entry(i.clone())
                        .or_insert_with(|| Array::zeros(variable_values.get(i).shape())) += &g;
                }
                NodeInput::Node(i) => {
                    *context
                        .result_so_far
                        .internal_values
                        .entry(*i)
                        .or_insert_with(|| {
                            Array::zeros(inference_result.internal_values.get(i).unwrap().shape())
                        }) += &g;
                }
            }
        }
    }
    context.result_so_far
}

pub fn loss_output_id() -> OutputId {
    "loss".to_owned()
}
pub fn loss_graph_observed_output_variable_id(output_id: impl Into<OutputId>) -> VariableId {
    format!("observed_{}", output_id.into())
}

pub fn calculate_loss(
    parameters: &VariableValues,
    loss_graph: &Graph,
    samples: &InputOutputSampleBatch,
) -> f32 {
    do_inference(
        loss_graph,
        &samples
            .variable_values_including_observed_outputs()
            .merge(parameters),
    )
    .loss()
}
