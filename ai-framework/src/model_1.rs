use crate::differentiable_operations::{
    AnyDifferentiableOperation as Operation, DifferentiableOperation,
};
use crate::model_shared::{
    loss_output_id, Array, ArrayExt, BatchValues, InputOutputSampleBatch, NodeId, OutputId,
    VariableId, VariableValues,
};
use std::collections::HashMap;
use std::fmt::Debug;
use std::iter::zip;

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
macro_rules! graph_1 {
    ($([$($line:tt)*];)*) => {
        {
            let mut g = $crate::model_1::Graph::default();
            $($crate::graph_1!(@line g: $($line)*);)*
            g
        }
    };
    (@line $g:ident: let $binding:ident $($rest:tt)*) => {
        let $binding = $crate::graph_1!(@name $g: $($rest)*);
    };
    (@line $g:ident: $($rest:tt)*) => {
        let _ = $crate::graph_1!(@name $g: $($rest)*);
    };
    (@name $g:ident: @($name:expr) = $($rest:tt)*) => {
        {
            let node_id = $crate::graph_1!(@node $g: $($rest)*);
            $g.new_output($name, node_id);
            node_id
        }
    };
    (@name $g:ident: = $($rest:tt)*) => {
        $crate::graph_1!(@node $g: $($rest)*)
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
