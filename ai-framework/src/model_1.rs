use crate::differentiable_operations::{
    mean_squared_difference, sum_inputs, AnyDifferentiableOperation as Operation,
    DifferentiableOperation,
};
use ndarray::{ArrayD, ArrayViewD};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::iter;
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

pub type VariableId = String;
pub type OutputId = VariableId;
// the value of a variable, which can either be a batch, or not
pub type ValueMaybeBatch = ArrayD<f32>;
pub type ValueMaybeBatchView<'a> = ArrayViewD<'a, f32>;
pub type ValueMaybeBatchDerivative = ArrayD<f32>;
pub type ValueMaybeBatchDerivativeView<'a> = ArrayViewD<'a, f32>;

pub fn merge<K: Eq + Hash, V>(a: HashMap<K, V>, b: HashMap<K, V>) -> HashMap<K, V> {
    let mut a = a;
    a.extend(b.into_iter());
    a
}

// pub trait Model {
//     type Value;
//     type Derivative;
//     fn nodes() -> Vec<NodeId>;
//     fn parameters() -> Vec<ParameterId>;
// }

#[derive(Clone, Debug)]
pub struct Graph {
    nodes: HashMap<NodeId, Node>,
    outputs: HashMap<OutputId, NodeId>,
}

#[derive(Clone, Debug)]
pub enum Node {
    Variable(VariableId),
    Internal(InternalNode),
}

#[derive(Clone)]
pub struct InternalNode {
    pub inputs: Vec<NodeId>,
    pub operation: Operation,
}

impl Debug for InternalNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.inputs.fmt(f)
    }
}

pub trait Optimize {
    fn optimize(
        &mut self,
        parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        graph: &Graph,
    );
}

pub struct TrainingSampleBatch {
    pub inputs: HashMap<VariableId, ValueMaybeBatch>,
    pub outputs: HashMap<OutputId, ValueMaybeBatch>,
    pub output_loss_function: Operation,
}

impl TrainingSampleBatch {
    fn for_optimizer(&self) -> HashMap<VariableId, ValueMaybeBatch> {
        let mut result = self.inputs.clone();
        result.extend(
            self.outputs
                .iter()
                .map(|(id, value)| (loss_graph_observed_output_variable_id(id), value.clone())),
        );
        result
    }
}

impl Graph {
    pub fn new_variable(&mut self, variable_id: impl Into<VariableId>) -> NodeId {
        self.new_node_impl(Node::Variable(variable_id))
    }
    pub fn new_node(&mut self, node: InternalNode) -> NodeId {
        self.new_node_impl(Node::Internal(node))
    }
    pub fn new_output(&mut self, output_id: impl Into<OutputId>, node_id: NodeId) {
        self.outputs.insert(output_id, node_id);
    }
    fn new_node_impl(&mut self, node: Node) -> NodeId {
        let node_id = NodeId::new_random();
        self.nodes.insert(node_id, node);
        node_id
    }
    pub fn backward_topological_order(&self) -> Vec<(NodeId, &InternalNode)> {
        let mut num_out_edges: HashMap<NodeId, usize> =
            self.nodes.keys().map(|&id| (id, 0)).collect();
        let mut ready_stack = Vec::new();
        let mut result = Vec::with_capacity(self.nodes.len());
        for node in self.nodes.values() {
            if let Node::Internal(node) = node {
                for neighbor in &node.inputs {
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
            if let Node::Internal(node) = node {
                result.push((id, node));
                for neighbor in &node.inputs {
                    *num_out_edges.get_mut(neighbor).unwrap() -= 1;
                }
            }
        }
        result
    }
    pub fn forward_topological_order(&self) -> Vec<(NodeId, &InternalNode)> {
        let mut result = self.backward_topological_order();
        result.reverse();
        result
    }

    pub fn compose(&self, other: &Graph) -> Graph {
        let mut result = self.clone();
        let mut replacements = HashMap::new();
        for (&id, node) in &other.nodes {
            if let Node::Variable(variable_id) = node {
                replacements.insert(id, self.outputs[variable_id]);
            }
        }
        for (&id, node) in &other.nodes {
            if let Node::Internal(node) = node {
                result.nodes.insert(
                    id,
                    Node::Internal(InternalNode {
                        inputs: node
                            .inputs
                            .iter()
                            .map(|ni| replacements.get(ni).copied().unwrap_or(ni)),
                        operation: node.operation.clone(),
                    }),
                );
            }
        }
        result
    }
}

pub struct InferenceResult {
    pub outputs: HashMap<VariableId, ValueMaybeBatch>,
    pub internal_values: HashMap<NodeId, ValueMaybeBatch>,
}

struct InferenceContext<'a> {
    graph: &'a Graph,
    variable_values: &'a HashMap<VariableId, ValueMaybeBatch>,
    result_so_far: InferenceResult,
}

impl InferenceContext<'_> {
    fn node_input_values(&self, node: &InternalNode) -> Vec<ValueMaybeBatchView> {
        node.inputs
            .iter()
            .map(|i| match &self.graph.nodes[i] {
                Node::Variable(variable_id) => self.variable_values[variable_id].view(),
                Node::Internal { .. } => self.result_so_far.internal_values[i].view(),
            })
            .collect()
    }
}

pub fn do_inference(
    graph: &Graph,
    variable_values: &HashMap<VariableId, ValueMaybeBatch>,
) -> InferenceResult {
    let mut context = InferenceContext {
        graph,
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

fn loss_output_id() -> OutputId {
    "loss".to_owned()
}
fn loss_graph_observed_output_variable_id(output_id: &OutputId) -> VariableId {
    format!("observed_{output_id}")
}

fn loss_graph(graph: &Graph, output_loss_function: Graph) -> Graph {
    let mut result = graph.clone();
    let observed_output_nodes: Vec<_> = graph
        .outputs
        .keys()
        .map(|output_id| result.new_variable(loss_graph_observed_output_variable_id(output_id)))
        .collect();
    let loss_node = result.new_node(InternalNode {
        inputs: graph
            .outputs
            .values()
            .copied()
            .chain(observed_output_nodes)
            .collect(),
        operation: output_loss_function,
    });
    result.outputs = [(loss_output_id(), loss_node)].into_iter().collect();
    result
}
fn loss_graph2_node_output_variable_id(node_id: NodeId) -> VariableId {
    format!("output_for_{node_id:?}")
}
fn intermediate_value_loss_function() -> Operation {
    mean_squared_difference()
}

fn loss_graph2(graph: &Graph, output_loss_function: Operation) -> Graph {
    let mut result = graph.clone();
    let intermediate_value_variables: Vec<(VariableId, NodeId, NodeId)> = graph
        .nodes
        .keys()
        .map(|&id| {
            let variable_id = loss_graph2_node_output_variable_id(id);
            (variable_id.clone(), id, result.new_variable(variable_id))
        })
        .collect();
    let observed_output_nodes: Vec<NodeId> = graph
        .outputs
        .keys()
        .map(|output_id| result.new_variable(loss_graph_observed_output_variable_id(output_id)))
        .collect();
    let original_loss_node = result.new_node(InternalNode {
        inputs: graph
            .outputs
            .values()
            .copied()
            .chain(observed_output_nodes)
            .collect(),
        operation: output_loss_function,
    });
    let all_loss_nodes = iter::once(original_loss_node)
        .chain(
            intermediate_value_variables
                .iter()
                .map(|&(_, original, new)| {
                    result.new_node(InternalNode {
                        inputs: vec![original, new],
                        operation: intermediate_value_loss_function(),
                    })
                }),
        )
        .collect();
    let loss_node = result.new_node(InternalNode {
        inputs: all_loss_nodes,
        operation: sum_inputs(),
    });
    result.outputs = [(loss_output_id(), loss_node)].into_iter().collect();
    result
}

fn lossgraph2_internal_parameters(
    graph: &Graph,
    samples: &TrainingSampleBatch,
) -> HashMap<VariableId, ValueMaybeBatch> {
    let internal_values = do_inference(graph, &samples.inputs).internal_values;
    internal_values
        .into_iter()
        .map(|(id, value)| (loss_graph2_node_output_variable_id(id), value))
        .collect()
}

pub fn train_1(
    parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
    graph: &Graph,
    samples: &TrainingSampleBatch,
    optimizer: &mut impl Optimize,
) {
    let lg = loss_graph(graph, samples.output_loss_function.clone());
    optimizer.optimize(parameters, samples.for_optimizer(), &lg);
}

pub fn train_2(
    mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
    graph: &Graph,
    samples: &TrainingSampleBatch,
    optimizer: &mut impl Optimize,
) {
    let lg = loss_graph2(graph, samples.output_loss_function.clone());
    let mut extra_parameters = lossgraph2_internal_parameters(graph, samples);
    let mut all_parameters = HashMap::new();
    all_parameters.extend(
        parameters
            .iter_mut()
            .map(|(id, value)| (id.clone(), &mut **value)),
    );
    all_parameters.extend(
        extra_parameters
            .iter_mut()
            .map(|(id, value)| (id.clone(), value)),
    );
    optimizer.optimize(all_parameters, samples.for_optimizer(), &lg);
}
