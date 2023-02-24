use crate::differentiable_operations::{
    AnyDifferentiableOperation as Operation, DifferentiableOperation,
};
use crate::model_shared::{
    loss_output_id, Array, ArrayExt, BatchValues, InputOutputSampleBatch, NodeId, OutputId,
    VariableId,
};
use ndarray::{IxDyn, SliceInfo, SliceInfoElem};
use std::collections::HashMap;
use std::iter::zip;

#[derive(Clone, Debug, Default)]
pub struct Graph {
    // variables: HashSet<VariableId>,
    nodes: HashMap<NodeId, Node>,
    outputs: HashMap<OutputId, NodeId>,
}

#[derive(Clone, Debug)]
pub enum NodeInputKind {
    Variable(VariableId),
    Parameter(Array),
    Node(NodeId),
}

#[derive(Clone, Debug)]
pub struct NodeInput {
    kind: NodeInputKind,
    slice: Option<SliceInfo<Vec<SliceInfoElem>, IxDyn, IxDyn>>,
}

impl<'a> From<&'a str> for NodeInput {
    fn from(value: &'a str) -> Self {
        NodeInput {
            kind: NodeInputKind::Variable(value.into()),
            slice: None,
        }
    }
}
impl From<VariableId> for NodeInput {
    fn from(value: VariableId) -> Self {
        NodeInput {
            kind: NodeInputKind::Variable(value),
            slice: None,
        }
    }
}
impl From<NodeId> for NodeInput {
    fn from(value: NodeId) -> Self {
        NodeInput {
            kind: NodeInputKind::Node(value),
            slice: None,
        }
    }
}
impl From<Array> for NodeInput {
    fn from(value: Array) -> Self {
        NodeInput {
            kind: NodeInputKind::Parameter(value),
            slice: None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Node {
    pub inputs: Vec<NodeInput>,
    pub operation: Operation,
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
                if let NodeInputKind::Node(neighbor) = &neighbor.kind {
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
                if let NodeInputKind::Node(neighbor) = &neighbor.kind {
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
        let mut result = self.clone();
        result
            .outputs
            .extend(other.outputs.iter().map(|(k, &v)| (k.clone(), v)));
        // let mut replacements = HashMap::new();
        for (&id, node) in &other.nodes {
            let mut new_node = node.clone();
            for input in &mut new_node.inputs {
                if let NodeInputKind::Variable(vi) = &input.kind {
                    if let Some(&repl) = self.outputs.get(vi) {
                        input.kind = NodeInputKind::Node(repl);
                    }
                }
            }
            result.nodes.insert(id, new_node);
        }
        result
    }

    pub fn update(&mut self, gradients: &LossGradients, factor: f32) {
        for (id, gradients) in &gradients.internal_values {
            for (input, gradient) in zip(
                &mut self.nodes.get_mut(id).unwrap().inputs,
                &gradients.parameter_gradients,
            ) {
                if let NodeInputKind::Parameter(parameter) = &mut input.kind {
                    *parameter += &(gradient.clone() * factor);
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct InferenceResult {
    pub outputs: BatchValues,
    pub internal_values: HashMap<NodeId, Array>,
}
#[derive(Debug)]
pub struct NodeGradients {
    pub output_gradient: Array,
    pub parameter_gradients: Vec<Array>,
}
#[derive(Debug)]
pub struct LossGradients {
    pub variables: BatchValues,
    pub internal_values: HashMap<NodeId, NodeGradients>,
}

impl InferenceResult {
    pub fn loss(&self) -> f32 {
        self.outputs[&loss_output_id()].as_scalar()
    }
}

#[derive(Debug)]
struct InferenceContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a BatchValues,
    result_so_far: InferenceResult,
}
#[derive(Debug)]
struct BackpropContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a BatchValues,
    inference_result: &'a InferenceResult,
    result_so_far: LossGradients,
}

impl InferenceContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<Array> {
        node.inputs
            .iter()
            .map(|i| match &i.kind {
                NodeInputKind::Variable(variable_id) => self.variable_values.get(variable_id),
                NodeInputKind::Node(node_id) => self.result_so_far.internal_values[node_id].clone(),
                NodeInputKind::Parameter(parameter) => parameter.clone(),
            })
            .collect()
    }
}
impl BackpropContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<Array> {
        node.inputs
            .iter()
            .map(|i| match &i.kind {
                NodeInputKind::Variable(variable_id) => self.variable_values.get(variable_id),
                NodeInputKind::Node(node_id) => {
                    self.inference_result.internal_values[node_id].clone()
                }
                NodeInputKind::Parameter(parameter) => parameter.clone(),
            })
            .collect()
    }
}

pub fn do_inference(graph: &Graph, variable_values: &BatchValues) -> InferenceResult {
    let mut context = InferenceContext {
        // graph,
        variable_values,
        result_so_far: InferenceResult {
            outputs: BatchValues::empty_with_batch_size(variable_values.batch_size()),
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
    variable_values: &BatchValues,
    inference_result: &InferenceResult,
) -> LossGradients {
    let mut context = BackpropContext {
        // graph,
        variable_values,
        inference_result,
        result_so_far: LossGradients {
            variables: BatchValues::empty_with_batch_size(variable_values.batch_size()),
            internal_values: Default::default(),
        },
    };
    context.result_so_far.internal_values.insert(
        graph.outputs[&loss_output_id()],
        NodeGradients {
            output_gradient: Array::from_scalar(1.0),
            parameter_gradients: Default::default(),
        },
    );
    for (id, node) in graph.backward_topological_order() {
        // take out to put back later, to simplify borrow checker stuff
        let mut this_node_gradients = context.result_so_far.internal_values.remove(&id).unwrap();
        let node_input_gradients = node.operation.gradient(
            &context.node_input_values(node),
            this_node_gradients.output_gradient.clone(),
        );
        this_node_gradients.parameter_gradients = node_input_gradients
            .iter()
            .map(|_| Default::default())
            .collect();
        for ((input, gradient), parameter_gradient_slot) in zip(
            zip(&node.inputs, node_input_gradients),
            &mut this_node_gradients.parameter_gradients,
        ) {
            //dbg!(i, g.shape());
            let full_array: &mut Array = match &input.kind {
                NodeInputKind::Variable(i) => context
                    .result_so_far
                    .variables
                    .entry(i.clone())
                    .or_insert_with(|| Array::zeros(variable_values.get(i).shape())),
                NodeInputKind::Node(i) => {
                    &mut context
                        .result_so_far
                        .internal_values
                        .entry(*i)
                        .or_insert_with(|| NodeGradients {
                            output_gradient: Array::zeros(
                                inference_result.internal_values.get(i).unwrap().shape(),
                            ),
                            parameter_gradients: Default::default(),
                        })
                        .output_gradient
                }
                NodeInputKind::Parameter(_parameter) => {
                    assert!(input.slice.is_none());
                    *parameter_gradient_slot = gradient;
                    continue;
                }
            };
            let mut relevant_part = match &input.slice {
                None => full_array.view_mut(),
                Some(slice) => full_array.slice_mut(slice),
            };
            relevant_part += &gradient;
        }
        context
            .result_so_far
            .internal_values
            .insert(id, this_node_gradients);
    }
    context.result_so_far
}

pub fn calculate_loss(loss_graph: &Graph, samples: &InputOutputSampleBatch) -> f32 {
    do_inference(
        loss_graph,
        &samples.variable_values_including_observed_outputs(),
    )
    .loss()
}
