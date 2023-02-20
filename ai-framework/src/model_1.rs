use crate::differentiable_operations::{
    AnyDifferentiableOperation as Operation, DifferentiableOperation,
};
use ndarray::{arr0, ArrayD, ArrayViewD, Ix0};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::zip;
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
    pub output_loss_graph: Graph,
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
    // (@line) => {};
    // (@line: let $binding:ident $($rest:tt)*) => {
    //     graph!(@name: $binding $($rest)*)
    // };
    // (@line: $($rest:tt)*) => {
    //     graph!(@name: _ $($rest)*)
    // };
    // (@name: $binding:tt @($name:expr) = $($rest:tt)*) => {
    //     {
    //         graph!(@node: $binding {graph.new_output($name, node_id);} $($rest)*);
    //         graph.new_output($name, node_id);
    //         node_id
    //     }
    // };
    // (@name: $binding:tt = $($rest:tt)*) => {
    //     graph!(@node: $binding $($rest)*);
    // };
    // (@node: $binding:tt {$extra:stmt} = ($operation:expr)($($args:expr),*$(,)*); $($rest:tt)*) => {
    //     let $binding = {
    //         let node_id = graph.new_node(Node {
    //             inputs: vec![$(($args).into()),*],
    //             operation: $operation,
    //         });
    //         $extra
    //         node_id
    //     };
    //     $(graph!(@line: $($rest)*))*
    // };
    // ($($stuff:tt)*) => {
    //     {
    //         let mut graph = Graph::default();
    //         graph!(@line: $($stuff)*);
    //         graph
    //     }
    // };
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
    pub outputs: HashMap<OutputId, ValueMaybeBatch>,
    pub internal_values: HashMap<NodeId, ValueMaybeBatch>,
}
#[derive(Debug)]
pub struct LossGradients {
    pub variables: HashMap<VariableId, ValueMaybeBatchDerivative>,
    pub internal_values: HashMap<NodeId, ValueMaybeBatchDerivative>,
}

#[derive(Debug)]
struct InferenceContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a HashMap<VariableId, ValueMaybeBatch>,
    result_so_far: InferenceResult,
}
#[derive(Debug)]
struct BackpropContext<'a> {
    // graph: &'a Graph,
    variable_values: &'a HashMap<VariableId, ValueMaybeBatch>,
    inference_result: &'a InferenceResult,
    result_so_far: LossGradients,
}

impl InferenceContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<ValueMaybeBatchView> {
        node.inputs
            .iter()
            .map(|i| match i {
                NodeInput::Variable(variable_id) => match self.variable_values.get(variable_id) {
                    Some(v) => v.view(),
                    None => {
                        panic!(
                            "Tried to get variable `{variable_id}` but inputs only provided {:?}",
                            self.variable_values.keys().collect::<Vec<_>>(),
                        );
                    }
                },
                NodeInput::Node(node_id) => self.result_so_far.internal_values[node_id].view(),
            })
            .collect()
    }
}
impl BackpropContext<'_> {
    fn node_input_values(&self, node: &Node) -> Vec<ValueMaybeBatchView> {
        node.inputs
            .iter()
            .map(|i| match i {
                NodeInput::Variable(variable_id) => self.variable_values[variable_id].view(),
                NodeInput::Node(node_id) => self.inference_result.internal_values[node_id].view(),
            })
            .collect()
    }
    fn output_gradient(&self, id: NodeId) -> ValueMaybeBatchDerivativeView {
        self.result_so_far.internal_values[&id].view()
    }
}

pub fn do_inference(
    graph: &Graph,
    variable_values: &HashMap<VariableId, ValueMaybeBatch>,
) -> InferenceResult {
    let mut context = InferenceContext {
        // graph,
        variable_values,
        result_so_far: InferenceResult {
            outputs: Default::default(),
            internal_values: Default::default(),
        },
    };
    for (id, node) in graph.forward_topological_order() {
        // dbg!(
        //     graph,
        //     &context
        //         .result_so_far
        //         .internal_values
        //         .keys()
        //         .collect::<Vec<_>>(),
        //     id,
        //     node,
        //     graph.forward_topological_order()
        // );
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
    variable_values: &HashMap<VariableId, ValueMaybeBatch>,
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
        .insert(graph.outputs[&loss_output_id()], arr0(1.0).into_dyn());
    for (id, node) in graph.backward_topological_order() {
        let node_input_gradients = node.operation.gradient(
            &context.node_input_values(node),
            context.output_gradient(id),
        );
        for (i, g) in zip(&node.inputs, node_input_gradients) {
            dbg!(i, g.shape());
            match i {
                NodeInput::Variable(i) => {
                    *context
                        .result_so_far
                        .variables
                        .entry(i.clone())
                        .or_insert_with(|| {
                            ArrayD::zeros(variable_values.get(i).unwrap().shape())
                        }) += &g;
                }
                NodeInput::Node(i) => {
                    *context
                        .result_so_far
                        .internal_values
                        .entry(*i)
                        .or_insert_with(|| {
                            ArrayD::zeros(inference_result.internal_values.get(i).unwrap().shape())
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
    parameters: HashMap<VariableId, &ValueMaybeBatch>,
    graph: &Graph,
    samples: &TrainingSampleBatch,
) -> f32 {
    let mut variable_values: HashMap<VariableId, ValueMaybeBatch> = samples.inputs.clone();
    variable_values.extend(
        parameters
            .iter()
            .map(|(id, &val)| (id.clone(), val.clone())),
    );
    let lg = graph.compose(&samples.output_loss_graph);
    do_inference(&lg, &variable_values).outputs[&loss_output_id()]
        .view()
        .into_dimensionality::<Ix0>()
        .unwrap()[()]
}

// fn loss_graph(graph: &Graph, output_loss_function: Graph) -> Graph {
//     let mut result = graph.clone();
//     let observed_output_nodes: Vec<_> = graph
//         .outputs
//         .keys()
//         .map(|output_id| result.new_variable(loss_graph_observed_output_variable_id(output_id)))
//         .collect();
//     let loss_node = result.new_node(Node {
//         inputs: graph
//             .outputs
//             .values()
//             .copied()
//             .chain(observed_output_nodes)
//             .collect(),
//         operation: output_loss_function,
//     });
//     result.outputs = [(loss_output_id(), loss_node)].into_iter().collect();
//     result
// }
// fn loss_graph2_node_output_variable_id(node_id: NodeId) -> VariableId {
//     format!("output_for_{node_id:?}")
// }
// fn intermediate_value_loss_function() -> Operation {
//     mean_squared_difference()
// }
//
// fn loss_graph2(graph: &Graph, output_loss_function: Operation) -> Graph {
//     let mut result = graph.clone();
//     let intermediate_value_variables: Vec<(VariableId, NodeId, NodeId)> = graph
//         .nodes
//         .keys()
//         .map(|&id| {
//             let variable_id = loss_graph2_node_output_variable_id(id);
//             (variable_id.clone(), id, result.new_variable(variable_id))
//         })
//         .collect();
//     let observed_output_nodes: Vec<NodeId> = graph
//         .outputs
//         .keys()
//         .map(|output_id| result.new_variable(loss_graph_observed_output_variable_id(output_id)))
//         .collect();
//     let original_loss_node = result.new_node(Node {
//         inputs: graph
//             .outputs
//             .values()
//             .copied()
//             .chain(observed_output_nodes)
//             .collect(),
//         operation: output_loss_function,
//     });
//     let all_loss_nodes = iter::once(original_loss_node)
//         .chain(
//             intermediate_value_variables
//                 .iter()
//                 .map(|&(_, original, new)| {
//                     result.new_node(Node {
//                         inputs: vec![original, new],
//                         operation: intermediate_value_loss_function(),
//                     })
//                 }),
//         )
//         .collect();
//     let loss_node = result.new_node(Node {
//         inputs: all_loss_nodes,
//         operation: sum_inputs(),
//     });
//     result.outputs = [(loss_output_id(), loss_node)].into_iter().collect();
//     result
// }
//
// fn lossgraph2_internal_parameters(
//     graph: &Graph,
//     samples: &TrainingSampleBatch,
// ) -> HashMap<VariableId, ValueMaybeBatch> {
//     let internal_values = do_inference(graph, &samples.inputs).internal_values;
//     internal_values
//         .into_iter()
//         .map(|(id, value)| (loss_graph2_node_output_variable_id(id), value))
//         .collect()
// }

pub fn train_1(
    parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
    graph: &Graph,
    samples: &TrainingSampleBatch,
    optimizer: &mut impl Optimize,
) {
    let lg = graph.compose(&samples.output_loss_graph);
    optimizer.optimize(parameters, samples.for_optimizer(), &lg);
}

// pub fn train_2(
//     mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
//     graph: &Graph,
//     samples: &TrainingSampleBatch,
//     optimizer: &mut impl Optimize,
// ) {
//     let lg = loss_graph2(graph, samples.output_loss_function.clone());
//     let mut extra_parameters = lossgraph2_internal_parameters(graph, samples);
//     let mut all_parameters = HashMap::new();
//     all_parameters.extend(
//         parameters
//             .iter_mut()
//             .map(|(id, value)| (id.clone(), &mut **value)),
//     );
//     all_parameters.extend(
//         extra_parameters
//             .iter_mut()
//             .map(|(id, value)| (id.clone(), value)),
//     );
//     optimizer.optimize(all_parameters, samples.for_optimizer(), &lg);
// }
