use crate::differentiable_operations::{
    activation_functions, scalar_multiply, sum_inputs, AnyDifferentiableOperation,
    DifferentiableOperation,
};
use crate::model_2::{Graph, InferenceResult, LossGradients, Node, NodeInput, NodeInputKind};
use crate::model_shared::{Array, ArrayExt, BatchValues, NodeId, OutputId, VariableId};
use ndarray::s;
use ordered_float::OrderedFloat;
use rand::Rng;
use std::collections::HashMap;

pub struct InEdge {
    pub activation_id: NodeId,
    pub weight_id: NodeId,
}
pub struct LayerNode {
    pub in_edges: Vec<InEdge>,
}
pub struct Layer {
    pub nodes: HashMap<NodeId, LayerNode>,
}
pub struct Model {
    pub input_id: VariableId,
    pub output_id: OutputId,
    pub input_size: usize,
    pub output_size: usize,
    pub graph: Graph,
    pub layers: Vec<Layer>,
}

impl Model {
    pub fn new_1(input: (VariableId, usize), output: (OutputId, usize)) -> Model {
        let (input_id, input_size) = input;
        let (output_id, output_size) = output;
        let mut graph = Graph::default();

        let output_nodes = (0..output_size)
            .map(|_| {
                let id = graph.new_node(Node {
                    inputs: vec![Array::from_scalar(0.0).into()],
                    operation: sum_inputs(),
                });
                (id, LayerNode { in_edges: vec![] })
            })
            .collect();
        let output_layer = Layer {
            nodes: output_nodes,
        };
        Model {
            input_id,
            output_id,
            input_size,
            output_size,
            graph,
            layers: vec![output_layer],
        }
    }
    //pub fn new_2(input_length: usize, layer_sizes: &[usize]) -> Model {}

    pub fn add_promising_edges(&mut self, samples: &BatchValues) {
        AddPromisingEdgesContext::new(self, samples).run();
    }

    pub fn remove_random_edges(&mut self) {
        for layer in &mut self.layers {
            for (id, node) in &mut layer.nodes {
                let index = rand::thread_rng().gen_range(0..node.in_edges.len());
                let removed_edge = node.in_edges.remove(index);
                let removed_input = self
                    .graph
                    .nodes
                    .get_mut(id)
                    .unwrap()
                    .inputs
                    .remove(index + 1);
                assert_eq!(removed_input, NodeInput::from(removed_edge.weight_id));
                self.graph.nodes.remove(&removed_edge.weight_id);
                self.graph.nodes.remove(&removed_edge.activation_id);
            }
        }
    }

    pub fn add_edge(
        &mut self,
        destination: NodeId,
        source: &RawInputOption,
        activation_function: AnyDifferentiableOperation,
    ) {
        let first_input = match source {
            RawInputOption::InputColumn(input_name, column) => NodeInput {
                kind: NodeInputKind::Variable(input_name.clone()),
                slice: Some(vec![(..).into(), (*column).into()]),
            },
            &RawInputOption::Node(id) => id.into(),
        };
        let activation_id = self.graph.new_node(Node {
            inputs: vec![first_input],
            operation: activation_function,
        });
        let weight_id = self.graph.new_node(Node {
            inputs: vec![activation_id.into(), Array::from_scalar(0.0).into()],
            operation: scalar_multiply(),
        });
        self.graph
            .nodes
            .get_mut(&destination)
            .unwrap()
            .inputs
            .push(weight_id.into());

        for layer in &mut self.layers {
            if let Some(node) = layer.nodes.get_mut(&destination) {
                node.in_edges.push(InEdge {
                    activation_id,
                    weight_id,
                });
            }
        }
    }
}

#[derive(Clone)]
pub enum RawInputOption {
    InputColumn(VariableId, usize),
    Node(NodeId),
}

#[derive(Default)]
struct BruteForceSpatialDataStructure {
    entries: Vec<(Array, RawInputOption, AnyDifferentiableOperation)>,
}

impl BruteForceSpatialDataStructure {
    fn insert(
        &mut self,
        position: Array,
        input: RawInputOption,
        operation: AnyDifferentiableOperation,
    ) {
        self.entries.push((position, input, operation));
    }
    fn nearest_neighbor(
        &self,
        query: Array,
    ) -> Option<(RawInputOption, AnyDifferentiableOperation)> {
        let (_array, input, operation) = self
            .entries
            .iter()
            .max_by_key(|(array, _, _)| OrderedFloat(array.squared_difference(&query)))?;
        Some((input.clone(), operation.clone()))
    }
}

struct AddPromisingEdgesContext<'a> {
    options: BruteForceSpatialDataStructure,
    model: &'a mut Model,
    samples: &'a BatchValues,
    inference_result: InferenceResult,
    gradients: LossGradients,
}

impl<'a> AddPromisingEdgesContext<'a> {
    fn new(model: &'a mut Model, samples: &'a BatchValues) -> Self {
        let inference_result = model.graph.do_inference(samples);
        let gradients = model.graph.backprop(samples, &inference_result);
        AddPromisingEdgesContext {
            options: BruteForceSpatialDataStructure::default(),
            model,
            samples,
            inference_result,
            gradients,
        }
    }

    fn value(&self, option: &RawInputOption) -> Array {
        match option {
            RawInputOption::InputColumn(id, index) => {
                self.samples.get(id).slice_move(s![.., *index]).into_dyn()
            }
            RawInputOption::Node(id) => self
                .inference_result
                .internal_values
                .get(id)
                .unwrap()
                .clone(),
        }
    }

    fn insert_options(&mut self, raw: RawInputOption) {
        for activation_function in activation_functions() {
            self.options.insert(
                self.value(&raw)
                    .map(|&a| activation_function.forward_scalar(a))
                    .into_shared()
                    .normalized(),
                raw.clone(),
                activation_function,
            );
        }
    }

    fn insert_input_options(&mut self) {
        for column in 0..self.model.input_size {
            self.insert_options(RawInputOption::InputColumn(
                self.model.input_id.clone(),
                column,
            ))
        }
    }

    fn do_layer(&mut self, layer: usize) {
        let ids = self.model.layers[layer]
            .nodes
            .keys()
            .copied()
            .collect::<Vec<_>>();
        for &id in &ids {
            let normalized_gradient = self
                .gradients
                .internal_values
                .get(&id)
                .unwrap()
                .output_gradient
                .clone()
                .normalized();
            let (input, operation) = self.options.nearest_neighbor(normalized_gradient).unwrap();
            self.model.add_edge(id, &input, operation);
        }
        for &id in &ids {
            self.insert_options(RawInputOption::Node(id));
        }
    }

    fn run(&mut self) {
        self.insert_input_options();
        for i in 0..self.model.layers.len() {
            self.do_layer(i);
        }
    }
}
