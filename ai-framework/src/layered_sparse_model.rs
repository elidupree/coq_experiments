use crate::differentiable_operations::{
    activation_functions, scalar_multiply, stack, sum_inputs, AnyDifferentiableOperation,
    DifferentiableOperation,
};
use crate::model_2::{Graph, InferenceResult, LossGradients, Node, NodeInput, NodeInputKind};
use crate::model_shared::{Array, ArrayExt, BatchValues, NodeId, OutputId, VariableId};
use ndarray::{s, Ix1, SliceInfoElem};
use ordered_float::OrderedFloat;
use rand::Rng;
use std::collections::HashMap;
use std::io::Write;

#[derive(Debug)]
pub struct InEdge {
    pub activation_id: NodeId,
    pub weight_id: NodeId,
}
#[derive(Debug)]
pub struct LayerNode {
    pub in_edges: Vec<InEdge>,
}
#[derive(Debug)]
pub struct Layer {
    pub nodes: HashMap<NodeId, LayerNode>,
}
#[derive(Debug)]
pub struct Model {
    pub input_id: VariableId,
    pub output_id: OutputId,
    pub input_size: usize,
    pub output_size: usize,
    pub graph: Graph,
    pub layers: Vec<Layer>,
}

impl Model {
    pub fn new_1(
        input: (VariableId, usize),
        output: (OutputId, usize),
        output_loss_graph: &Graph,
    ) -> Model {
        let (input_id, input_size) = input;
        let (output_id, output_size) = output;
        let mut graph = Graph::default();

        let output_nodes: HashMap<NodeId, LayerNode> = (0..output_size)
            .map(|_| {
                let id = graph.new_node(Node {
                    inputs: vec![
                        // Mega hack: Always have two entries to work around bug with using autograd's add_n on less than 2
                        NodeInput {
                            kind: NodeInputKind::Variable(input_id.clone()),
                            slice: Some(vec![(..).into(), 0.into()]),
                        },
                        NodeInput {
                            kind: NodeInputKind::Variable(input_id.clone()),
                            slice: Some(vec![(..).into(), 0.into()]),
                        },
                        // Array::from_scalar(0.0).into(),
                    ],
                    operation: sum_inputs(),
                });
                (id, LayerNode { in_edges: vec![] })
            })
            .collect();
        let output_node = graph.new_node(Node {
            inputs: output_nodes.keys().map(|&i| i.into()).collect(),
            operation: stack(1),
        });
        let output_layer = Layer {
            nodes: output_nodes,
        };
        graph.new_output(output_id.clone(), output_node);
        graph = graph.compose(output_loss_graph);
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
                    .remove(index + 2);
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

    pub fn draw_graphviz(
        &self,
        samples: &BatchValues,
        writer: &mut impl Write,
    ) -> Result<(), std::io::Error> {
        writeln!(writer, "digraph G {{")?;
        let inference_results = self.graph.do_inference(samples);
        let gradients = self.graph.backprop(samples, &inference_results);

        // for layer in &self.layers {
        //     for (id, node) in &layer.nodes {
        //         write!(writer, r#"{id}[label="{}"]"#)?;
        //     }
        // }
        fn format_id(id: &NodeId) -> String {
            format!("node_{}", id.0.as_simple())
        }
        fn number_label(array: &Array) -> String {
            let mut iter = array.iter();
            let first = iter.next();
            let second = iter.next();
            if let Some(first) = first {
                if second.is_none() {
                    format!("{}", first)
                } else if array.iter().all(|v| v == first) {
                    format!("[{}]*{}", first, array.len())
                } else {
                    format!("[{}...]", first)
                }
            } else {
                "[]".to_string()
            }
        }

        for (id, node) in &self.graph.nodes {
            let idfmt = format_id(id);
            let inference_label = number_label(&inference_results.internal_values[id]);
            let gradient_label = number_label(&gradients.internal_values[id].output_gradient);
            writeln!(
                writer,
                r#"{idfmt}[label="{}\n{inference_label}\n{gradient_label}"]"#,
                node.operation
            )?;
            for (input_index, input) in node.inputs.iter().enumerate() {
                match &input.kind {
                    NodeInputKind::Variable(v) => {
                        if let Some(slice) = input.slice.as_ref() {
                            let SliceInfoElem::Index(i) = slice[1] else { panic!() };
                            writeln!(writer, r#"{v}{i} -> {idfmt}"#)?;
                        } else {
                            writeln!(writer, r#"{v} -> {idfmt}"#)?;
                        }
                    }
                    NodeInputKind::Parameter(p) => {
                        let parameter = number_label(p);
                        let parameter_gradient = number_label(
                            &gradients.internal_values[id].parameter_gradients[input_index],
                        );
                        writeln!(writer, r#"{idfmt}{input_index} -> {idfmt}"#)?;
                        writeln!(
                            writer,
                            r#"{idfmt}{input_index}[label="{parameter}\n{parameter_gradient}"]"#
                        )?;
                    }
                    NodeInputKind::Node(n) => {
                        let nfmt = format_id(n);
                        writeln!(writer, r#"{nfmt} -> {idfmt}"#)?;
                    }
                }
            }
        }

        writeln!(writer, "}}")?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
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
        let (_array, input, operation) = self.entries.iter().max_by_key(|(array, _, _)| {
            OrderedFloat(
                array
                    .view()
                    .into_dimensionality::<Ix1>()
                    .unwrap()
                    .dot(&query.view().into_dimensionality::<Ix1>().unwrap())
                    .abs(),
            )
        })?;
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
            if let Some(position) = activation_function
                .forward(&[self.value(&raw)])
                .normalized()
            {
                self.options
                    .insert(position, raw.clone(), activation_function);
            }
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
            if let Some(normalized_gradient) = self
                .gradients
                .internal_values
                .get(&id)
                .unwrap()
                .output_gradient
                .clone()
                .normalized()
            {
                let (input, operation) =
                    self.options.nearest_neighbor(normalized_gradient).unwrap();
                self.model.add_edge(id, &input, operation);
            }
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
        // dbg!(&self.options.entries);
    }
}
