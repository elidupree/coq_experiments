use crate::differentiable_operations::get_only_value;
use crate::model_1::{
    backprop, do_inference, loss_output_id, Graph, Optimizer, ValueMaybeBatch, VariableId,
};
use autograd::rand;
use autograd::rand::distributions::uniform::SampleRange;
use ndarray::{stack, Axis};
use std::collections::HashMap;

pub struct NaiveGradientDescent {
    pub learning_rate: f32,
}

impl Optimizer for NaiveGradientDescent {
    fn step(
        &mut self,
        mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        loss_graph: &Graph,
    ) {
        let mut variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant;
        variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let inference_result = do_inference(loss_graph, &variable_values);
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        for (id, value) in &mut parameters {
            **value -= &(gradients.variables[id].clone() * self.learning_rate);
        }
    }
}

pub struct AdaptiveGradientDescent {
    pub learning_rate: f32,
}

impl Optimizer for AdaptiveGradientDescent {
    fn step(
        &mut self,
        mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        loss_graph: &Graph,
    ) {
        let old_parameters: HashMap<VariableId, ValueMaybeBatch> = parameters
            .iter()
            .map(|(id, val)| (id.clone(), (**val).clone()))
            .collect();
        let mut variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant.clone();
        variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let inference_result = do_inference(loss_graph, &variable_values);
        let old_loss = *get_only_value(&inference_result.outputs[&loss_output_id()]);
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        for (id, value) in &mut parameters {
            **value -= &(gradients.variables[id].clone() * self.learning_rate);
        }
        let mut new_variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant;
        new_variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let new_inference_result = do_inference(loss_graph, &new_variable_values);
        let new_loss = *get_only_value(&new_inference_result.outputs[&loss_output_id()]);
        if new_loss > old_loss {
            for (id, p) in &mut parameters {
                **p = old_parameters[id].clone();
            }
            self.learning_rate /= 2.0;
        } else {
            self.learning_rate *= 1.1;
        }
    }
}

pub struct AdaptiveSGD {
    pub learning_rate: f32,
    pub batch_size: usize,
}

// impl AdaptiveSGD {
//     fn new(learning_rate: f32, batch_size: usize) {
//         AdaptiveSGD {
//             learning_rate,
//             batch_size,
//         }
//     }
// }

impl Optimizer for AdaptiveSGD {
    fn step(
        &mut self,
        mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        loss_graph: &Graph,
    ) {
        let n = variables_being_held_constant
            .values()
            .next()
            .unwrap()
            .shape()[0];
        let samples: Vec<usize> = (0..self.batch_size)
            .map(|_| (0..n).sample_single(&mut rand::thread_rng()))
            .collect();
        let old_parameters: HashMap<VariableId, ValueMaybeBatch> = parameters
            .iter()
            .map(|(id, val)| (id.clone(), (**val).clone()))
            .collect();
        let variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        stack(
                            Axis(0),
                            &samples
                                .iter()
                                .map(|&i| v.index_axis(Axis(0), i))
                                .collect::<Vec<_>>(),
                        )
                        .unwrap(),
                    )
                })
                .collect();
        let mut variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant.clone();
        variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let inference_result = do_inference(loss_graph, &variable_values);
        let old_loss = *get_only_value(&inference_result.outputs[&loss_output_id()]);
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        for (id, value) in &mut parameters {
            **value -= &(gradients.variables[id].clone() * self.learning_rate);
        }
        let mut new_variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant;
        new_variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let new_inference_result = do_inference(loss_graph, &new_variable_values);
        let new_loss = *get_only_value(&new_inference_result.outputs[&loss_output_id()]);
        if new_loss > old_loss {
            for (id, p) in &mut parameters {
                **p = old_parameters[id].clone();
            }
            self.learning_rate /= 2.0;
        } else {
            self.learning_rate *= 1.03;
        }
    }
}
