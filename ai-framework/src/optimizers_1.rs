use crate::model_1::{backprop, do_inference, Graph, Optimize, ValueMaybeBatch, VariableId};
use std::collections::HashMap;

pub struct NaiveGradientDescent {
    pub learning_rate: f32,
}

impl Optimize for NaiveGradientDescent {
    fn optimize(
        &mut self,
        mut parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        graph: &Graph,
    ) {
        let mut variable_values: HashMap<VariableId, ValueMaybeBatch> =
            variables_being_held_constant;
        variable_values.extend(parameters.iter().map(|(k, v)| (k.clone(), (**v).clone())));
        let inference_result = do_inference(graph, &variable_values);
        let gradients = backprop(graph, &variable_values, &inference_result);
        for (id, value) in &mut parameters {
            **value -= &(gradients.variables[id].clone() * self.learning_rate);
        }
    }
}
