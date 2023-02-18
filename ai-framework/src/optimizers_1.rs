use crate::model_1::{Graph, Optimize, ValueMaybeBatch, VariableId};
use std::collections::HashMap;

pub struct NaiveGradientDescent {
    pub learning_rate: f32,
}

impl Optimize for NaiveGradientDescent {
    fn optimize(
        &mut self,
        parameters: HashMap<VariableId, &mut ValueMaybeBatch>,
        variables_being_held_constant: HashMap<VariableId, ValueMaybeBatch>,
        graph: &Graph,
    ) {
        todo!()
    }
}
