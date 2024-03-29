use crate::model_1::{backprop, do_inference, Graph, ParametersOptimizer};
use crate::model_shared::{BatchValues, VariableValues};
use autograd::rand;
use autograd::rand::distributions::uniform::SampleRange;

pub struct NaiveGradientDescent {
    pub learning_rate: f32,
}

impl ParametersOptimizer for NaiveGradientDescent {
    fn step(
        &mut self,
        parameters: &mut VariableValues,
        training_batch: &BatchValues,
        loss_graph: &Graph,
    ) {
        let variable_values: VariableValues = training_batch.merge(parameters);
        let inference_result = do_inference(loss_graph, &variable_values);
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        parameters.update(&gradients.variables, -self.learning_rate);
    }
}

pub struct AdaptiveGradientDescent {
    pub learning_rate: f32,
}

impl ParametersOptimizer for AdaptiveGradientDescent {
    fn step(
        &mut self,
        parameters: &mut VariableValues,
        training_batch: &BatchValues,
        loss_graph: &Graph,
    ) {
        let old_parameters = parameters.clone();
        let variable_values = training_batch.merge(parameters);
        let inference_result = do_inference(loss_graph, &variable_values);
        let old_loss = inference_result.loss();
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        parameters.update(&gradients.variables, -self.learning_rate);

        let variable_values = training_batch.merge(parameters);
        let new_loss = do_inference(loss_graph, &variable_values).loss();
        if new_loss > old_loss {
            parameters.clone_from(&old_parameters);
            self.learning_rate /= 2.0;
        } else {
            self.learning_rate *= 1.1;
        }
    }
}

pub struct AdaptiveSGD {
    pub learning_rate: f32,
    pub batch_size: usize,
    pub adapt_on_success: f32,
    pub adapt_on_failure: f32,
}

// impl AdaptiveSGD {
//     fn new(learning_rate: f32, batch_size: usize) {
//         AdaptiveSGD {
//             learning_rate,
//             batch_size,
//         }
//     }
// }

impl ParametersOptimizer for AdaptiveSGD {
    fn step(
        &mut self,
        parameters: &mut VariableValues,
        training_batch: &BatchValues,
        loss_graph: &Graph,
    ) {
        let train_samples: Vec<usize> = (0..self.batch_size)
            .map(|_| (0..training_batch.batch_size()).sample_single(&mut rand::thread_rng()))
            .collect();
        let test_samples: Vec<usize> = (0..self.batch_size)
            .map(|_| (0..training_batch.batch_size()).sample_single(&mut rand::thread_rng()))
            .collect();
        let old_parameters = parameters.clone();
        let test_batch = training_batch.sample_batch(&test_samples);
        let training_batch = training_batch.sample_batch(&train_samples);

        let old_test_loss = do_inference(loss_graph, &test_batch.merge(parameters)).loss();

        let variable_values = training_batch.merge(parameters);
        let inference_result = do_inference(loss_graph, &variable_values);
        let gradients = backprop(loss_graph, &variable_values, &inference_result);
        parameters.update(&gradients.variables, -self.learning_rate);

        let new_test_loss = do_inference(loss_graph, &test_batch.merge(parameters)).loss();
        if new_test_loss > old_test_loss {
            parameters.clone_from(&old_parameters);
            self.learning_rate *= self.adapt_on_failure;
        } else {
            self.learning_rate *= self.adapt_on_success;
        }
    }
}
