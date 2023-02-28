use crate::model_2::Graph;
use crate::model_shared::BatchValues;
use autograd::rand;
use autograd::rand::distributions::uniform::SampleRange;

pub struct AdaptiveSGD {
    pub learning_rate: f32,
    pub batch_size: usize,
    pub adapt_on_success: f32,
    pub adapt_on_failure: f32,
}

impl AdaptiveSGD {
    pub fn step(&mut self, graph: &mut Graph, training_batch: &BatchValues) {
        let train_samples: Vec<usize> = (0..self.batch_size)
            .map(|_| (0..training_batch.batch_size()).sample_single(&mut rand::thread_rng()))
            .collect();
        let test_samples: Vec<usize> = (0..self.batch_size)
            .map(|_| (0..training_batch.batch_size()).sample_single(&mut rand::thread_rng()))
            .collect();
        let old_graph = graph.clone();
        let test_batch = training_batch.sample_batch(&test_samples);
        let training_batch = training_batch.sample_batch(&train_samples);

        let old_test_loss = graph.loss(&test_batch);

        let inference_result = graph.do_inference(&training_batch);
        let gradients = graph.backprop(&training_batch, &inference_result);
        graph.update(&gradients, -self.learning_rate);

        let new_test_loss = graph.loss(&test_batch);
        if new_test_loss > old_test_loss {
            graph.clone_from(&old_graph);
            self.learning_rate *= self.adapt_on_failure;
        } else {
            self.learning_rate *= self.adapt_on_success;
        }
    }
}
