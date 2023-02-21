#![recursion_limit = "2560"]

use ai_framework::differentiable_operations::{
    matrix_multiply, mean_axis, sparse_softmax_cross_entropy,
};
use ai_framework::graph;
use ai_framework::model_1::{
    calculate_loss, do_inference, loss_graph_observed_output_variable_id, loss_output_id,
    BatchValues, InputOutputSampleBatch, ParametersOptimizer, VariableValues,
};
#[allow(unused_imports)]
use ai_framework::optimizers_1::{AdaptiveGradientDescent, AdaptiveSGD, NaiveGradientDescent};
use ndarray::{s, ArcArray2, Axis};
use ordered_float::OrderedFloat;
use std::env::args;
use std::iter::zip;

mod mnist_data;

fn main() {
    live_prop_test::initialize();
    let path = args().collect::<Vec<_>>()[1].clone();
    let ((x_train, y_train), (x_test, y_test)) = mnist_data::load(path);
    let n = 60000; //1000;
    let x_train = x_train.slice_move(s![..n, ..]).into_dyn();
    let y_train = y_train.slice_move(s![..n, ..]).into_dyn();
    println!(
        "Loaded of shape {:?}, {:?}, {:?}, {:?}",
        x_train.shape(),
        y_train.shape(),
        x_test.shape(),
        y_test.shape()
    );

    let image_variable = "image";
    let parameter = "weights";
    let output = "output";

    let output_loss_graph = graph! {
        [let a = (sparse_softmax_cross_entropy())(output, loss_graph_observed_output_variable_id(output))];
        [@(loss_output_id()) = (mean_axis(0))(a)];
    };

    let train_inputs = BatchValues::new([(image_variable.to_owned(), x_train)]);
    let train_outputs = BatchValues::new([(output.to_owned(), y_train)]);
    let test_inputs = BatchValues::new([(image_variable.to_owned(), x_test)]);
    let test_outputs = BatchValues::new([(output.to_owned(), y_test.clone())]);

    let train_samples = InputOutputSampleBatch {
        inputs: train_inputs,
        outputs: train_outputs,
    };

    let test_samples = InputOutputSampleBatch {
        inputs: test_inputs,
        outputs: test_outputs,
    };

    let graph = graph! {
        [@(output) = (matrix_multiply())(image_variable, parameter)];
    };

    let parameter_value = ArcArray2::zeros((28 * 28, 10)).into_dyn();
    let mut parameters = VariableValues::new([(parameter.to_owned(), parameter_value)]);
    let lg = graph.compose(&output_loss_graph);
    //let mut optimizer = NaiveGradientDescent { learning_rate: 0.006 };
    //let mut optimizer = AdaptiveGradientDescent { learning_rate: 1.0 };
    let mut optimizer = AdaptiveSGD {
        learning_rate: 1.0,
        batch_size: 200,
    };
    for iteration in 0..100 {
        optimizer.step(
            &mut parameters,
            &train_samples.variable_values_including_observed_outputs(),
            &lg,
        );

        if iteration % 20 == 0 {
            let train_loss = calculate_loss(&parameters, &lg, &train_samples);

            let test_loss = calculate_loss(&parameters, &lg, &test_samples);

            let test_results = do_inference(
                &graph,
                &parameters.merge(&test_samples.variable_values_including_observed_outputs()),
            )
            .outputs[output]
                .clone();
            let mut num_correct = 0;
            for (&given, predictions) in zip(&y_test, test_results.axis_iter(Axis(0))) {
                let guessed = predictions
                    .iter()
                    .enumerate()
                    .max_by_key(|(_i, x)| OrderedFloat(**x))
                    .unwrap()
                    .0;
                let given = given as usize;
                if given == guessed {
                    num_correct += 1;
                }
            }
            let accuracy = num_correct as f32 / y_test.len_of(Axis(0)) as f32;

            println!("{iteration}:\n  Train loss: {train_loss}\n  Test loss:{test_loss}\n  Test accuracy: {accuracy}");
        }
    }
    println!("Done!")
}
