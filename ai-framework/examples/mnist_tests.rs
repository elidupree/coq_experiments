#![recursion_limit = "2560"]

use ai_framework::differentiable_operations::{
    matrix_multiply, mean_axis, softplus, sparse_softmax_cross_entropy,
};
use ai_framework::graph_1;
use ai_framework::model_1::{calculate_loss, do_inference, ParametersOptimizer};
use ai_framework::model_shared::{
    loss_graph_observed_output_variable_id, loss_output_id, BatchValues, InputOutputSampleBatch,
    VariableValues,
};
#[allow(unused_imports)]
use ai_framework::optimizers_1::{AdaptiveGradientDescent, AdaptiveSGD, NaiveGradientDescent};
use ndarray::{s, Axis};
use ordered_float::OrderedFloat;
use std::env::args;
use std::iter::zip;
use std::time::Instant;

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
    // let parameter = "weights";
    let output = "output";

    let output_loss_graph = graph_1! {
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

    let graph = graph_1! {
        [let a = (matrix_multiply())(image_variable, "p1")];
        [let b = (softplus())(a)];
        // [let b = (matrix_multiply())(a, "p2")];
        [@(output) = (matrix_multiply())(b, "p3")];
    };

    let array_gen = autograd::ndarray_ext::ArrayRng::default();
    let mut parameters = VariableValues::new([
        (
            "p1".to_owned(),
            array_gen.glorot_uniform(&[28 * 28, 10]).into_shared(),
        ),
        // ("p2".to_owned(), ArcArray2::zeros((10, 10)).into_dyn()),
        (
            "p3".to_owned(),
            array_gen.glorot_uniform(&[10, 10]).into_shared(),
        ),
    ]);
    let lg = graph.compose(&output_loss_graph);
    //let mut optimizer = NaiveGradientDescent { learning_rate: 0.006 };
    //let mut optimizer = AdaptiveGradientDescent { learning_rate: 1.0 };
    let mut optimizer = AdaptiveSGD {
        learning_rate: 1.0,
        batch_size: 200,
        adapt_on_success: 1.03,
        adapt_on_failure: 0.96,
    };
    let start = Instant::now();
    for iteration in 0..1000 {
        optimizer.step(
            &mut parameters,
            &train_samples.variable_values_including_observed_outputs(),
            &lg,
        );

        if iteration % 50 == 0 {
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

            println!("{iteration}:\n  Train loss: {train_loss}\n  Test loss:{test_loss}\n  Test accuracy: {accuracy}\n  Learning rate:{},\n  Time:{:?}", optimizer.learning_rate, start.elapsed());
        }
    }
    println!("Done!")
}
