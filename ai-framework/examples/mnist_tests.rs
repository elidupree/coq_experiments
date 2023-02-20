#![recursion_limit = "2560"]

use ai_framework::differentiable_operations::{
    matrix_multiply, mean_axis, sparse_softmax_cross_entropy,
};
use ai_framework::graph;
use ai_framework::model_1::{
    calculate_loss, loss_graph_observed_output_variable_id, loss_output_id, InputOutputSampleBatch,
    Optimizer,
};
use ai_framework::optimizers_1::{AdaptiveGradientDescent, NaiveGradientDescent};
use map_macro::map;
use ndarray::{s, Array2};
use std::env::args;

mod mnist_data;

fn main() {
    live_prop_test::initialize();
    let path = args().collect::<Vec<_>>()[1].clone();
    let ((x_train, y_train), (x_test, y_test)) = mnist_data::load(path);
    let n = 1000;
    let x_train = x_train.slice(s![..n, ..]).to_owned().into_dyn();
    let y_train = y_train.slice(s![..n, ..]).to_owned().into_dyn();
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

    let train_samples = InputOutputSampleBatch {
        inputs: map! {image_variable.to_owned() => x_train},
        outputs: map! {output.to_owned() => y_train},
        output_loss_graph: output_loss_graph.clone(),
    };

    let test_samples = InputOutputSampleBatch {
        inputs: map! {image_variable.to_owned() => x_test},
        outputs: map! {output.to_owned() => y_test},
        output_loss_graph,
    };

    let graph = graph! {
        [@(output) = (matrix_multiply())(image_variable, parameter)];
    };

    let mut parameter_value = Array2::zeros((28 * 28, 10)).into_dyn();
    let lg = graph.compose(&train_samples.output_loss_graph);
    let mut optimizer = AdaptiveGradientDescent { learning_rate: 1.0 };
    for iteration in 0..100000 {
        optimizer.step(
            map! {"weights".to_owned() => &mut parameter_value},
            train_samples.variable_values_including_observed_outputs(),
            &lg,
        );

        let train_loss = calculate_loss(
            map! {"weights".to_owned() => & parameter_value},
            &lg,
            &train_samples,
        );

        let test_loss = calculate_loss(
            map! {"weights".to_owned() => & parameter_value},
            &lg,
            &test_samples,
        );
        println!("{iteration}:\n  Train loss: {train_loss}\n  Test loss:{test_loss}");
    }
    println!("Done!")
}
