#![recursion_limit = "2560"]

use ai_framework::differentiable_operations::{mean_axis, sparse_softmax_cross_entropy};
use ai_framework::layered_sparse_model::Model;
use ai_framework::model_2::Graph;
use ai_framework::model_2::Node;
use ai_framework::model_shared::{
    loss_graph_observed_output_variable_id, loss_output_id, BatchValues, InputOutputSampleBatch,
};
#[allow(unused_imports)]
use ai_framework::optimizers_2::AdaptiveSGD;
use ndarray::{s, Axis};
use ordered_float::OrderedFloat;
use rand::distributions::uniform::SampleRange;
use std::env::args;
use std::iter::zip;
use std::process::Command;
use std::time::Instant;

mod mnist_data;

fn main() {
    live_prop_test::initialize();
    let path = args().collect::<Vec<_>>()[1].clone();
    let ((x_train, y_train), (x_test, y_test)) = mnist_data::load(path);
    let n = 60000; //1000;
    let t = 10000; //1000;
    let x_train = x_train.slice_move(s![..n, ..]).into_dyn();
    let y_train = y_train.slice_move(s![..n, ..]).into_dyn();
    let x_test = x_test.slice_move(s![..t, ..]).into_dyn();
    let y_test = y_test.slice_move(s![..t, ..]).into_dyn();
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

    let mut output_loss_graph = Graph::default();
    let a = output_loss_graph.new_node(Node {
        inputs: vec![
            output.into(),
            loss_graph_observed_output_variable_id(output).into(),
        ],
        operation: sparse_softmax_cross_entropy(),
    });
    let b = output_loss_graph.new_node(Node {
        inputs: vec![a.into()],
        operation: mean_axis(0),
    });
    output_loss_graph.new_output(loss_output_id(), b);

    let train_inputs = BatchValues::new([(image_variable.to_owned(), x_train.clone())]);
    let train_outputs = BatchValues::new([(output.to_owned(), y_train.clone())]);
    let test_inputs = BatchValues::new([(image_variable.to_owned(), x_test.clone())]);
    let test_outputs = BatchValues::new([(output.to_owned(), y_test.clone())]);

    let train_samples = InputOutputSampleBatch {
        inputs: train_inputs,
        outputs: train_outputs,
    }
    .variable_values_including_observed_outputs();

    let test_samples = InputOutputSampleBatch {
        inputs: test_inputs,
        outputs: test_outputs,
    }
    .variable_values_including_observed_outputs();

    let mut model = Model::new_1(
        (image_variable.into(), x_train.len_of(Axis(1))),
        (output.into(), 10),
        &output_loss_graph,
    );

    let mut optimizer = AdaptiveSGD {
        learning_rate: 1.0,
        batch_size: 200,
        adapt_on_success: 1.03,
        adapt_on_failure: 0.96,
    };
    let start = Instant::now();
    for pass in 0..100 {
        println!("{pass} adding edges...");
        let train_sample_indices: Vec<usize> = (0..optimizer.batch_size * 10)
            .map(|_| (0..train_samples.batch_size()).sample_single(&mut rand::thread_rng()))
            .collect();
        model.add_promising_edges(&train_samples.sample_batch(&train_sample_indices));
        // if pass > 10 {
        //     model.remove_random_edges();
        // }
        // dbg!(&model);
        println!("{pass} optimizing...");
        for _iteration in 0..50 {
            optimizer.step(&mut model.graph, &train_samples);
        }

        if pass % 10 == 9 {
            let train_loss = model.graph.loss(&train_samples);

            let test_loss = model.graph.loss(&test_samples);

            let mut file = std::fs::File::create("mnist_model_2_graph.dot").unwrap();
            model.draw_graphviz(&train_samples, &mut file).unwrap();
            dbg!(Command::new("sh")
                .args([
                    "-c",
                    "dot -Tpng mnist_model_2_graph.dot > mnist_model_2_graph.png",
                ])
                .output())
            .unwrap();

            // let train_results = model.graph.do_inference(&train_samples);
            // let train_gradients = model.graph.backprop(&train_samples, &train_results);
            // dbg!(train_gradients);
            let test_results = model.graph.do_inference(&test_samples).outputs[output].clone();
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

            println!("{pass}:\n  Train loss: {train_loss}\n  Test loss:{test_loss}\n  Test accuracy: {accuracy}\n  Learning rate:{},\n  Time:{:?}", optimizer.learning_rate, start.elapsed());
        }
    }
    println!("Done!")
}
