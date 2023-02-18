use ai_framework::differentiable_operations::{
    matrix_multiply, sparse_softmax_cross_entropy, DifferentiableOperation,
};
use ai_framework::model_1::{do_inference, train_1, Graph, InternalNode, TrainingSampleBatch};
use map_macro::map;
use ndarray::{Array2, Ix0};
use std::env::args;

mod mnist_data;

fn main() {
    let path = args().collect::<Vec<_>>()[1].clone();
    let ((x_train, y_train), (x_test, y_test)) = mnist_data::load(path);
    println!(
        "Loaded of shape {:?}, {:?}, {:?}, {:?}",
        x_train.shape(),
        y_train.shape(),
        x_test.shape(),
        y_test.shape()
    );

    let inputs = map! {"image".to_owned() => x_train};

    let samples = TrainingSampleBatch {
        inputs: inputs.clone(),
        outputs: map! {"output".to_owned() => y_train},
        output_loss_function: sparse_softmax_cross_entropy(),
    };

    let mut graph = Graph::default();
    let input = graph.new_variable("image");
    let parameter = graph.new_variable("weights");
    let layer = graph.new_node(InternalNode {
        inputs: vec![input, parameter],
        operation: matrix_multiply(),
    });
    let mut parameter_value = Array2::zeros((28 * 28, 10)).into_dyn();
    for iteration in 0..100 {
        train_1(
            map! {"weights".to_owned() => &mut parameter_value},
            graph,
            &samples,
            &mut NaiveGradientDescent {
                learning_rate: 0.0006,
            },
        );

        let inference_result = do_inference(graph, &inputs).outputs["output"].clone();
        let loss = sparse_softmax_cross_entropy()
            .forward(&[inference_result.view()])
            .into_dimensionality::<Ix0>()
            .unwrap()[()];
        println!("Loss: {loss}");
    }
    println!("Done!")
}
