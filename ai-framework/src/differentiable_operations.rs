use crate::model_shared::{Array, ArrayExt};
use autograd::tensor_ops::grad_with_default;
use autograd::{Context, Evaluator, Tensor};
use live_prop_test::{live_prop_test, lpt_assert_eq};
use ndarray::{ArrayViewD, Axis, Ix0, Zip};
use std::cell::RefCell;
use std::fmt::{Debug, Display, Formatter};
use std::iter::zip;
use std::sync::Arc;

pub fn get_only_value<T>(i: impl IntoIterator<Item = T>) -> T {
    let mut i = i.into_iter();
    let result = i.next().unwrap();
    assert!(i.next().is_none());
    result
}

#[live_prop_test]
pub trait DifferentiableOperation: Send + Sync {
    fn forward(&self, inputs: &[Array]) -> Array;

    #[live_prop_test(
        postcondition = "gradient_reasonably_correct(self, inputs, old(output_gradient.clone()), &result)"
    )]
    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array>;

    fn forward_scalar(&self, input: f32) -> f32 {
        self.forward(&[Array::from_scalar(input)]).as_scalar()
    }
}

fn gradient_reasonably_correct(
    _operation: &(impl DifferentiableOperation + ?Sized),
    inputs: &[Array],
    _output_gradient: Array,
    result: &[Array],
) -> Result<(), String> {
    lpt_assert_eq!(inputs.len(), result.len());
    for (i, r) in zip(inputs, result) {
        lpt_assert_eq!(i.shape(), r.shape());
    }
    // let epsilon = 0.000001;
    // let lots = 100000.0;
    // let original_output = operation.forward(inputs);
    // let inputs: Vec<_> = inputs.iter().map(ToOwned::to_owned).collect();
    // for index in 0..inputs.len() {
    //     let mut inputs = inputs.clone();
    //     inputs [index] +=
    // }
    Ok(())
}

// TODO: do we need to be able to deserialize these things ? how to deal with that ?
#[derive(Clone)]
pub struct AnyDifferentiableOperation {
    name: String,
    operation_impl: Arc<dyn DifferentiableOperation>,
}

#[derive(Clone)]
pub struct AutogradWrapper {
    #[allow(clippy::type_complexity)]
    graph_setup: Arc<
        dyn for<'a> Fn(&'a Context<'a, f32>, &[Tensor<'a, f32>]) -> Tensor<'a, f32> + Send + Sync,
    >,
}

impl AnyDifferentiableOperation {
    fn new(
        name: impl Into<String>,
        operation_impl: impl DifferentiableOperation + 'static,
    ) -> Self {
        AnyDifferentiableOperation {
            name: name.into(),
            operation_impl: Arc::new(operation_impl),
        }
    }
}

impl Debug for AnyDifferentiableOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.name, f)
    }
}

impl Display for AnyDifferentiableOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.name, f)
    }
}

struct AutogradContextHack<'graph, 'env, 'feed> {
    context: &'graph Context<'env, f32>,
    evaluator: Evaluator<'graph, 'env, 'feed, f32>,
    next_placeholder_index: usize,
}
impl<'graph, 'env, 'feed> AutogradContextHack<'graph, 'env, 'feed> {
    fn placeholder<'b>(&'b mut self, input: ArrayViewD<'feed, f32>) -> Tensor<'graph, f32> {
        thread_local! {
            static AUTOGRAD_PLACEHOLDERS_HACK: RefCell<Vec<&'static str>> = RefCell:: new (Vec:: new());
        }
        AUTOGRAD_PLACEHOLDERS_HACK.with(|hack| {
            let mut hack = hack.borrow_mut();
            while hack.len() <= self.next_placeholder_index {
                let name = hack.len().to_string().leak();
                hack.push(name);
            }
            let name = hack[self.next_placeholder_index];
            let result = self.context.placeholder(
                name,
                &input
                    .shape()
                    .iter()
                    .map(|&d| d as isize)
                    .collect::<Vec<_>>(),
            );
            self.evaluator.feed(name, input);
            self.next_placeholder_index += 1;
            result
        })
    }
    fn placeholders<'b>(&'b mut self, inputs: &'feed [Array]) -> Vec<Tensor<'graph, f32>> {
        inputs
            .iter()
            .map(|input| self.placeholder(input.view()))
            .collect()
    }
}

#[live_prop_test(use_trait_tests)]
impl DifferentiableOperation for AnyDifferentiableOperation {
    fn forward(&self, inputs: &[Array]) -> Array {
        // dbg!(
        //     &self.name,
        //     inputs.iter().map(|a| a.shape()).collect::<Vec<_>>()
        // );
        self.operation_impl.forward(inputs)
    }

    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        // dbg!(
        //     &self.name,
        //     inputs.iter().map(|a| a.shape()).collect::<Vec<_>>()
        // );
        self.operation_impl.gradient(inputs, output_gradient)
    }
}

impl DifferentiableOperation for AutogradWrapper {
    fn forward(&self, inputs: &[Array]) -> Array {
        autograd::run(|context| {
            let mut context = AutogradContextHack {
                context,
                evaluator: context.evaluator(),
                next_placeholder_index: 0,
            };
            let output = (self.graph_setup)(context.context, &context.placeholders(inputs));
            context
                .evaluator
                .push(output)
                .run()
                .pop()
                .unwrap()
                .unwrap()
                .into_shared()
        })
    }

    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        autograd::run(|context| {
            let mut context = AutogradContextHack {
                context,
                evaluator: context.evaluator(),
                next_placeholder_index: 0,
            };
            let input_tensors = context.placeholders(inputs);
            let output_gradient = context.placeholder(output_gradient.view());
            let output = (self.graph_setup)(context.context, &input_tensors);
            let grads = grad_with_default(&[output], &input_tensors, &[output_gradient]);
            let result = context
                .evaluator
                .extend(&grads)
                .run()
                .into_iter()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            zip(inputs, result)
                .map(|(input, grad)| {
                    if grad.shape() != input.shape() {
                        Array::ones(input.shape())
                    } else {
                        grad.into_shared()
                    }
                })
                .collect()
        })
    }
}

#[derive(Copy, Clone, Debug)]
struct Identity;
pub fn identity() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("identity", Identity)
}

impl DifferentiableOperation for Identity {
    fn forward(&self, inputs: &[Array]) -> Array {
        let [a]: &[Array; 1] = inputs.try_into().unwrap();
        a.clone()
    }

    fn gradient(&self, _inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        vec![output_gradient]
    }
}

// #[derive(Copy, Clone, Debug)]
// struct SumInputs;
// pub fn sum_inputs() -> AnyDifferentiableOperation {
//     AnyDifferentiableOperation::new("sum_inputs", SumInputs)
// }
//
// impl DifferentiableOperation for SumInputs {
//     fn forward(&self, inputs: &[Array]) -> Array {
//         let mut result = Array::zeros(inputs[0].shape());
//         for input in inputs {
//             result += input;
//         }
//         result
//     }
//
//     fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
//         inputs.iter().map(|_| output_gradient.clone()).collect()
//     }
// }

#[derive(Copy, Clone, Debug)]
struct ScalarAdd;
pub fn scalar_add() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("scalar_multiply", ScalarAdd)
}

impl DifferentiableOperation for ScalarAdd {
    fn forward(&self, inputs: &[Array]) -> Array {
        let [a, b]: &[Array; 2] = inputs.try_into().unwrap();
        a.clone() + b.as_scalar()
    }

    fn gradient(&self, _inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        vec![
            output_gradient.clone(),
            Array::from_scalar(output_gradient.sum()),
        ]
    }
}

#[derive(Copy, Clone, Debug)]
struct ScalarMultiply;
pub fn scalar_multiply() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("scalar_multiply", ScalarMultiply)
}

impl DifferentiableOperation for ScalarMultiply {
    fn forward(&self, inputs: &[Array]) -> Array {
        let [a, b]: &[Array; 2] = inputs.try_into().unwrap();
        a.clone() * b.as_scalar()
    }

    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        let [a, b]: &[Array; 2] = inputs.try_into().unwrap();
        vec![
            output_gradient.clone() * b.as_scalar(),
            Array::from_scalar((output_gradient * a).sum()),
        ]
    }
}

#[derive(Copy, Clone, Debug)]
struct MeanSquaredDifference;
pub fn mean_squared_difference() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("mean_squared_difference", MeanSquaredDifference)
}

impl DifferentiableOperation for MeanSquaredDifference {
    fn forward(&self, inputs: &[Array]) -> Array {
        let [a, b]: &[Array; 2] = inputs.try_into().unwrap();
        assert_eq!(a.len(), b.len());
        Array::from_scalar(a.squared_difference(b) / a.len() as f32)
    }

    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        let [a, b]: &[Array; 2] = inputs.try_into().unwrap();
        let output_gradient = output_gradient.into_dimensionality::<Ix0>().unwrap()[()];
        let factor = output_gradient / a.len() as f32;
        let mut a = a.clone();
        let mut b = b.clone();
        Zip::from(&mut a).and(&mut b).for_each(|a, b| {
            let d = 2.0 * (*a - *b);
            *a = d * factor;
            *b = -d * factor;
        });

        vec![a, b]
    }
}

#[derive(Copy, Clone, Debug)]
struct MeanAxis(usize);
pub fn mean_axis(axis: usize) -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(format!("mean_axis({axis})"), MeanAxis(axis))
}

impl DifferentiableOperation for MeanAxis {
    fn forward(&self, inputs: &[Array]) -> Array {
        let [a]: &[Array; 1] = inputs.try_into().unwrap();
        a.mean_axis(Axis(self.0)).unwrap().into_shared()
    }

    fn gradient(&self, inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        let [a]: &[Array; 1] = inputs.try_into().unwrap();
        let axis_length = a.len_of(Axis(self.0));
        vec![(output_gradient).broadcast(a.shape()).unwrap().to_shared() / axis_length as f32]
    }
}

#[derive(Copy, Clone, Debug)]
struct Stack(usize);
pub fn stack(axis: usize) -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("stack", Stack(axis))
}

impl DifferentiableOperation for Stack {
    fn forward(&self, inputs: &[Array]) -> Array {
        ndarray::stack(
            Axis(self.0),
            &inputs.iter().map(|a| a.view()).collect::<Vec<_>>(),
        )
        .unwrap()
        .into_shared()
    }

    fn gradient(&self, _inputs: &[Array], output_gradient: Array) -> Vec<Array> {
        output_gradient
            .axis_iter(Axis(self.0))
            .map(|a| a.to_shared())
            .collect()
    }
}

macro_rules! autograd_wrapper {
    ($name:ident()[$($input_binding: ident),*$(,)*] => $body:expr) => {
        pub fn $name() -> AnyDifferentiableOperation {
            AnyDifferentiableOperation::new(
                ::std::stringify!($name),
                AutogradWrapper {
                    graph_setup: Arc::new(|_context, inputs| {
                        #[allow(unused_imports)]
                        use autograd::tensor_ops::*;
                        let [$($input_binding),*] = inputs else { panic!("Wrong number of inputs to {} operation", ::std::stringify!($name)) };
                        $body
                    }),
                },
            )
        }
    };
    ($name:ident()($input_binding: ident) => $body:expr) => {
        pub fn $name() -> AnyDifferentiableOperation {
            AnyDifferentiableOperation::new(
                ::std::stringify!($name),
                AutogradWrapper {
                    graph_setup: Arc::new(|_context, inputs| {
                        #[allow(unused_imports)]
                        use autograd::tensor_ops::*;
                        let $input_binding = inputs;
                        $body
                    }),
                },
            )
        }
    };
}

// TODO: fix bug when inputs has length 1
autograd_wrapper!(sum_inputs()(inputs) => add_n(inputs));
autograd_wrapper!(matrix_multiply()[a, b] => matmul(a, b));
// autograd_wrapper!(mul()[a, b] => mul(a, b));
autograd_wrapper!(sparse_softmax_cross_entropy()[a, b] => sparse_softmax_cross_entropy(a, b));
autograd_wrapper!(softplus()[a] => softplus(a));
autograd_wrapper!(sigmoid()[a] => sigmoid(a));

pub fn activation_functions() -> Vec<AnyDifferentiableOperation> {
    vec![identity(), softplus(), sigmoid()]
}
