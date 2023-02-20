use autograd::tensor_ops::grad_with_default;
use autograd::{tensor_ops, Context, Evaluator, Tensor};
use live_prop_test::{live_prop_test, lpt_assert_eq};
use ndarray::{arr0, ArrayD, ArrayViewD, Axis, Ix0, Ix2, Zip};
use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::iter::zip;
use std::sync::Arc;

#[live_prop_test]
pub trait DifferentiableOperation: Send + Sync {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32>;

    #[live_prop_test(
        postcondition = "gradient_reasonably_correct(self, inputs, old(output_gradient.clone()), &result)"
    )]
    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>>;
}

fn gradient_reasonably_correct(
    _operation: &(impl DifferentiableOperation + ?Sized),
    inputs: &[ArrayViewD<f32>],
    _output_gradient: ArrayViewD<f32>,
    result: &[ArrayD<f32>],
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
        self.name.fmt(f)
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
    fn placeholders<'b>(
        &'b mut self,
        inputs: &[ArrayViewD<'feed, f32>],
    ) -> Vec<Tensor<'graph, f32>> {
        inputs
            .iter()
            .map(|input| self.placeholder(input.clone()))
            .collect()
    }
    fn run<R>(f: impl FnOnce(AutogradContextHack) -> R) -> R {
        autograd::run(|context| {
            let mut this = AutogradContextHack {
                context,
                evaluator: context.evaluator(),
                next_placeholder_index: 0,
            };
            f(this)
        })
    }
}

#[live_prop_test(use_trait_tests)]
impl DifferentiableOperation for AnyDifferentiableOperation {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        self.operation_impl.forward(inputs)
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        self.operation_impl.gradient(inputs, output_gradient)
    }
}

impl DifferentiableOperation for AutogradWrapper {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        autograd::run(|context| {
            let mut context = AutogradContextHack {
                context,
                evaluator: context.evaluator(),
                next_placeholder_index: 0,
            };
            let output = (self.graph_setup)(context.context, &context.placeholders(inputs));
            context.evaluator.push(output).run().pop().unwrap().unwrap()
        })
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        autograd::run(|context| {
            let mut context = AutogradContextHack {
                context,
                evaluator: context.evaluator(),
                next_placeholder_index: 0,
            };
            let input_tensors = context.placeholders(
                &inputs
                    .iter()
                    .map(|v| v.clone().reborrow())
                    .collect::<Vec<_>>(),
            );
            let output_gradient = context.placeholder(output_gradient.reborrow());
            let output = (self.graph_setup)(context.context, &input_tensors);
            let grads = grad_with_default(&[output], &input_tensors, &[output_gradient]);
            let mut result = context
                .evaluator
                .extend(&grads)
                .run()
                .into_iter()
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            for (input, grad) in zip(inputs, &mut result) {
                if grad.shape() != input.shape() {
                    *grad = ArrayD::zeros(input.shape());
                }
            }
            result
        })
    }
}

#[derive(Copy, Clone, Debug)]
struct SumInputs;
pub fn sum_inputs() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("sum_inputs", SumInputs)
}

impl DifferentiableOperation for SumInputs {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        let mut result = ArrayD::zeros(inputs[0].shape());
        for input in inputs {
            result += input;
        }
        result
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        inputs.iter().map(|_| output_gradient.to_owned()).collect()
    }
}

#[derive(Copy, Clone, Debug)]
struct MeanSquaredDifference;
pub fn mean_squared_difference() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("mean_squared_difference", MeanSquaredDifference)
}

impl DifferentiableOperation for MeanSquaredDifference {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        let [a, b]: &[ArrayViewD<f32>; 2] = inputs.try_into().unwrap();
        arr0(
            Zip::from(a).and(b).par_fold(
                || 0.0,
                |sum, a, b| sum + (a - b).powi(2),
                |sum1, sum2| sum1 + sum2,
            ) / a.len() as f32,
        )
        .into_dyn()
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        let [a, b]: &[ArrayViewD<f32>; 2] = inputs.try_into().unwrap();
        let output_gradient = output_gradient.into_dimensionality::<Ix0>().unwrap()[()];
        let factor = output_gradient / a.len() as f32;
        let mut a = a.to_owned();
        let mut b = b.to_owned();
        Zip::from(&mut a).and(&mut b).par_for_each(|a, b| {
            let d = 2.0 * (*a - *b);
            *a = d * factor;
            *b = -d * factor;
        });

        vec![a, b]
    }
}

#[derive(Copy, Clone, Debug)]
struct MatrixMultiply;
pub fn matrix_multiply() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new("matrix_multiply", MatrixMultiply)
}

impl DifferentiableOperation for MatrixMultiply {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        let [a, b]: &[ArrayViewD<f32>; 2] = inputs.try_into().unwrap();
        let a = a.clone().into_dimensionality::<Ix2>().unwrap();
        let b = b.clone().into_dimensionality::<Ix2>().unwrap();
        a.dot(&b).into_dyn()
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        todo!()
    }
}

pub fn sparse_softmax_cross_entropy() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(
        "sparse_softmax_cross_entropy",
        AutogradWrapper {
            graph_setup: Arc::new(|context, inputs| {
                let [a, b]: &[Tensor<f32>; 2] = inputs.try_into().unwrap();
                tensor_ops::sparse_softmax_cross_entropy(a, b)
            }),
        },
    )
}

#[derive(Copy, Clone, Debug)]
struct MeanAxis(usize);
pub fn mean_axis(axis: usize) -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(format!("mean_axis({axis})"), MeanAxis(axis))
}

impl DifferentiableOperation for MeanAxis {
    fn forward(&self, inputs: &[ArrayViewD<f32>]) -> ArrayD<f32> {
        let [a]: &[ArrayViewD<f32>; 1] = inputs.try_into().unwrap();
        a.mean_axis(Axis(self.0)).unwrap()
    }

    fn gradient(
        &self,
        inputs: &[ArrayViewD<f32>],
        output_gradient: ArrayViewD<f32>,
    ) -> Vec<ArrayD<f32>> {
        let [a]: &[ArrayViewD<f32>; 1] = inputs.try_into().unwrap();
        let axis_length = a.len_of(Axis(self.0));
        vec![(output_gradient).broadcast(a.shape()).unwrap().to_owned() * axis_length as f32]
    }
}
