use live_prop_test::{live_prop_test, lpt_assert_eq};
use ndarray::{arr0, ArrayD, ArrayViewD, Axis, Ix0, Zip};
use std::fmt::{Debug, Formatter};
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

impl AnyDifferentiableOperation {
    fn new(operation_impl: impl DifferentiableOperation + Debug + 'static) -> Self {
        AnyDifferentiableOperation {
            name: format!("{:?}", &operation_impl),
            operation_impl: Arc::new(operation_impl),
        }
    }
}

impl Debug for AnyDifferentiableOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
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

#[derive(Copy, Clone, Debug)]
struct SumInputs;
pub fn sum_inputs() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(SumInputs)
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
    AnyDifferentiableOperation::new(MeanSquaredDifference)
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
    AnyDifferentiableOperation::new(MatrixMultiply)
}

impl DifferentiableOperation for MatrixMultiply {
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
struct SparseSoftmaxCrossEntropy;
pub fn sparse_softmax_cross_entropy() -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(SparseSoftmaxCrossEntropy)
}

impl DifferentiableOperation for SparseSoftmaxCrossEntropy {
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
struct MeanAxis(usize);
pub fn mean_axis(axis: usize) -> AnyDifferentiableOperation {
    AnyDifferentiableOperation::new(MeanAxis(axis))
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
