use crate::differentiable_operations::get_only_value;
use ndarray::{arr0, stack, ArcArray, Axis, IxDyn, Slice, Zip};
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use uuid::Uuid;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
pub struct NodeId(pub Uuid);

impl NodeId {
    pub fn new_random() -> Self {
        NodeId(Uuid::new_v4())
    }
}

pub type Array = ArcArray<f32, IxDyn>;

pub trait ArrayExt: Sized {
    fn from_scalar(x: f32) -> Self;
    fn as_scalar(&self) -> f32;
    fn norm_squared(&self) -> f32;
    fn norm(&self) -> f32;
    fn normalize(&mut self);
    fn normalized(self) -> Option<Self>;
    fn squared_difference(&self, other: &Array) -> f32;
}

impl ArrayExt for Array {
    fn from_scalar(x: f32) -> Self {
        arr0(x).into_dyn().into_shared()
    }
    fn as_scalar(&self) -> f32 {
        *get_only_value(self)
    }

    fn norm_squared(&self) -> f32 {
        self.iter().map(|a| a * a).sum()
    }

    fn norm(&self) -> f32 {
        self.norm_squared().sqrt()
    }

    fn normalize(&mut self) {
        let norm = self.norm();
        *self /= norm;
    }

    fn normalized(self) -> Option<Self> {
        let norm = self.norm();
        (norm != 0.0).then(|| self / norm)
    }

    fn squared_difference(&self, other: &Array) -> f32 {
        Zip::from(self)
            .and(other)
            .fold(0.0, |sum, a, b| sum + (a - b).powi(2))
    }
}

pub type VariableId = String;
pub type OutputId = VariableId;

#[derive(Clone, Debug, Default)]
pub struct VariableValues {
    values: HashMap<VariableId, Array>,
}

#[derive(Clone, Debug)]
pub struct BatchValues {
    values: VariableValues,
    batch_size: usize,
}

impl Deref for VariableValues {
    type Target = HashMap<VariableId, Array>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for VariableValues {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl Deref for BatchValues {
    type Target = VariableValues;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for BatchValues {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl VariableValues {
    pub fn new(values: impl IntoIterator<Item = (VariableId, Array)>) -> VariableValues {
        let values = values.into_iter().collect();
        VariableValues { values }
    }

    pub fn get<Q>(&self, id: &Q) -> Array
    where
        VariableId: Borrow<Q>,
        Q: Hash + Eq + Debug + ?Sized,
    {
        self.values
            .get(id)
            .unwrap_or_else(|| {
                panic!("Tried to get value of variable {id:?} in a batch without that variable")
            })
            .clone()
    }

    pub fn get_mut<Q: Debug>(&mut self, id: &Q) -> &mut Array
    where
        VariableId: Borrow<Q>,
        Q: Hash + Eq + Debug + ?Sized,
    {
        self.values.get_mut(id).unwrap_or_else(|| {
            panic!("Tried to get value of variable {id:?} in a batch without that variable")
        })
    }

    pub fn merge(&self, other: &VariableValues) -> VariableValues {
        let mut values = self.values.clone();
        values.extend(other.values.iter().map(|(i, v)| (i.clone(), v.clone())));
        VariableValues { values }
    }

    pub fn update(&mut self, other: &VariableValues, factor: f32) {
        for (id, value) in &mut self.values {
            *value = (other[id].clone() * factor) + value.view();
        }
    }
}

pub trait Merge<Other> {
    fn merge(&self, other: &Other) -> Self;
}

impl Merge<BatchValues> for VariableValues {
    fn merge(&self, other: &BatchValues) -> Self {
        self.merge(other)
    }
}

impl Merge<BatchValues> for BatchValues {
    fn merge(&self, other: &BatchValues) -> Self {
        assert_eq!(self.batch_size, other.batch_size);
        BatchValues {
            batch_size: self.batch_size,
            values: self.values.merge(&other.values),
        }
    }
}

impl BatchValues {
    pub fn new(values: impl IntoIterator<Item = (VariableId, Array)>) -> BatchValues {
        let values = VariableValues::new(values);
        let mut iter = values.values.values();
        let first = iter.next().unwrap();
        let batch_size = first.len_of(Axis(0));
        for a in iter {
            assert_eq!(a.len_of(Axis(0)), batch_size);
        }
        BatchValues { values, batch_size }
    }
    pub fn empty_with_batch_size(batch_size: usize) -> BatchValues {
        BatchValues {
            values: Default::default(),
            batch_size,
        }
    }

    pub fn batch_size(&self) -> usize {
        self.batch_size
    }

    pub fn slice_batch(&self, slice: Slice) -> BatchValues {
        let values: HashMap<VariableId, Array> = self
            .values
            .values
            .iter()
            .map(|(id, value)| {
                (id.clone(), {
                    let mut value = value.clone();
                    value.slice_axis_inplace(Axis(0), slice);
                    value
                })
            })
            .collect();
        let batch_size = values.values().next().unwrap().len_of(Axis(0));
        BatchValues {
            batch_size,
            values: VariableValues { values },
        }
    }

    pub fn sample_batch(&self, samples: &[usize]) -> BatchValues {
        let values = self
            .values
            .values
            .iter()
            .map(|(id, value)| {
                (
                    id.clone(),
                    stack(
                        Axis(0),
                        &samples
                            .iter()
                            .map(|&i| value.index_axis(Axis(0), i))
                            .collect::<Vec<_>>(),
                    )
                    .unwrap()
                    .into_shared(),
                )
            })
            .collect();
        let batch_size = samples.len();
        BatchValues {
            batch_size,
            values: VariableValues { values },
        }
    }

    pub fn merge<Other: Merge<BatchValues>>(&self, other: &Other) -> Other {
        other.merge(self)
    }
}

pub struct InputOutputSampleBatch {
    pub inputs: BatchValues,
    pub outputs: BatchValues,
}

impl InputOutputSampleBatch {
    pub fn variable_values_including_observed_outputs(&self) -> BatchValues {
        let mut result = (**self.inputs).clone();
        result.extend(
            self.outputs
                .iter()
                .map(|(id, value)| (loss_graph_observed_output_variable_id(id), value.clone())),
        );
        BatchValues::new(result)
    }
}

pub fn loss_output_id() -> OutputId {
    "loss".to_owned()
}
pub fn loss_graph_observed_output_variable_id(output_id: impl Into<OutputId>) -> VariableId {
    format!("observed_{}", output_id.into())
}
