use crate::{CapsuleContents, HashCapsule, HashCapsuleInner};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::marker::PhantomData;
use std::path::Path;
use std::sync::Arc;
use std::{io, mem};

// struct ObjectSerializationInfo {
//     serial_number: usize,
//     state: ObjectSerializationState,
// }
// enum ObjectSerializationState {
//     WaitingToSerialize,
//     SerializingOrWaitingToBeStored,
//     Stored,
// }
//
// struct SerializationContext {
//     next_serial_number: usize,
//     objects_info: HashMap<*const (), ObjectSerializationInfo>,
//     stored_objects: Vec<serde_json::Value>,
// }
//

#[derive(Default)]
struct SerializationContext {
    // index by object memory addresses rather than hashes, because this is a heterogeneous collection and I don't guarantee that objects of different types have different hashes
    serial_numbers_by_object: HashMap<usize, u64>,
    stored_objects: Vec<Option<serde_json::Value>>,
}

// struct ObjectDeserializationInfo {
//     state: ObjectDeserializationState,
// }
#[derive(Clone)]
enum ObjectDeserializationState {
    UnknownType(serde_json::Value),
    AlreadyDeserialized(Arc<dyn Any>),
}
#[derive(Default)]
struct DeserializationContext {
    objects: Vec<ObjectDeserializationState>,
}

fn with_serialization_context<R>(callback: impl FnOnce(&mut SerializationContext) -> R) -> R {
    thread_local! {
        static CONTEXT: RefCell<SerializationContext> = RefCell::new(SerializationContext::default());
    }
    CONTEXT.with(|context| callback(&mut context.borrow_mut()))
}

fn with_deserialization_context<R>(callback: impl FnOnce(&mut DeserializationContext) -> R) -> R {
    thread_local! {
        static CONTEXT: RefCell<DeserializationContext> = RefCell::new(DeserializationContext::default());
    }
    CONTEXT.with(|context| callback(&mut context.borrow_mut()))
}

impl<T: CapsuleContents + Serialize> Serialize for HashCapsule<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let (serial_number, already_serialized) = with_serialization_context(|context| {
            let serial_number = *context
                .serial_numbers_by_object
                .entry(&**self as *const HashCapsuleInner<T> as *const () as usize)
                .or_insert_with(|| {
                    let result = context.stored_objects.len() as u64;
                    context.stored_objects.push(None);
                    result
                });
            (
                serial_number,
                context.stored_objects[serial_number as usize].is_some(),
            )
        });
        if !already_serialized {
            use serde::ser::Error;
            let contents = (**self)
                .serialize(serde_json::value::Serializer)
                .map_err(Error::custom)?;
            with_serialization_context(|context| {
                context.stored_objects[serial_number as usize] = Some(contents);
            })
        }
        serial_number.serialize(serializer)
    }
}
impl<'de, T: CapsuleContents + DeserializeOwned> Deserialize<'de> for HashCapsule<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let serial_number = u64::deserialize(deserializer)?;

        let state: ObjectDeserializationState =
            with_deserialization_context(|context| context.objects[serial_number as usize].clone());

        Ok(match state {
            ObjectDeserializationState::AlreadyDeserialized(pointer) => {
                (*pointer.downcast_ref::<HashCapsule<T>>().unwrap()).clone()
            }
            ObjectDeserializationState::UnknownType(object) => {
                use serde::de::Error;
                // eprintln!(
                //     "hmm {serial_number} {} {object}",
                //     std::any::type_name::<T>()
                // );
                let result: T = serde_json::from_value(object).map_err(Error::custom)?;
                let result = HashCapsule::new(result);
                with_deserialization_context(|context| {
                    context.objects[serial_number as usize] =
                        ObjectDeserializationState::AlreadyDeserialized(Arc::new(result.clone()));
                });
                result
            }
        })
    }
}

#[derive(Serialize, Deserialize)]
pub struct SerializedWithHashCapsules<T> {
    pub value: T,
    pub capsule_data: Vec<serde_json::Value>,
}

impl<T> SerializedWithHashCapsules<T> {
    pub fn new(value_maker: impl FnOnce() -> T) -> Self {
        with_serialization_context(|context| {
            *context = SerializationContext::default();
        });
        let value = value_maker();
        let capsule_data = with_serialization_context(|context| {
            context.stored_objects.drain(..).flatten().collect()
        });
        SerializedWithHashCapsules {
            value,
            capsule_data,
        }
    }
    pub fn consume<R>(self, value_consumer: impl FnOnce(T) -> R) -> R {
        let objects = self
            .capsule_data
            .into_iter()
            .map(ObjectDeserializationState::UnknownType)
            .collect();
        with_deserialization_context(move |context| {
            *context = DeserializationContext { objects };
        });
        value_consumer(self.value)
    }
}

#[derive(Serialize, Deserialize)]
pub enum StorageLine {
    HashCapsuleContents(serde_json::Value),
    UserValue(serde_json::Value),
}

#[derive(Serialize)]
pub enum StorageLineRef<'a> {
    HashCapsuleContents(&'a serde_json::Value),
    UserValue(serde_json::Value),
}

pub struct IncrementalSerializer<T> {
    capsules_stored: usize,
    context: SerializationContext,
    _marker: PhantomData<fn(&T)>,
}

impl<T> Default for IncrementalSerializer<T> {
    fn default() -> Self {
        IncrementalSerializer {
            capsules_stored: 0,
            context: Default::default(),
            _marker: Default::default(),
        }
    }
}

impl<T: Serialize> IncrementalSerializer<T> {
    pub fn store(&mut self, value: &T, writer: &mut impl io::Write) -> Result<(), anyhow::Error> {
        with_serialization_context(|context| {
            *context = mem::take(&mut self.context);
        });
        let v = serde_json::to_value(value)?;
        with_serialization_context(|context| {
            self.context = mem::take(context);
        });
        for capsule_contents in &self.context.stored_objects[self.capsules_stored..] {
            serde_json::to_writer(
                &mut *writer,
                &StorageLineRef::HashCapsuleContents(
                    capsule_contents.as_ref().expect(
                        "by the time you finish serializing, the stack should have resolved",
                    ),
                ),
            )?;
            writeln!(&mut *writer)?;
        }
        self.capsules_stored = self.context.stored_objects.len();
        serde_json::to_writer(&mut *writer, &StorageLine::UserValue(v))?;
        writeln!(&mut *writer)?;
        Ok(())
    }
}

pub fn deserialize_with_hash_capsules<T: DeserializeOwned>(
    mut lines: impl Iterator<Item = Result<StorageLine, anyhow::Error>>,
) -> impl Iterator<Item = Result<T, anyhow::Error>> {
    let mut context = DeserializationContext::default();
    std::iter::from_fn(move || loop {
        let line = match lines.next()? {
            Ok(line) => line,
            Err(e) => return Some(Err(e)),
        };
        match line {
            StorageLine::HashCapsuleContents(value) => {
                context
                    .objects
                    .push(ObjectDeserializationState::UnknownType(value));
            }
            StorageLine::UserValue(value) => {
                with_deserialization_context(|c| {
                    *c = mem::take(&mut context);
                });
                // eprintln!("{}", value);
                let result = serde_json::from_value(value);
                with_deserialization_context(|c| {
                    context = mem::take(c);
                });
                return Some(result.map_err(Into::into));
            }
        }
    })
}

pub fn deserialize_file_with_hash_capsules<T: DeserializeOwned>(
    path: impl AsRef<Path>,
) -> Result<impl Iterator<Item = Result<T, anyhow::Error>>, anyhow::Error> {
    Ok(deserialize_with_hash_capsules(
        BufReader::new(File::open(path)?)
            .lines()
            .map(|l| Ok(serde_json::from_str(&l?)?)),
    ))
}
