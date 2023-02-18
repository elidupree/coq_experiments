use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;

#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default, Debug,
)]
pub struct EntityId(pub u128);
pub struct QueryKind {
    pub index: usize,
    pub input_entities: usize,
    pub output_entities: usize,
    pub output_numbers: usize,
}
pub struct Query<Name> {
    pub kind: QueryKind,
    pub input_entities: Vec<(EntityId, Name)>,
    pub output_entities: Vec<EntityId>,
}
pub struct QueryResult<Name> {
    pub output_entities: Vec<Name>,
    pub output_numbers: Vec<f32>,
}
pub struct TrainingQuery<Name> {
    pub query: Query<Name>,
    pub given_result: QueryResult<Name>,
    pub target_output_numbers: Vec<f32>,
}

pub trait Predictor: Clone + Serialize + DeserializeOwned + Debug {
    type Name;
    fn new(query_kinds: &[QueryKind]) -> Self;
    fn query(&self, query: &Query<Self::Name>) -> QueryResult<Self::Name>;
    fn train(&mut self, queries: &[TrainingQuery<Self::Name>]);
}

pub struct EntityConstructorDefinition {
    pub index: usize,
    pub arguments: usize,
}

pub struct EntityConstructor {
    pub definition: EntityConstructorDefinition,
    pub arguments: Vec<EntityId>,
}

pub struct ChoiceKind {
    pub index: usize,
    pub num_choices: usize,
}

pub trait Entity {
    fn constructor(&self) -> EntityConstructor;
}

pub trait SearchPosition: Entity {
    type SearchResult;
    fn entity_constructors() -> Vec<EntityConstructor>;
    fn choice_kind(&self) -> ChoiceKind;
    fn next_state(&self, move_index: usize) -> Self;
    fn as_result(&self) -> Option<Self::SearchResult>;
}

pub trait SearchRunner<Position: SearchPosition, Model: Predictor> {
    fn new(start: Position, model: Model) -> Self;
    fn step(&mut self);
    fn result(&self) -> Option<Position::SearchResult>;
    fn training_data(&self) -> Vec<TrainingQuery<Model::Name>>;
}
