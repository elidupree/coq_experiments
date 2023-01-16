pub enum MetavariableKind {
    Term,
    HasType,
    SingleSubstitution,
}

pub enum TermConstructor {}

macro_rules! constructor {
    ($($a:tt)*) => {};
}

constructor! {}
