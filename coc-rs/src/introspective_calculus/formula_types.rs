// use crate::introspective_calculus::Atom;
// use hash_capsule::HashCapsule;
//
// pub struct Equivalence<F> {
//     sides: [F; 2],
// }
//
// pub trait Represents<T> {
//     fn make_represented(&self) -> T;
// }
// pub trait MakeApply {
//     fn make_apply(children: [WithCaches<Self>; 2]) -> Self;
// }
//
// pub trait MakeEquals {
//     fn make_equals(&self, other: &Self) -> Self;
// }
//
// impl<T: From<Atom> + MakeApply> MakeEquals for T {
//     default fn make_equals(&self, other: &Self) -> Self {
//         (Atom::Equals).into().make_apply(self).make_apply(other)
//     }
// }
//
// pub struct WithCachesInner<T, U> {
//     value: T,
//     represented: U,
// }
//
// pub struct WithCaches<T, U>(HashCapsule<WithCachesInner<T, U>>);
//
// impl<F> Represents<F> for Equivalence<F> {
//     fn make_represented(&self) -> F {
//         self.sides
//     }
// }
