/*

Let's implement the Calculus of Constructions!

Basically, there's only one kind of things: Terms. Even typing is just a relationship between one term and another.

Terms are ideal mathematical objects, but as a concession to practicality, we must describe a memory representation for them. As a concession to "EliDupree loves engineering", this memory representation will be optimized.

A Term is represented as a slice of bytes. Large terms will be deduplicated and identified by their 128-bit hash; we are willing to assume these will not collide. (If we later use this system in a way that accepts malicious inputs, this is worth revisiting to minimize the cryptographic guarantees we rely on; for now, I'm willing to ignore it.)

The term constructors are:
Type (note that I write Type instead of T because it is easier for speech-recognition, but perhaps also for readability to a programmer rather than a mathematician)
Prop
Variable (De Bruijn index)
Apply (Term, Term)
Lambda (Term, Term)
ForAll (Term, Term)

So the requirements for the representation are a discriminant (choice among these 6 options), the ability to recursively reference 2 other terms, and a representation of De Bruijn indices (hereafter "variable indices" because that's easier for speech recognition; if I later polish this documentation, I will convert it to use the proper name.)

For representing subterms, any Term < 32 bytes shall be embedded, and any other Term shall be referenced by its hash.

The values of the first byte of a Term are defined as follows:
00111110 = Prop
00111111 = Type
00VVVVVV = Variable
01XXXXXY = Lambda
10XXXXXY = ForAll
11XXXXXY = Apply


Each XXXXX describes the length of the first subterm, as follows:
00000 = represented by a 16 byte hash
ZZZZZ = embedded, with length ZZZZZ

Each Y describes the second subterm, as follows:
0 = represented by a 16 byte hash
1 = embedded (the length is known implicitly, since you are expected to know the length of the outer term when you refer to it as a slice)

VVVVVV is the top 6 bits of the (0-indexed) variable index. If the present term is longer than 1 byte, remaining bytes are also included in the value.

 */

use arrayvec::ArrayVec;
use bitmatch::bitmatch;
use serde::{Deserialize, Serialize};
use siphasher::sip128::{Hasher128, SipHasher};
use std::cell::RefCell;
use std::collections::HashMap;
use std::default::default;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Serialize, Deserialize, Debug)]
pub enum RecursiveTermKind {
    Lambda,
    ForAll,
    Apply,
}

/// Might be more proper to call this "TermConstructor" in the sense of the 6 constructors of Term,
/// but I currently feel better about this more English-like name: you ask "what kind of term is it?"
/// and I tell you a "kind of term", i.e. TermKind.
///
/// Actually I've added the value to the Variable variant, making this more into "1 layer of term"
/// rather than a "kind" of term. better rename it later

pub enum TermKind<'a> {
    Prop,
    Type,
    Variable(u64),
    Recursive(RecursiveTermKind, [SubTerm<'a>; 2]),
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum SubTerm<'a> {
    Embedded(TermRef<'a>),
    Reference(TermId),
}

fn sub_terms(x: u8, y: u8, rest: &[u8]) -> [SubTerm; 2] {
    let (first, first_length) = match x {
        0 => (
            SubTerm::Reference(TermId(u128::from_le_bytes(rest[0..16].try_into().unwrap()))),
            16,
        ),
        length => {
            let length = usize::from(length);
            (SubTerm::Embedded(TermRef(&rest[0..length])), length)
        }
    };
    let second_bytes = &rest[first_length..];
    let second = match y {
        0 => {
            assert_eq!(second_bytes.len(), 16);
            SubTerm::Reference(TermId(u128::from_le_bytes(
                second_bytes.try_into().unwrap(),
            )))
        }
        _ => SubTerm::Embedded(TermRef(second_bytes)),
    };
    [first, second]
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TermRef<'a>(&'a [u8]);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct TermArrayVec(ArrayVec<u8, 63>);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Term(TermArrayVec);

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TermId(u128);

pub const PROP: TermRef<'static> = TermRef(&[0b00111110]);
pub const TYPE: TermRef<'static> = TermRef(&[0b00111111]);

impl<'a> TermRef<'a> {
    #[bitmatch]
    pub fn kind(self) -> TermKind<'a> {
        use RecursiveTermKind::*;
        use TermKind::*;
        let (&first, rest) = self.0.split_first().unwrap();
        #[bitmatch]
        match first {
            "00111110" => Prop,
            "00111111" => Type,
            "00??????" => {
                let mut result = 0;
                for &byte in self.0.iter() {
                    result <<= 8;
                    result += u64::from(byte);
                }
                Variable(result)
            }
            "01xxxxxy" => Recursive(Lambda, sub_terms(x, y, rest)),
            "10xxxxxy" => Recursive(ForAll, sub_terms(x, y, rest)),
            "11xxxxxy" => Recursive(Apply, sub_terms(x, y, rest)),
        }
    }
    fn id(self) -> TermId {
        let mut hasher = SipHasher::new_with_keys(0xf9b1a3338349fa34, 0x24aa9b72e6020897);
        self.0.hash(&mut hasher);
        TermId(hasher.finish128().as_u128())
    }
    pub fn to_term_array_vec(&self) -> TermArrayVec {
        TermArrayVec(self.0.iter().copied().collect())
    }
    pub fn to_owned(&self) -> Term {
        Term(self.to_term_array_vec())
    }
    pub fn display(self, options: FormatTermOptions) -> DisplayTerm<'a> {
        DisplayTerm {
            term: self,
            options,
        }
    }
}

impl<'a> Display for TermRef<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.display(default()).fmt(f)
    }
}

impl TermId {
    pub fn get_term(self) -> Term {
        CURRENT_ENVIRONMENT
            .with(|environment| environment.borrow_mut().get_term(self).unwrap().to_owned())
    }
}

impl<'a> SubTerm<'a> {
    pub fn get(self) -> Term {
        match self {
            SubTerm::Embedded(t) => t.to_owned(),
            SubTerm::Reference(id) => id.get_term(),
        }
    }
}

impl TermArrayVec {
    pub fn variable(index: u64) -> Self {
        let mut result = ArrayVec::new();
        let mut partially_digested_index = index;
        while partially_digested_index > 61 {
            result.push(partially_digested_index as u8);
            partially_digested_index >>= 8;
        }
        result.push(partially_digested_index as u8);
        TermArrayVec(result)
    }
    pub fn as_term_ref(&self) -> TermRef {
        TermRef(&self.0[..])
    }
}

impl Term {
    pub fn prop() -> Self {
        Term(PROP.to_term_array_vec())
    }
    pub fn t() -> Self {
        Term(TYPE.to_term_array_vec())
    }
    pub fn variable(index: u64) -> Self {
        Term(TermArrayVec::variable(index))
    }
    pub fn recursive(kind: RecursiveTermKind, sub_terms: [TermRef; 2]) -> Self {
        Term(CURRENT_ENVIRONMENT.with(|environment| {
            environment
                .borrow_mut()
                .make_recursive_term(kind, sub_terms)
        }))
    }
    pub fn as_term_ref(&self) -> TermRef {
        self.0.as_term_ref()
    }
    pub fn kind(&self) -> TermKind {
        self.as_term_ref().kind()
    }
    pub fn display(&self, options: FormatTermOptions) -> DisplayTerm {
        self.as_term_ref().display(options)
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.display(default()).fmt(f)
    }
}

#[derive(Default)]
pub struct TermEnvironment {
    long_term_data: Vec<u8>,
    long_term_start_indices: HashMap<TermId, usize>,
}

thread_local! {
    static CURRENT_ENVIRONMENT: RefCell<TermEnvironment> =RefCell:: new (TermEnvironment::default());
}

#[derive(Clone)]
pub struct FormatTermOptions {
    pub depth: usize,
    pub parens_if_recursive: bool,
}

impl Default for FormatTermOptions {
    fn default() -> Self {
        FormatTermOptions {
            depth: 5,
            parens_if_recursive: false,
        }
    }
}

pub struct DisplayTerm<'a> {
    term: TermRef<'a>,
    options: FormatTermOptions,
}

impl Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        CURRENT_ENVIRONMENT.with(|environment| {
            environment
                .borrow()
                .format_term(f, &self.options, self.term)
        })
    }
}

impl TermEnvironment {
    pub fn new() -> Self {
        Self::default()
    }
    fn record_long_term(&mut self, id: TermId, term: TermRef) {
        self.long_term_start_indices.entry(id).or_insert_with(|| {
            let start = self.long_term_data.len();
            self.long_term_data.push(term.0.len().try_into().unwrap());
            self.long_term_data.extend_from_slice(term.0);
            start
        });
    }
    #[bitmatch]
    pub fn make_recursive_term(
        &mut self,
        kind: RecursiveTermKind,
        sub_terms: [TermRef; 2],
    ) -> TermArrayVec {
        let [first, second] = sub_terms;
        let mut result = ArrayVec::new();
        result.push(0);

        let h = match kind {
            RecursiveTermKind::Lambda => 0b01,
            RecursiveTermKind::ForAll => 0b10,
            RecursiveTermKind::Apply => 0b11,
        };
        let x = if first.0.len() >= 31 {
            let id = first.id();
            self.record_long_term(id, first);
            result.extend(id.0.to_le_bytes());
            0
        } else {
            result.extend(first.0.iter().copied());
            u8::try_from(first.0.len()).unwrap()
        };
        let y = if second.0.len() >= 31 {
            let id = second.id();
            self.record_long_term(id, second);
            result.extend(id.0.to_le_bytes());
            0
        } else {
            result.extend(second.0.iter().copied());
            u8::try_from(second.0.len()).unwrap()
        };

        result[0] = bitpack!("hhxxxxxy");
        TermArrayVec(result)
    }
    pub fn get_term(&self, id: TermId) -> Option<TermRef> {
        let index = *self.long_term_start_indices.get(&id)?;
        let length = usize::from(self.long_term_data[index]);
        Some(TermRef(&self.long_term_data[index + 1..index + 1 + length]))
    }
    pub fn get_sub_term<'a>(&'a self, sub_term: SubTerm<'a>) -> Option<TermRef<'a>> {
        match sub_term {
            SubTerm::Embedded(term) => Some(term),
            SubTerm::Reference(id) => self.get_term(id),
        }
    }
    fn format_term(
        &self,
        f: &mut Formatter,
        options: &FormatTermOptions,
        term: TermRef,
    ) -> Result<(), fmt::Error> {
        use RecursiveTermKind::*;
        if options.depth == 0 {
            return Ok(());
        }
        match term.kind() {
            TermKind::Prop => f.write_str("P"),
            TermKind::Type => f.write_str("T"),
            TermKind::Variable(index) => {
                write!(f, "{}", index)
            }
            TermKind::Recursive(kind, children) => {
                if options.parens_if_recursive {
                    f.write_str("(")?
                }
                match kind {
                    Lambda => f.write_str("λ")?,
                    ForAll => f.write_str("∀")?,
                    Apply => {}
                };
                let [a, b] = children.map(|c| self.get_sub_term(c).unwrap());
                let child_options = FormatTermOptions {
                    parens_if_recursive: true,
                    depth: options.depth - 1,
                    //..*options
                };
                self.format_term(f, &child_options, a)?;
                if kind == Apply {
                    f.write_str(" ")?;
                } else {
                    f.write_str(",")?;
                }
                self.format_term(f, &child_options, b)?;
                if options.parens_if_recursive {
                    f.write_str(")")?
                }
                Ok(())
            }
        }
    }
}

/// Something that can be computed about terms recursively, based on the values in the subterms.
pub trait TermAugmentationCore: Clone {
    fn of_prop() -> Self;
    fn of_type() -> Self;
    fn of_variable(index: u64) -> Self;
    fn of_recursive_term(kind: RecursiveTermKind, children: [&Self; 2]) -> Self;
    fn with_cache<R>(callback: impl FnOnce(&mut TermAugmentationCache<Self>) -> R) -> R;
}

pub trait TermAugmentation {
    fn of(term: TermRef) -> Self;
}

impl<T: TermAugmentationCore> TermAugmentation for T {
    fn of(term: TermRef) -> Self {
        fn of_impl<S: TermAugmentationCore>(
            term: TermRef,
            cache: &mut TermAugmentationCache<S>,
        ) -> S {
            match term.kind() {
                TermKind::Prop => S::of_prop(),
                TermKind::Type => S::of_type(),
                TermKind::Variable(index) => S::of_variable(index),
                TermKind::Recursive(kind, children) => {
                    let children = children.map(|c| match c {
                        SubTerm::Embedded(s) => of_impl(s, cache),
                        SubTerm::Reference(id) => match cache.values.get(&id) {
                            Some(preexisting) => preexisting.clone(),
                            None => {
                                let term = id.get_term();
                                let result = of_impl(term.as_term_ref(), cache);
                                cache.values.insert(id, result.clone());
                                result
                            }
                        },
                    });
                    S::of_recursive_term(kind, children.each_ref())
                }
            }
        }
        Self::with_cache(|cache| of_impl::<Self>(term, cache))
    }
}

pub struct TermAugmentationCache<T> {
    values: HashMap<TermId, T>,
}

impl<T> Default for TermAugmentationCache<T> {
    fn default() -> Self {
        TermAugmentationCache { values: default() }
    }
}

#[derive(Clone, Debug)]
pub struct TermCheapInfo {
    height: u64,
    naive_size: u64,
    low_free_variable_indices: u64,
}

impl TermAugmentationCore for TermCheapInfo {
    fn of_prop() -> Self {
        TermCheapInfo {
            height: 0,
            naive_size: 1,
            low_free_variable_indices: 0,
        }
    }

    fn of_type() -> Self {
        Self::of_prop()
    }

    fn of_variable(index: u64) -> Self {
        TermCheapInfo {
            height: 0,
            naive_size: 1,
            low_free_variable_indices: 1 << index,
        }
    }

    fn of_recursive_term(kind: RecursiveTermKind, children: [&Self; 2]) -> Self {
        let mut low_free_variable_indices = children[0].low_free_variable_indices;
        if kind == RecursiveTermKind::Apply {
            low_free_variable_indices |= children[1].low_free_variable_indices;
        } else {
            low_free_variable_indices |= children[1].low_free_variable_indices >> 1;
        }
        TermCheapInfo {
            height: 1 + children.iter().map(|c| c.height).max().unwrap(),
            naive_size: 1u64
                .saturating_add(children[0].naive_size)
                .saturating_add(children[1].naive_size),
            low_free_variable_indices,
        }
    }

    fn with_cache<R>(callback: impl FnOnce(&mut TermAugmentationCache<Self>) -> R) -> R {
        thread_local! {
            static CACHE: RefCell<TermAugmentationCache<TermCheapInfo>> =RefCell:: new (TermAugmentationCache::default());
        }
        CACHE.with(|c| callback(&mut c.borrow_mut()))
    }
}
