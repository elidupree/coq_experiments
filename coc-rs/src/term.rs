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

use std::collections::HashMap;
use std::hash::Hash;
use std::num::NonZeroU8;
use arrayvec::ArrayVec;
use bitmatch::bitmatch;
use siphasher::sip128::{Hasher128, SipHasher};

/// Might be more proper to call this "TermConstructor" in the sense of the 6 constructors of Term,
/// but I currently feel better about this more English-like name: you ask "what kind of term is it?"
/// and I tell you a "kind of term", i.e. TermKind.
///
/// Actually I've added the value to the Variable variant, making this more into "1 layer of term"
/// rather than a "kind" of term. better rename it later
pub enum TermKind<'a> { Prop, Type, Variable(u64), Lambda([SubTerm<'a>; 2]), ForAll([SubTerm<'a>; 2]), Apply([SubTerm<'a>; 2]) }

pub enum SubTerm<'a> { Embedded(TermRef<'a>), Reference(TermId) }

fn sub_terms(x: u8, y: u8, rest: &[u8]) -> [SubTerm; 2] {
    let (first, first_length) = match x {
        0 => (SubTerm::Reference(TermId(u128::from_le_bytes(rest[0..16].try_into().unwrap()))), 16),
        length => {
            let length = usize::from(length);
            (SubTerm::Embedded(TermRef(&rest[0..length])), length)
        }
    };
    let second_bytes = &rest[first_length..];
    let second = match y {
        0 => {
            assert_eq!(second_bytes.len(), 16);
            SubTerm::Reference(TermId(u128::from_le_bytes(second_bytes.try_into().unwrap())))
        }
        _ => SubTerm::Embedded(TermRef(second_bytes))
    };
    [first, second]
}

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TermRef<'a> (&'a [u8]);

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TermArrayVec(ArrayVec<u8, 33>);

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TermId(u128);

pub const PROP: TermRef<'static> = TermRef(&[0b00111110]);
pub const TYPE: TermRef<'static> = TermRef(&[0b00111111]);

impl<'a> TermRef<'a> {
    #[bitmatch]
    pub fn kind(self) -> TermKind<'a> {
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
            "01xxxxxy" => Lambda(sub_terms(x, y, rest)),
            "10xxxxxy" => ForAll(sub_terms(x, y, rest)),
            "11xxxxxy" => Apply(sub_terms(x, y, rest)),
        }
    }
    fn id(self) -> TermId {
        let mut hasher = SipHasher::new_with_keys(0xf9b1a3338349fa34, 0x24aa9b72e6020897);
        self.0.hash(&mut hasher);
        TermId(hasher.finish128().as_u128())
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

pub struct TermEnvironment {
    long_term_data: Vec<u8>,
    long_term_start_indices: HashMap<TermId, usize>,
}

impl TermEnvironment {
    fn record_long_term(&mut self, term: TermRef) {
        self.long_term_start_indices.entry(term.id()).or_insert_with(|| {
            let start = self.long_term_data.len();
            self.long_term_data.push(term.0.len().try_into().unwrap());
            self.long_term_data.extend_from_slice(term.0);
            start
        });
    }
    pub fn get_term(&self, id: TermId) -> Option<TermRef> {
        let index = *self.long_term_start_indices.get(&id)?;
        let length = usize::from(self.long_term_data[index]);
        Some(TermRef(&self.long_term_data[index + 1..index + 1 + length]))
    }
    pub fn get_sub_term<'a>(&'a self, sub_term: SubTerm<'a>) -> Option<TermRef<'a>> {
        match sub_term {
            SubTerm::Embedded(term) => { Some(term) }
            SubTerm::Reference(id) => { self.get_term(id) }
        }
    }
}
