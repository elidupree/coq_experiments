(* Just an example file for me to test my proof explorer with. *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Classes.SetoidDec.
Require Import Lists.SetoidList.
Require Import Nat.
 
Require Import Coq.Program.Equality.
Lemma NoDupA_head : ∀ (A : Type) (eqA : A -> A -> Prop) (x : A) (l : list A), NoDupA eqA (x::l) → ¬ InA eqA x l.

