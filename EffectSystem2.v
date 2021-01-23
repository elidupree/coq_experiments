(* Some attempts to build an effect system for my code generation *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Notation "x × y" := (prod x y) (at level 60, right associativity) : type_scope.
Require Import List.
Import EqNotations.
Require Import Coq.Program.Equality.

Definition Step State : Type := State → State → Prop.
Definition Partition P A B
  (SP : Step P) (SA : Step A) (SB : Step B)
  (MA : P → A) (MB : P → B)
  (p : P) : Prop :=
  ∀ n, SP p n →
    (SA (MA p) (MA n) ∧ MB p = MB n) 
    ∨
    (SB (MB p) (MB n) ∧ MA p = MA n).
    
Definition Isolate P C
  (SP : Step P) (SC : Step C)
  (M : P → C)
  (p : P) : Prop :=
  ∀ n, SP p n → SC (M p) (M n).

(* Inductive History A (SA : Step A) : list A → Prop :=
| HistoryInitial : ∀ initial , History SA (initial :: nil)
| HistoryStep : ∀ x y l, SA x y → History SA (x :: l) → History SA (y :: x :: l). *)

Inductive History A (SA : Step A) (initial : A) : ∀ final : A, Prop :=
| HistoryInitial : History SA initial initial
| HistoryStep : ∀ x y, SA x y → History SA initial x → History SA initial y.

(* Inductive IsolateHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) : list P → Prop :=
| IsolateHistoryInitial : ∀ initial , IsolateHistory SP SC M (initial :: nil)
| IsolateHistoryStep : ∀ x y l, SP x y → SC (M x) (M y) → IsolateHistory SP SC M (x :: l) → IsolateHistory SP SC M (y :: x :: l). *)

Inductive IsolateHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) : ∀ final : P, Prop :=
| IsolateHistoryInitial : IsolateHistory SP SC M initial initial
| IsolateHistoryStep : ∀ x y, SP x y → SC (M x) (M y) → IsolateHistory SP SC M initial x → IsolateHistory SP SC M initial y.

Lemma parentHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) (final : P) : IsolateHistory SP SC M initial final → History SP initial final.
  intros; induction H.
  constructor.
  apply (HistoryStep _ H); assumption.
Qed.

Lemma childHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) (final : P) : IsolateHistory SP SC M initial final → History SC (M initial) (M final).
  intros; induction H.
  constructor.
  apply (HistoryStep _ H0); assumption.
Qed.

(* Definition NonNullStep A (SA : Step A) : Step A := λ x y, SA x y ∧ x ≠ y. *)
Lemma RemoveNullSteps A (SA : Step A) (NonNullSA : Step A) (null_dec : ∀ x y : A, SA x y → NonNullSA x y ∨ x = y) i f : History SA i f → History NonNullSA i f.
  intros; induction H.
  constructor.
  destruct (null_dec x y H).
  exact (HistoryStep y H1 IHHistory).
  rewrite <- H1; assumption.
Qed.

Lemma NullStepsIrrelevant A (SA : Step A) (NonNullSA : Step A) (null_dec : ∀ x y : A, SA x y → NonNullSA x y ∨ x = y) (R : A → Prop) i : (∀ f, History NonNullSA i f → R f) → (∀ f, History SA i f → R f).
  intros; exact (H f (RemoveNullSteps NonNullSA null_dec H0)).
Qed.
  
