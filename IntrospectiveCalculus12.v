Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import List.
Require Import String.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(* Protect myself from accidental infinite loops during dev work *)
(* Set Typeclasses Iterative Deepening. *)
Set Typeclasses Depth 3.

(****************************************************
                 Proof bureaucracy
****************************************************)

(* When proving, there are a lot of simplification steps that I want to be applied automatically, with very little effort. As the definitions and lemmas proceed, I want to add more simplification steps to a hints database.

Unfortunately, the `auto` family of tactics, which apply hints from a database, cancel all the applications if you didn't solve the entire goal. That's not what I want. As a hack to work around this, it's possible to shelve an incomplete goal, and `auto` will interpret this as "success". So we just end every hint with `shelve`. *)

Ltac autouse_shelving_db steps db :=
  idtac steps; match steps with
    | S ?p => try ((progress (unshelve typeclasses eauto 99 with db));
      autouse_shelving_db p db)
    | _ => idtac "Warning: steps ran out"
  end.

Create HintDb simplify.
Ltac simplify := autouse_shelving_db 20 ident:(simplify).

(* We *do* want to apply intros if it helps simplify, but not if it doesn't, so don't shelve here. Also, since it's the second-choice and can duplicate work, make it high-cost. *)
(* Hint Extern 12 => intro; intros : simplify. *)

(* ...and if we *can* solve easily, might as well. *)
Hint Extern 1 => solve [trivial | constructor | discriminate] : simplify.

(* One notable simplification step is to rewrite equality hypotheses when one side is just another hypothesis. But it's kinda expensive, so we give it a high-ish cost. *)
Hint Extern 9 => progress match goal with
  | x : _ |- _ => match goal with
    | eq : x = _ |- _ => rewrite eq in *; clear x eq
    | eq : _ = x |- _ => rewrite <- eq in *; clear x eq
    end
  end; shelve
  : simplify.

(* `remember`, but not if it's redundant *)
Ltac dontforget term :=
  lazymatch term with
  | (_ _) => lazymatch goal with
    | _ : _ = term |- _ => idtac
    | _ : term = _ |- _ => idtac
    | _ => remember term
    end
  | _ => idtac 
  end.

(****************************************************
                   Tree structure
****************************************************)

Inductive WhichChild := wc_left | wc_right.
Definition Location := list WhichChild.
Bind Scope list_scope with Location.
Notation "'𝕃'" := wc_left.
Notation "'ℝ'" := wc_right.
Hint Extern 5 => progress change (list WhichChild) with Location in *; shelve : simplify.

Notation "P '⊆' Q" := (∀ x, P x -> Q x) (at level 70, no associativity) : type_scope.
Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '∩' Q" := (λ x, P x ∧ Q x) (at level 80, right associativity) : type_scope.
Notation "P '∩₂' Q" := (λ x y, P x y ∧ Q x y) (at level 80, right associativity) : type_scope.
Notation "P '∪' Q" := (λ x, P x ∨ Q x) (at level 85, right associativity) : type_scope.
Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 85, right associativity) : type_scope.
Notation "P '≡' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity) : type_scope.
Notation "P '≡₂' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.
(* Notation "'⋂' x .. y , P" := (∀ x, .. (∀ y, P) ..)
  (at level 200, x binder, y binder, right associativity).
Notation "'⋂₂' P" := (⋂ x y, P x y) (at level 200, right associativity). *)
Notation "'ThingsWhose' F ⊇₂ P" :=
  (λ S, P ⊆₂ (F S)) (at level 90).
Notation "'PairsWhose' F ⊇ P" :=
  (λ x y, P ⊆ (F x y)) (at level 90).

Definition LSet := Location -> Prop.
Definition LSSet := LSet -> Prop.
Definition LRel := Location -> Location -> Prop.

Inductive SubtreeMap (S : LSet) (d : Location) : LSet :=
  | sm_cons x : S x -> SubtreeMap S d (x++d). 

Infix "*++" := SubtreeMap (right associativity, at level 60).

(****************************************************
          Independent sets and conformances
****************************************************)

Section IndepsAndConformances.
  Definition IndepsOfConformance (x y : Location) : LSSet
    := λ I, ∀ (d e : Location), (I*++d) (x++e) -> (I*++d) (y++e).
  Definition ConformancesOfIndep (I : LSet) : LRel
    := λ x y, ∀ (d e : Location), IndepsOfConformance x y I.

  Definition IndepsOfConformances (C : LRel) : LSSet
    := ThingsWhose ConformancesOfIndep ⊇₂ C.
  Definition ConformancesOfIndeps (Indeps : LSSet) : LRel
    := PairsWhose IndepsOfConformance ⊇ Indeps.

  Definition IndepsOfIndeps (Indeps : LSSet) : LSSet
    := IndepsOfConformances (ConformancesOfIndeps Indeps).
  Definition ConformancesOfConformances (C : LRel) : LRel
    := ConformancesOfIndeps (IndepsOfConformances C).

  Definition IndepsComplete (Indeps : LSSet)
    := IndepsOfIndeps Indeps ⊆ Indeps.
  Definition ConformancesComplete (C : LRel)
    := ConformancesOfConformances C ⊆₂ C.

  Section Properties.
    Create HintDb iandc.
    Hint Unfold
      IndepsOfConformance IndepsOfConformances IndepsOfIndeps
      ConformancesOfIndep ConformancesOfIndeps ConformancesOfConformances : iandc.
    (* Hint Extern 6 => intro : intro_harder. *)
    Lemma IndepsOfIndeps_Positive Indeps
      : Indeps ⊆ IndepsOfIndeps Indeps.
      (* debug auto with iandc. *)
      intros I II. intros x y Cxy x2 y2.
      apply Cxy; assumption.
    Qed.
    Lemma ConformancesOfConformances_Positive C
      : C ⊆₂ ConformancesOfConformances C.
      intros x y Cxy. intros I II.
      apply II; assumption.
    Qed.
    Lemma IndepsOfConformances_Complete C
      : IndepsComplete (IndepsOfConformances C).
      intros I II. intros x y CI.
      apply II. apply ConformancesOfConformances_Positive; assumption.
    Qed.
    Lemma ConformancesOfIndeps_Complete Indeps
      : ConformancesComplete (ConformancesOfIndeps Indeps).
      intros x y Cxy. intros I II.
      apply Cxy. apply IndepsOfIndeps_Positive; assumption.
    Qed.
    Lemma Indeps_Intersection_Complete As Bs :
      IndepsComplete As -> IndepsComplete Bs ->
      IndepsComplete (As ∩ Bs).
      intros ICA ICB I II.
      split; [apply ICA|apply ICB];
        intros x y Cxy;
        apply II;
        intros I2 (AI2, BI2);
        apply Cxy; assumption.
    Qed.
    Lemma Conformances_Intersection_Complete As Bs :
      ConformancesComplete As -> ConformancesComplete Bs ->
      ConformancesComplete (As ∩₂ Bs).
      intros CCA CCB x y Cxy.
      split; [apply CCA|apply CCB];
        intros I II;
        apply Cxy;
        intros x2 y2 (Axy2, Bxy2);
        apply II; assumption.
    Qed.
  End Properties.
End IndepsAndConformances.


(****************************************************
          Concrete constructors of indeps
****************************************************)
Section ConcreteIndeps.
  Definition Indeps_LL_RL : LSSet := IndepsOfConformance (𝕃::𝕃::nil) (ℝ::𝕃::nil).
  Definition Indeps_LR_RRL : LSSet := IndepsOfConformance (𝕃::ℝ::nil) (ℝ::ℝ::𝕃::nil).
  Definition Indeps_LR_RRR : LSSet := IndepsOfConformance (𝕃::ℝ::nil) (ℝ::ℝ::ℝ::nil).
  
  Definition IndepsOfPushedConformance c x y
  := IndepsOfConformance (c::x) (c::y).
  Definition PushedConformancesOfIndeps c (Indeps : LSSet) : LRel
    := PairsWhose (IndepsOfPushedConformance c) ⊇ Indeps.
  Definition IndepsPush c Indeps : LSSet :=
    IndepsOfConformances (PushedConformancesOfIndeps c Indeps).
  
  Definition PulledSet c (S : LSet) : LSet := λ x, S (c::x).
  Definition ConformancesOfPulledIndep c (I : LSet) : LRel
    := ConformancesOfIndep (PulledSet c I).
  Definition PulledIndepsOfConformances c (C : LRel) : LSSet
    := ThingsWhose (ConformancesOfPulledIndep c) ⊇₂ C.
  Definition IndepsPull c Indeps : LSSet :=
    PulledIndepsOfConformances c (ConformancesOfIndeps Indeps).

  
End ConcreteIndeps.
  

  