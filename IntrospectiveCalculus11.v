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
Notation "P '∩' Q" := (λ x, P x ∧ Q x) (at level 80, right associativity) : type_scope.
Notation "P '∪' Q" := (λ x, P x ∨ Q x) (at level 85, right associativity) : type_scope.
Notation "P '≡' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity) : type_scope.
Notation "P '≡2' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.


Definition LSet := Location -> Prop.
Definition LSSet := LSet -> Prop.
Definition LRel := Location -> Location -> Prop.

Inductive AssertedRewrites (S : LSet) : Location -> Location -> Prop :=
  | rewrites x y z : S x -> S y -> AssertedRewrites S (x++z) (y++z).

Definition ARewritesRespectB A B :=
  ∀ x y, (AssertedRewrites A) x y -> B x -> B y.


  (* λ x y, ∀ z w, S (x++z) -> S (y++z). *)
Search (∀ S, (S -> S) -> (S -> Prop) -> (S -> Prop)).
Definition PrefixRewrites (S : LSet) : Location -> Location -> Prop :=
  λ x y, ∀ z w, S (x++z) -> S (y++z).


Inductive SubtreeMap (S : LSet) (d : Location) : LSet :=
  | sm_cons x : S x -> SubtreeMap S d (x++d). 

Infix "++₁" := SubtreeMap (right associativity, at level 60).

Definition UnifiableAssuming (Indep : LSSet) (x y : Location)
  := ∀   S   e,   Indep   S -> ( S      (x++e) <->  S      (y++e)).
Definition Unifiable (Indep : LSSet) (x y : Location)
  := ∀   S d e,   Indep   S -> ((S++₁d) (x++e) <-> (S++₁d) (y++e)).
Definition UnifiableSet (Indep : LSSet) (U : LSet)
  := ∀ S x y d e, Indep   S -> U x -> U y -> (S++₁d) (x++e) -> (S++₁d) (y++e).

Definition IndepAbleAssuming (Unified : LRel) (S : LSet)
  := ∀ x y f  , Unified x y ->  (S++₁f)  x ->     (S++₁f)  y.
Definition IndepAble (Unified : LRel) (S : LSet)
  := ∀ x y f g, Unified x y ->  (S++₁f) (x++g) -> (S++₁f) (y++g).
Definition IndepAbleWithSets (Unif : LSSet) (S : LSet)
  := ∀ U x y f g, Unif U  -> U x -> U y -> (S++₁f) (x++g) -> (S++₁f) (y++g).

Definition IndepSetPermitsUnifyingSet (S U : LSet)
  := ∀ x y d e, U x -> U y -> (S++₁d) (x++e) -> (S++₁d) (y++e).
Definition UnifiableAllSetVersion (Indep : LSSet) (U : LSet)
  := ∀ S, Indep S -> IndepSetPermitsUnifyingSet S U.
Definition IndepAbleAllSetVersion (Unif : LSSet) (S : LSet)
  := ∀ U, Unif U -> IndepSetPermitsUnifyingSet S U.

  
Definition IndepSetPermitsUnifyingSetUnrolled (S U : LSet)
  := ∀ x y z d e, U x -> U y -> S z -> (z++d) = (x++e) -> ∃ w, S w ∧ (w++d) = (y++e).

Class IndepSets (Indep : LSSet) := {
  _ : Indep ≡ IndepAble (Unifiable Indep)
}.

Class UnifRel (Unified : LRel) := {
  _ : Unified ≡2 Unifiable (IndepAble Unified)
}.