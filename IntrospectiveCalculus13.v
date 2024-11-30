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

(****************************************************
                   ContextSet
****************************************************)

Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '≡₂' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.

Definition Context M := Location -> M -> Prop.
Definition ContextSet := ∀ M, Context M -> Prop.
(* Definition ContextHasSubtreeAt M (x : Location) (C S : Context M) : Prop
  := ∀ d m, S d m -> C (x++d) m. *)
  
(* Definition ContextSet_Positive (Cs : ContextSet) :=
  ∀ M C1 C2, C1 ⊆₂ C2 -> Cs M C1 -> ∃ C3, C2 ⊆₂ C3 ∧ Cs M C3. *)
Definition ContextSet_Extensional (Cs : ContextSet) :=
  ∀ M C1 C2, C1 ≡₂ C2 -> Cs M C1 -> Cs M C2. 
Definition MeaningsCanContainOtherMeanings (Cs : ContextSet) :=
  ∀ M C1 C2 (Submeanings : M -> Context M),
    C2 ≡₂ (λ x m, ∀ C3, C3 ⊆₂ C2 -> (MeaningsAgree Submeanings C3) -> C3 x m) ->
    Cs M C1 ->
    Cs M C2
    (* (λ)
    Cs M C1 ->
    ∃ C2, Cs M C2 ∧
      C1 ⊆₂ C2 ∧
      ∀ x d m n, Submeanings m d n ->
        C2 x m -> C2 (x++d) n *)
        .
Definition ConformsTo x y (Cs : ContextSet) : Prop :=
  ∀ M (m : M) C, Cs M C -> C x m -> C y m.
Definition Independent (I : Location -> Prop) (Cs : ContextSet) : Prop :=
  ∀ M (m : M), ∃ Cs, Cs M Cs ∧ ∀ x, I x -> C x m.