Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Fin.
Require Import Coq.Program.Equality.
Notation "x × y" := (prod x y) (at level 60, right associativity) : type_scope.

Ltac dig depth report :=
  first [solve[idtac]; report |
    guard depth > 0 ; multimatch goal with
      | _ => intro; dig (depth - 1) ltac:(report; idtac "intro")
      | _ => contradiction; dig (depth - 1) ltac:(report; idtac "contradiction")
      | [H : _ |- _] => dependent destruction H; dig (depth - 10) ltac:(report; idtac "dependent destruction"; idtac H)
    end].

Tactic Notation "report_solved" tactic(x) string(y) := timeout 1 (solve [x]); idtac y; gfail.
Tactic Notation "report_progress" tactic(x) string(y) := timeout 1 (progress x); idtac y; fail.
Ltac explore :=
  assert_succeeds (first [
    report_solved (assumption) "`assumption` solves it" | report_solved (reflexivity) "`reflexivity` solves it" | report_solved (contradiction) "`contradiction` solves it" | report_solved (constructor) "`constructor` solves it" | report_solved (discriminate) "`discriminate` solves it" | report_solved (injection) "`injection` solves it" | report_solved (decide equality) "`decide equality` solves it" | report_solved (trivial) "`trivial` solves it" | report_solved (tauto) "`tauto` solves it" | report_solved (dtauto) "`dtauto` solves it" | report_solved (congruence) "`congruence` solves it" | report_solved (firstorder) "`firstorder` solves it" | report_solved (easy) "`easy` solves it" | report_solved (auto) "`auto` solves it" | report_solved (eauto) "`eauto` solves it" | report_solved (auto with *) "`auto with *` solves it" | report_solved (eauto with *) "`eauto with *` solves it" |
    report_progress (subst) "`subst` makes progress" |
    idtac "done"
  ]).

Theorem m2: ∀P Q R:Prop,P→Q→R→Q.
  intros.
  
  (* 
  multimatch goal with|[H : _ |- _] => let k := (type of H) in idtac k; fail end.
  cut ((P,Q)=(Q,R)).
  intros <-.
  intros [= <- <- <-].
  injection H as <- <-.
  first [idtac "a"; fail | idtac"b"]. *)
  explore.
  
  multimatch goal with|[H : _ |- _] => let k := (type of H) in idtac k end.
  assumption.
Qed.


Fixpoint lookup A (l : list A) : Fin.t (length l) → A.
  refine(match l return Fin.t (length l) → A with
    | nil => λ i, Fin.case0 (λ _, A) i
    | x :: xs => λ i, match i in Fin.t n return (n = S (length xs)) → A with
      | F1 _ => λ _, x
      | FS _ p => λ eq, _
    end eq_refl
  end).
  injection eq as ->.
  exact (lookup A xs p).
Defined.
(* Notation "l [ i ]" := (lookup l i) (at level 70). *)


(*Reserved Notation "l [ i ]" (at level 70).*)
Inductive listIndex A : list A → Type :=
| here (head: A) (tail: list A) : listIndex (head::tail)
| there head tail (intexInTail : listIndex tail) : listIndex (head::tail).
(*where "l [ i ]"  := (listIndex l i).*)

Fixpoint valueAt A (l : list A) (i : listIndex l) : A :=
  match i with
  | here head _ => head
  | there _ _ indexInTail => valueAt indexInTail
  end.

Fixpoint positionOf A (l : list A) (i : listIndex l) : nat :=
  match i with
  | here _ _ => 0
  | there _ _ indexInTail => S (positionOf indexInTail)
  end.

Fixpoint replaceAt A (l : list A) (i : listIndex l) (new : A) : list A :=
  match i with
  | here _ tail => new :: tail
  | there head _ indexInTail => head :: replaceAt indexInTail new
  end.

Lemma replaceRetainsLength A (l : list A) (i : listIndex l) (new : A) : length (replaceAt i new) = length l.
  induction i.
  easy.
  unfold length in *; cbn; rewrite IHi; reflexivity.
Qed.

Lemma listIndex_In A (l : list A) (i : listIndex l) : In (valueAt i) l.
  induction i; cbn; tauto.
Qed.

(*
Notation "l [ i ] ; P" := (sigT i P) (at level 70).
  
Notation "l [ i ] [ j ]" := { x : l[i] & (valueAt x) [j] } (at level 70).

Reserved Notation "l [ i ] = v" (at level 70).
Inductive index A : list A → nat → A → Prop :=
| here (head: A) (tail: list A) : (head::tail)[0] = head
| there head tail i v (inTail : tail[i] = v) : (head::tail)[S i] = v
where "l [ i ] = v"  := (index l i v).

Definition foo : (0:: nil)[0] = 0 := here 0 nil.

Reserved Notation "l [ i ] = v" (at level 70).
Inductive index2 A : list (list A) → nat → nat → A → Prop :=
| here (head: list A) (tail: list (list A)) : (head::tail)[0] = head
| there head tail i j v (inTail : tail[i][j] = v) : (head::tail)[S i] = v
where "l [ i ] [ j ] = v"  := (index2 l i j v).
*)

