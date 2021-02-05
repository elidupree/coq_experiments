Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
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
