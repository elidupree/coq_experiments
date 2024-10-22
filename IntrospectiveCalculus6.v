Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import List.
Require Import String.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(****************************************************
               Contexts and relations
****************************************************)

Class Context C := {
    ct_branch : C -> C -> C
  ; ct_branch_injective : ∀ a b c d,
       ((ct_branch a b) = (ct_branch c d)) ->
       (a = c) ∧ (b = d)
}.

Inductive ContextRelation :=
  | cr_compose : ContextRelation -> ContextRelation -> ContextRelation
  | cr_transitive_closure : ContextRelation -> ContextRelation
  | cr_union : ContextRelation -> ContextRelation -> ContextRelation
  | cr_converse : ContextRelation -> ContextRelation
  | cr_in_left : ContextRelation -> ContextRelation
  | cr_rotate_left : ContextRelation
  | cr_swap : ContextRelation
  | cr_dup : ContextRelation
  | cr_drop : ContextRelation
  .
Notation "P '∘' Q" := (cr_compose P Q) (at level 35, right associativity). 
Notation "P '^T'" := (cr_converse P) (at level 30).

Inductive TransitiveClosure F (R : F -> F -> Prop) : F -> F -> Prop :=
  | tc_single a b : R a b -> TransitiveClosure R a b
  | tc_trans a b c :
    TransitiveClosure R a b ->
    TransitiveClosure R b c ->
    TransitiveClosure R a c
    .

(* Definition ContextRelationCoq := ∀ C (CT: Context C), C -> C -> Prop. *)

Inductive CrrCompose {C} {CT: Context C} (R S : C -> C -> Prop)
  : C -> C -> Prop :=
  | crr_compose a b c : R a b -> S b c -> CrrCompose R S a c
  .

Inductive CrrConverse {C} {CT: Context C} (R : C -> C -> Prop)
  : C -> C -> Prop :=
  | crr_converse a b : R a b -> CrrConverse R b a
  .

Inductive CrrInLeft {C} {CT: Context C} (R : C -> C -> Prop)
  : C -> C -> Prop :=
  | crr_in_left a b c : R a b -> CrrInLeft R (ct_branch a c) (ct_branch b c)
  .

Inductive CrrRotateLeft {C} {CT: Context C}
  : C -> C -> Prop :=
  | crr_rotate_left a b c : CrrRotateLeft
      (ct_branch a (ct_branch b c)) (ct_branch (ct_branch a b) c)
  .

Inductive CrrSwap {C} {CT: Context C}
  : C -> C -> Prop :=
  | crr_swap a b : CrrSwap (ct_branch a b) (ct_branch b a)
  .

Inductive CrrDup {C} {CT: Context C}
  : C -> C -> Prop :=
  | crr_dup a : CrrDup a (ct_branch a a)
  .

Inductive CrrDrop {C} {CT: Context C}
  : C -> C -> Prop :=
  | crr_drop a b : CrrDrop (ct_branch a b) a
  .

Fixpoint CrRelates {C} {CT: Context C} (R : ContextRelation)
  : C -> C -> Prop :=
  match R with
  | cr_compose R s => CrrCompose (CrRelates R) (CrRelates s)
  | cr_transitive_closure R => TransitiveClosure (CrRelates R)
  | cr_union R s => λ a b, CrRelates R a b ∨ CrRelates s a b
  | cr_converse R => CrrConverse (CrRelates R)
  | cr_in_left R => CrrInLeft (CrRelates R)
  | cr_rotate_left => @CrrRotateLeft _ _
  | cr_swap => @CrrSwap _ _
  | cr_dup => @CrrDup _ _
  | cr_drop => @CrrDrop _ _
  end.

(****************************************************
          Proof automation bureaucracy
****************************************************)

Ltac autouse_shelving_db steps db :=
  idtac steps; match steps with
    | S ?p => try ((progress (unshelve typeclasses eauto 99 with db));
      autouse_shelving_db p db)
    | _ => idtac "Warning: steps ran out"
  end.

(****************************************************
      Proof automation for context relations
****************************************************)

Notation "R ⊆2 S" := (∀ x y, R x y -> S x y) (at level 70).
Lemma CrrCompose_monotonic_left
  {C} {CT: Context C} (R S R2 : C -> C -> Prop) :
  R ⊆2 R2 ->
  CrrCompose R S ⊆2 CrrCompose R2 S.
  intros. destruct H0.
  apply crr_compose with b; [apply H|]; assumption.
Qed.
Lemma CrrCompose_monotonic_right
  {C} {CT: Context C} (R S S2 : C -> C -> Prop) :
  S ⊆2 S2 ->
  CrrCompose R S ⊆2 CrrCompose R S2.
  intros. destruct H0.
  apply crr_compose with b; [|apply H]; assumption.
Qed.

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

Ltac destruct_crr crr :=
  match type of crr with
  | _ ?a ?b => dontforget a; dontforget b; destruct crr
  end.

Ltac break_down_one_builtin_crr :=
  match goal with
  | H : _ ∧ _ |- _ => destruct H
  | H : CrRelates _ _ _ |- _ => progress (hnf in H)
  | H : CrrCompose _ _ _ _ |- _ => destruct_crr H
  | H : TransitiveClosure _ _ _ |- _ => destruct_crr H
  | H : CrrConverse _ _ _ |- _ => destruct_crr H
  | H : CrrInLeft _ _ _ |- _ => destruct_crr H
  | H : CrrRotateLeft _ _ |- _ => destruct_crr H
  | H : CrrSwap _ _ |- _ => destruct_crr H
  | H : CrrDup _ _ |- _ => destruct_crr H
  | H : CrrDrop _ _ |- _ => destruct_crr H
  | H : ct_branch _ _ = ct_branch _ _ |- _ => destruct (ct_branch_injective _ _ _ _ H); clear H
  end.

Create HintDb break_down_crrs.
Ltac break_down_crrs :=
  autouse_shelving_db 20 ident:(break_down_crrs); trivial.

Hint Extern 5 => progress break_down_one_builtin_crr; shelve
  : break_down_crrs.

Hint Extern 1 (CrRelates _ _ _) => progress hnf; shelve
  : break_down_crrs.
Hint Extern 1 (CrrInLeft _ _ _) => simple apply crr_in_left; shelve
  : break_down_crrs.
Hint Extern 1 (CrrConverse _ _ _) => simple apply crr_converse; shelve
  : break_down_crrs.
Hint Immediate crr_rotate_left : break_down_crrs.
Hint Immediate crr_swap : break_down_crrs.
Hint Immediate crr_dup : break_down_crrs.
Hint Immediate crr_drop : break_down_crrs.

Hint Extern 2 (CrrCompose _ _ _ _) => progress cbn; shelve
  : break_down_crrs.
Hint Extern 1 (CrrCompose CrrSwap _ (ct_branch _ _) _) =>
  simple eapply crr_compose; [solve[simple apply crr_swap]|]; shelve
  : break_down_crrs.
Hint Extern 1 (CrrCompose _ CrrSwap _ (ct_branch _ _)) =>
  simple eapply crr_compose; [|solve[simple apply crr_swap]]; shelve
  : break_down_crrs.
Hint Extern 1 (CrrCompose CrrDup _ _ _) =>
  simple eapply crr_compose; [solve[simple apply crr_dup]|]; shelve
  : break_down_crrs.
Hint Extern 1 (CrrCompose CrrDrop _ (ct_branch _ _) _) =>
  simple eapply crr_compose; [solve[simple apply crr_drop]|]; shelve
  : break_down_crrs.
(* Hint Extern 1 (CrrCompose CrrDup CrrDrop ?a _) =>
  simple eapply crr_compose; [solve[simple apply crr_dup]|]; shelve
  : break_down_crrs. *)

(****************************************************
        Concrete usage of context relations
****************************************************)

Print CrrDup_ind.
(* Scheme  *)

Definition cr_id := cr_dup ∘ cr_dup^T.
Lemma cr_id_correct {C} {CT: Context C} a b :
  CrRelates cr_id a b <-> a = b.
  split; intro.
  {
    break_down_crrs.
  }
  {
    rewrite H.
    break_down_crrs.
  }
Qed.
Definition cr_dropleft := cr_swap ∘ cr_drop.
Inductive CrrDropleft {C} {CT: Context C}
  : C -> C -> Prop :=
  | crr_dropleft a b : CrrDropleft (ct_branch a b) b
  .
Hint Immediate crr_dropleft : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrrDropleft ?a ?b |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Hint Extern 1 (CrrCompose CrrDropleft _ (ct_branch _ _) _) =>
  simple eapply crr_compose; [solve[simple apply crr_dropleft]|]; shelve
  : break_down_crrs.
Lemma cr_dropleft_correct {C} {CT: Context C} a b :
  CrRelates cr_dropleft a b <-> CrrDropleft a b.
  split; intro.
  {
    break_down_crrs.
    rewrite H.
    break_down_crrs.
  }
  {
    break_down_crrs.
  }
Qed.


Definition cr_branch (a b : ContextRelation) : ContextRelation :=
  (cr_dup ∘ (cr_in_left b)) ∘ (cr_swap ∘ (cr_in_left a)).

Lemma cr_branch_correct {C} {CT: Context C} R S i r s :
  CrRelates (cr_branch R S) i (ct_branch r s) <->
  CrRelates R i r ∧ CrRelates S i s.
  split; intro. 
  {
    break_down_crrs. break_down_crrs.
    repeat match goal with
    | H : _ = _ |- _ => rewrite H in *; clear H
    end.
    split; assumption.
  }
  {
    econstructor; break_down_crrs.
  }
Qed.

(****************************************************
        Standard forms of inference rules
****************************************************)

Inductive VariableLocations :=
  | vl_here : VariableLocations
  | vl_branch : VariableLocations -> VariableLocations -> VariableLocations
  .

Inductive WhichVariable : VariableLocations -> Set :=
  | wv_here : WhichVariable vl_here
  | wv_left l r : WhichVariable l -> WhichVariable (vl_branch l r)
  | wv_right l r : WhichVariable r -> WhichVariable (vl_branch l r)
  .

Inductive GenericContext (vl : VariableLocations) :=
  | gc_var : WhichVariable vl -> GenericContext vl
  | gc_branch : GenericContext vl -> GenericContext vl -> GenericContext vl
  .

Instance ct_gc vl : Context (GenericContext vl).
  refine {|
    ct_branch := @gc_branch _
  |}.

  intros; split; injection H; trivial.
Defined.

Hint Extern 5 => progress (
    change (@gc_branch ?a) with
           (@ct_branch (GenericContext a) _) in *); shelve
  : break_down_crrs.

Fixpoint gc_map_vars
  (vl0 vl1 : VariableLocations)
  (m : WhichVariable vl0 -> WhichVariable vl1)
  (gc : GenericContext vl0)
  : GenericContext vl1 :=
  match gc with
  | gc_var wv => gc_var (m wv)
  | gc_branch l r => gc_branch (gc_map_vars m l) (gc_map_vars m r)
  end.

Definition gc_huddle_left l r
  : GenericContext l -> GenericContext (vl_branch l r) :=
  gc_map_vars (@wv_left _ _).

Definition gc_huddle_right l r
  : GenericContext r -> GenericContext (vl_branch l r) :=
  gc_map_vars (@wv_right _ _).

Fixpoint gc_standard_layout_of (vl : VariableLocations) :=
  match vl with
  | vl_here => gc_var wv_here
  | vl_branch l r => gc_branch
    (gc_huddle_left _ (gc_standard_layout_of l))
    (gc_huddle_right _ (gc_standard_layout_of r))
  end.

Fixpoint cr_select_variable vl (wv : WhichVariable vl) : ContextRelation :=
  match wv with
  | wv_here => cr_id
  | wv_left _ _ wv => cr_drop ∘ (cr_select_variable wv)
  | wv_right _ _ wv => cr_dropleft ∘ (cr_select_variable wv)
  end
  .

Ltac print foo := idtac foo.

Lemma cr_select_variable_correct vl (wv : WhichVariable vl) :
  CrRelates (cr_select_variable wv) (gc_standard_layout_of vl) (gc_var wv).
  induction wv;
    break_down_crrs.
  {
    (* probably lemma *)
    induction l; break_down_crrs.
    (* cbn in *. break_down_crrs. *)
    dependent destruction wv.
    apply cr_id_correct; reflexivity.

    break_down_crrs.

    induction wv; break_down_crrs.
    rewrite Heqg0 in *; clear c Heqg0.
    cbn in *.
    change (@gc_branch ?a) with
           (@ct_branch (GenericContext a) _) in Heqg.
    destruct (ct_branch_injective _ _ _ _ Heqg).
    rewrite H in *. rewrite H1 in *. clear H H1 a b Heqg.
    change (@gc_branch ?a) with
           (@ct_branch (GenericContext a) _).
    break_down_crrs.
    
    cbn in *.
  }
  {
    eapply CrrCompose_monotonic_left; [apply cr_dropleft_correct|].
    (* change (@gc_branch (vl_branch l r)) with
           (@ct_branch (GenericContext (vl_branch l r)) _). *)
    break_down_crrs.
  }
  cbn.
Qed.

Fixpoint cr_gc vl (gc : GenericContext vl) : ContextRelation :=
  match gc with
  | gc_var wv => cr_select_variable wv
  | gc_branch l r => cr_branch (cr_gc l) (cr_gc r)
  end
  .

Lemma cr_gc_correct vl gc :
  CrRelates (cr_gc gc) (gc_standard_layout_of vl) gc.
  induction gc.
  apply cr_select_variable_correct.
  apply cr_branch_correct; assumption.
Qed.



Inductive DD T : T -> Type :=
  ddcons t : DD t.

Lemma test : True -> True.
  intro.
  match goal with
  | H : _ |- _ => match constr:(ddcons H) with
    | (ddcons ?J) => dependent destruction J
    end
  end.
  match goal with
  | H : _ |- _ => dependent destruction H
  end.
  dependent destruction H.
