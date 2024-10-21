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

Definition ContextRelationCoq := ∀ C (CT: Context C), C -> C -> Prop.
Inductive CrrInLeft C {CT: Context C} (R : C -> C -> Prop)
  : C -> C -> Prop :=
  | crr_in_left a b c : R a b -> CrrInLeft R (ct_branch a c) (ct_branch b c)
  .

Inductive CrrRotateLeft C {CT: Context C}
  : C -> C -> Prop :=
  | crr_rotate_left a b c : CrrRotateLeft
      (ct_branch a (ct_branch b c)) (ct_branch (ct_branch a b) c)
  .

Inductive CrrSwap C {CT: Context C}
  : C -> C -> Prop :=
  | crr_swap a b : CrrSwap (ct_branch a b) (ct_branch b a)
  .

Inductive CrrDup C {CT: Context C}
  : C -> C -> Prop :=
  | crr_dup a : CrrDup a (ct_branch a a)
  .

Inductive CrrDrop C {CT: Context C}
  : C -> C -> Prop :=
  | crr_drop a b : CrrDrop (ct_branch a b) a
  .

Fixpoint CrRelates C {CT: Context C} (R : ContextRelation)
  : C -> C -> Prop :=
  match R with
  | cr_compose R s => λ a b, ∃ i, CrRelates R a i ∧ CrRelates s i b
  | cr_transitive_closure R => TransitiveClosure (CrRelates R)
  | cr_union R s => λ a b, CrRelates R a b ∨ CrRelates s a b
  | cr_converse R => λ a b, CrRelates R b a
  | cr_in_left R => CrrInLeft (CrRelates R)
  | cr_rotate_left => @CrrRotateLeft _ _
  | cr_swap => @CrrSwap _ _
  | cr_dup => @CrrDup _ _
  | cr_drop => @CrrDrop _ _
  end.

(****************************************************
        Concrete usage of context relations
****************************************************)

Definition cr_id := cr_dup ∘ cr_dup^T.
Lemma p_id_correct : ProgramImplements p_id (λ _ a b, a = b).
  unfold ProgramImplements; intros.
  split; intro.
  {
    break_down_executions.
  }
  {
    rewrite H.
    unfold p_id.
    break_down_executions.
  }
Qed.
Definition cr_dropleft := cr_drop ∘ cr_swap.

Definition cr_branch (a b : ContextRelation) : ContextRelation :=
  (cr_dup ∘ (cr_in_left b)) ∘ (cr_swap ∘ (cr_in_left a)).

Lemma cr_branch_correct C {CT: Context C} R S i r s :
  CrRelates R i r ->
  CrRelates S i s ->
  CrRelates (cr_branch R S) i (ct_branch r s).
  intros CrR CrS.
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
  | wv_left _ _ wv => (cr_select_variable wv) ∘ cr_drop
  | wv_right _ _ wv => (cr_select_variable wv) ∘ cr_dropleft
  end
  .

Lemma cr_select_variable_correct vl (wv : WhichVariable vl) :
  CrRelates (cr_select_variable wv) (gc_standard_layout_of vl) (gc_var wv).
  induction wv.
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
