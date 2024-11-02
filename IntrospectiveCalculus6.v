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

Inductive UnificationProgram :=
  | u_compose : UnificationProgram -> UnificationProgram -> UnificationProgram
  | u_transitive_closure : UnificationProgram -> UnificationProgram
  | u_union : UnificationProgram -> UnificationProgram -> UnificationProgram
  | u_converse : UnificationProgram -> UnificationProgram
  | u_in_left : UnificationProgram -> UnificationProgram
  | u_rotate_left : UnificationProgram
  | u_swap : UnificationProgram
  | u_dup : UnificationProgram
  | u_drop : UnificationProgram
  .
Declare Scope unif_scope.
Bind Scope unif_scope with UnificationProgram.
Notation "P '∘' Q" := (u_compose P Q) (at level 35, right associativity) : unif_scope. 
Notation "P '∪' Q" := (u_union P Q) (at level 85, right associativity) : unif_scope. 
Notation "P '^T'" := (u_converse P) (at level 30) : unif_scope.

Definition ContextRelation := ∀ C (CT: Context C), C -> C -> Prop.
Declare Scope cr_scope.
Bind Scope cr_scope with ContextRelation.

Definition CrSubset (R S : ContextRelation) : Prop :=
  ∀ C (CT: Context C) a b, S _ _ a b -> R _ _ a b.
Notation "P '⊆' Q" := (CrSubset P Q) (at level 70, no associativity) : type_scope.
Definition CrEquiv (R S : ContextRelation) : Prop :=
  ∀ C (CT: Context C) a b, S _ _ a b <-> R _ _ a b.
Notation "P '≡' Q" := (CrEquiv P Q) (at level 70, no associativity) : type_scope.
Lemma CrSubset_of_CrEquiv R S : R ≡ S -> R ⊆ S.
  unfold CrEquiv, CrSubset. intros. apply H. assumption.
Qed.
Lemma CrEquiv_refl A : A ≡ A.
  unfold CrEquiv; intros; split; trivial.
Qed.
Lemma CrEquiv_sym A B : A ≡ B -> B ≡ A.
  unfold CrEquiv; intros; split; intro; apply H; assumption.
Qed. 
Lemma CrEquiv_trans A B C : A ≡ B -> B ≡ C -> A ≡ C.
  unfold CrEquiv; intros; split; intro.
  apply H. apply H0. assumption.
  apply H0. apply H. assumption.
Qed. 

Inductive CrCompose (R S : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_compose a b c
      : R _ _ a b -> S _ _ b c -> CrCompose R S _ a c
  .
Notation "P '∘' Q" := (CrCompose P Q) (at level 35, right associativity) : cr_scope. 

Inductive CrTransitiveClosure (R : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_tc_single a b
      : R _ _ a b -> CrTransitiveClosure R _ a b
  | cr_tc_trans a b c :
    CrTransitiveClosure R _ a b ->
    CrTransitiveClosure R _ b c ->
    CrTransitiveClosure R _ a c
    .

Inductive CrUnion (R S : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_union_left a b
      : R _ _ a b -> CrUnion R S _ a b
  | cr_union_right a b
      : S _ _ a b -> CrUnion R S _ a b
  .
Notation "P '∪' Q" := (CrUnion P Q) (at level 85, right associativity) : cr_scope. 

Inductive CrConverse (R : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_converse a b
      : R _ _ a b -> CrConverse R _ b a
  .
Notation "P '^T'" := (CrConverse P) (at level 30) : cr_scope.

Inductive CrInLeft (R : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_in_left a b c
      : R _ _ a b -> CrInLeft R _ (ct_branch a c) (ct_branch b c)
  .

Inductive CrRotateLeft C (CT: Context C) : C -> C -> Prop :=
  | cr_rotate_left a b c : CrRotateLeft _
      (ct_branch a (ct_branch b c)) (ct_branch (ct_branch a b) c)
  .

Inductive CrSwap C (CT: Context C) : C -> C -> Prop :=
  | cr_swap a b
      : CrSwap _ (ct_branch a b) (ct_branch b a)
  .

Inductive CrDup C (CT: Context C) : C -> C -> Prop :=
  | cr_dup a : CrDup _ a (ct_branch a a)
  .

Inductive CrDrop C (CT: Context C) : C -> C -> Prop :=
  | cr_drop a b : CrDrop _ (ct_branch a b) a
  .

Fixpoint CRofUP (R : UnificationProgram) : ContextRelation :=
  match R with
  | u_compose R s => (CRofUP R) ∘ (CRofUP s)
  | u_transitive_closure R => CrTransitiveClosure (CRofUP R)
  | u_union R s => (CRofUP R) ∪ (CRofUP s)
  | u_converse R => (CRofUP R)^T
  | u_in_left R => CrInLeft (CRofUP R)
  | u_rotate_left => CrRotateLeft
  | u_swap => CrSwap
  | u_dup => CrDup
  | u_drop => CrDrop
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

(* Notation "R ⊆2 S" := (∀ x y, R x y -> S x y) (at level 70). *)
Lemma CrCompose_monotonic_left (R S R2 : ContextRelation) :
  R ⊆ R2 ->
  R ∘ S ⊆ R2 ∘ S.
  unfold CrSubset; intros. destruct H0.
  apply cr_compose with b; [apply H|]; assumption.
Qed.
Lemma CrCompose_monotonic_right (R S S2 : ContextRelation) :
  S ⊆ S2 ->
  R ∘ S ⊆ R ∘ S2.
  unfold CrSubset; intros. destruct H0.
  apply cr_compose with b; [|apply H]; assumption.
Qed.
Lemma CrCompose_compatibility_left (R S R2 : ContextRelation) :
  R ≡ R2 ->
  R ∘ S ≡ R2 ∘ S.
  unfold CrEquiv; split; intros.
  all: destruct H0; apply cr_compose with b; [apply H|]; assumption.
Qed.
Lemma CrCompose_compatibility_right (R S S2 : ContextRelation) :
  S ≡ S2 ->
  R ∘ S ≡ R ∘ S2.
  unfold CrEquiv; split; intros.
  all: destruct H0; apply cr_compose with b; [|apply H]; assumption.
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
Ltac induct_crr crr :=
  match type of crr with
  | _ ?a ?b => dontforget a; dontforget b; induction crr
  end.

Ltac break_down_one_builtin_crr :=
  match goal with
  | H : _ ∧ _ |- _ => destruct H
  | H : CrCompose _ _ _ _ _ |- _ => destruct_crr H
  (* | H : CrTransitiveClosure _ _ _ _ |- _ => induct_crr H *)
  | H : CrConverse _ _ _ _ |- _ => destruct_crr H
  | H : CrInLeft _ _ _ _ |- _ => destruct_crr H
  | H : CrRotateLeft _ _ _ |- _ => destruct_crr H
  | H : CrSwap _ _ _ |- _ => destruct_crr H
  | H : CrDup _ _ _ |- _ => destruct_crr H
  | H : CrDrop _ _ _ |- _ => destruct_crr H
  | H : ct_branch _ _ = ct_branch _ _ |- _ => destruct (ct_branch_injective _ _ _ _ H); clear H
  | eq : ?R ≡ ?S , H : ?R ?C ?CT ?a ?b |- ?S ?C ?CT ?a ?b => apply eq; exact H
  | eq : ?S ≡ ?R , H : ?R ?C ?CT ?a ?b |- ?S ?C ?CT ?a ?b => apply eq; exact H
  end.

Create HintDb break_down_crrs.
Ltac break_down_crrs :=
  autouse_shelving_db 20 ident:(break_down_crrs); trivial.

Hint Extern 5 => progress break_down_one_builtin_crr; shelve
  : break_down_crrs.

Hint Extern 6 => progress match goal with
    | eq : _ = _ |- _ => lazymatch (type of eq) with
      | (_ _) = (_ _) => fail
      | _ = (_ _) => try (rewrite eq in *); clear eq
      | _ => try (rewrite <- eq in *); clear eq
      end
    end; shelve
  : break_down_crrs.
(* Hint Extern 8 (CRofUP _ _ _ _) => progress hnf; shelve
  : break_down_crrs. *)
(* Hint Extern 9 => match goal with
  | H : CRofUP _ _ _ _ |- _ => progress hnf in H
  end; shelve : break_down_crrs.
   *)
Hint Extern 1 (CrInLeft _ _ _ _) => simple apply cr_in_left; shelve
  : break_down_crrs.
Hint Extern 1 (CrConverse _ _ _ _) => simple apply cr_converse; shelve
  : break_down_crrs.
Hint Immediate cr_rotate_left : break_down_crrs.
Hint Immediate cr_swap : break_down_crrs.
Hint Immediate cr_dup : break_down_crrs.
Hint Immediate cr_drop : break_down_crrs.

(* Hint Extern 10 (CrCompose _ _ _ _ _) => progress cbn; shelve
  : break_down_crrs. *)
Hint Extern 8 => progress change (CRofUP u_rotate_left) with CrRotateLeft in *; shelve
  : break_down_crrs.
Hint Extern 8 => progress change (CRofUP u_swap) with CrSwap in *; shelve
  : break_down_crrs.
Hint Extern 8 => progress change (CRofUP u_dup) with CrDup in *; shelve
  : break_down_crrs.
Hint Extern 8 => progress change (CRofUP u_drop) with CrDrop in *; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose CrSwap _ _ (ct_branch _ _) _) =>
  simple eapply cr_compose; [solve[simple apply cr_swap]|]; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose _ CrSwap _ _ (ct_branch _ _)) =>
  simple eapply cr_compose; [|solve[simple apply cr_swap]]; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose CrDup _ _ _ _) =>
  simple eapply cr_compose; [solve[simple apply cr_dup]|]; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose CrDrop _ _ (ct_branch _ _) _) =>
  simple eapply cr_compose; [solve[simple apply cr_drop]|]; shelve
  : break_down_crrs.
(* Hint Extern 1 (CrCompose CrDup CrDrop ?a _) =>
  simple eapply cr_compose; [solve[simple apply cr_dup]|]; shelve
  : break_down_crrs. *)
Hint Immediate CrEquiv_refl : break_down_crrs.

(****************************************************
        Concrete usage of context relations
****************************************************)

Print CrDup_ind.
(* Scheme  *)

Definition u_id : UnificationProgram := u_dup ∘ u_dup^T.
Inductive CrId C (CT: Context C) : C -> C -> Prop :=
  | cr_id a : CrId _ a a
  .
Hint Immediate cr_id : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrId _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose CrId _ _ _) =>
  simple eapply cr_compose; [solve[simple apply cr_id]|]; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose _ CrId _ _) =>
  simple eapply cr_compose; [|solve[simple apply cr_id]]; shelve
  : break_down_crrs.
Lemma u_id_correct : CRofUP u_id ≡ CrId.
  cbn; split; intro; break_down_crrs.
Qed.


Definition u_dropleft : UnificationProgram := u_swap ∘ u_drop.
Inductive CrDropleft C (CT: Context C) : C -> C -> Prop :=
  | cr_dropleft a b : CrDropleft _ (ct_branch a b) b
  .
Hint Immediate cr_dropleft : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrDropleft _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Hint Extern 1 (CrCompose CrDropleft _ _ (ct_branch _ _) _) =>
  simple eapply cr_compose; [solve[simple apply cr_dropleft]|]; shelve
  : break_down_crrs.

Lemma u_dropleft_correct : CRofUP u_dropleft ≡ CrDropleft.
  cbn; split; intro; break_down_crrs.
Qed.


Definition u_branch (a b : UnificationProgram) : UnificationProgram :=
  (u_dup ∘ (u_in_left b)) ∘ (u_swap ∘ (u_in_left a)).
Inductive CrBranch (R S : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_branch a b c :
      R _ _ a b ->
      S _ _ a c ->
      CrBranch R S _ a (ct_branch b c)
  .
Hint Extern 1 (CrBranch _ _ _ _ _) =>
  simple apply cr_branch; shelve
  : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrBranch _ _ _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Lemma CrBranch_monotonic_left (R S R2 : ContextRelation) :
  R ⊆ R2 ->
  CrBranch R S ⊆ CrBranch R2 S.
  unfold CrSubset; intros. destruct H0.
  apply cr_branch; [apply H|]; assumption.
Qed.
Lemma CrBranch_monotonic_right (R S S2 : ContextRelation) :
  S ⊆ S2 ->
  CrBranch R S ⊆ CrBranch R S2.
  unfold CrSubset; intros. destruct H0.
  apply cr_branch; [|apply H]; assumption.
Qed.
Lemma CrBranch_compatibility_left (R S R2 : ContextRelation) :
  R ≡ R2 ->
  CrBranch R S ≡ CrBranch R2 S.
  unfold CrEquiv; split; intros.
  all: destruct H0; apply cr_branch; [apply H|]; assumption.
Qed.
Lemma CrBranch_compatibility_right (R S S2 : ContextRelation) :
  S ≡ S2 ->
  CrBranch R S ≡ CrBranch R S2.
  unfold CrEquiv; split; intros.
  all: destruct H0; apply cr_branch; [|apply H]; assumption.
Qed.

Lemma u_branch_correct a b :
  CRofUP (u_branch a b) ≡ CrBranch (CRofUP a) (CRofUP b).
  cbn.
  split; intro; break_down_crrs.
  econstructor; break_down_crrs.
Qed.

Lemma u_branch_correct_subset a b :
  CRofUP (u_branch a b) ⊆ CrBranch (CRofUP a) (CRofUP b).
  intro; apply u_branch_correct.
Qed.



(****************************************************
        Standard forms of inference rules
****************************************************)

Inductive VariableLocations :=
  | vl_here : VariableLocations
  | vl_branch : VariableLocations -> VariableLocations -> VariableLocations
  .

Inductive WhichVariable :=
  | wv_here : WhichVariable
  | wv_left : WhichVariable -> WhichVariable
  | wv_right : WhichVariable -> WhichVariable
  .

Inductive WVinVL : VariableLocations -> WhichVariable -> Prop :=
  | wvivl_here : WVinVL vl_here wv_here
  | wvivl_left l r wv : WVinVL l wv -> WVinVL (vl_branch l r) (wv_left wv)
  | wvivl_right l r wv : WVinVL r wv -> WVinVL (vl_branch l r) (wv_right wv)
  .

Inductive GenericContext :=
  | gc_var : WhichVariable -> GenericContext
  | gc_branch : GenericContext -> GenericContext -> GenericContext
  .

Inductive GCinVL (vl : VariableLocations) : GenericContext -> Prop :=
  | gcivl_var wv : WVinVL vl wv -> GCinVL vl (gc_var wv)
  | gcivl_branch l r : GCinVL vl l -> GCinVL vl r -> GCinVL vl (gc_branch l r)
  .

Inductive WVinGC : GenericContext -> WhichVariable -> Prop :=
  | wvigc_here gc : WVinGC gc wv_here
  | wvigc_left l r wv : WVinGC l wv -> WVinGC (gc_branch l r) (wv_left wv)
  | wvigc_right l r wv : WVinGC r wv -> WVinGC (gc_branch l r) (wv_right wv)
  .

Instance ct_gc : Context GenericContext.
  refine {|
    ct_branch := @gc_branch
  |}.

  intros; split; injection H; trivial.
Defined.

Hint Extern 5 => progress (
    change gc_branch with (@ct_branch GenericContext ct_gc) in *
  ); shelve : break_down_crrs.

Fixpoint gc_map_vars
  (m : WhichVariable -> WhichVariable)
  (gc : GenericContext)
  : GenericContext :=
  match gc with
  | gc_var wv => gc_var (m wv)
  | gc_branch l r => gc_branch (gc_map_vars m l) (gc_map_vars m r)
  end.

(* Fixpoint gc_map_vars
  (vl0 vl1 : VariableLocations)
  (m : WhichVariable -> WhichVariable)
  (gc : GenericContext)
  : GenericContext :=
  match gc with
  | gc_var wv => gc_var (m wv)
  | gc_branch l r => gc_branch (gc_map_vars m l) (gc_map_vars m r)
  end. *)

Definition gc_huddle_left : GenericContext -> GenericContext :=
  gc_map_vars wv_left.

Definition gc_huddle_right : GenericContext -> GenericContext :=
  gc_map_vars wv_right.

(* Definition gc_huddle_left l r
  : GenericContext l -> GenericContext (vl_branch l r) :=
  gc_map_vars (@wv_left _ _).

Definition gc_huddle_right l r
  : GenericContext r -> GenericContext (vl_branch l r) :=
  gc_map_vars (@wv_right _ _). *)

Fixpoint gc_standard_layout_of (vl : VariableLocations) :=
  match vl with
  | vl_here => gc_var wv_here
  | vl_branch l r => gc_branch
    (gc_huddle_left (gc_standard_layout_of l))
    (gc_huddle_right (gc_standard_layout_of r))
  end.

Fixpoint u_select_variable (wv : WhichVariable) : UnificationProgram :=
  match wv with
  | wv_here => u_id
  | wv_left wv => u_drop ∘ (u_select_variable wv)
  | wv_right wv => u_dropleft ∘ (u_select_variable wv)
  end.
Inductive CrFromLeft (R : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_from_left a b c :
      R _ _ a c ->
      CrFromLeft R _ (ct_branch a b) c.
Inductive CrFromRight (R : ContextRelation) C (CT: Context C) : C -> C -> Prop :=
  | cr_from_right a b c :
      R _ _ b c ->
      CrFromRight R _ (ct_branch a b) c.
Fixpoint CrSelectVariable (wv : WhichVariable) : ContextRelation :=
  match wv with
  | wv_here => CrId
  | wv_left wv => CrFromLeft (CrSelectVariable wv)
  | wv_right wv => CrFromRight (CrSelectVariable wv)
  end.
Hint Extern 1 (CrFromLeft _ _ _ _) =>
  simple apply cr_from_left; shelve
  : break_down_crrs.
Hint Extern 1 (CrFromRight _ _ _ _) =>
  simple apply cr_from_right; shelve
  : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrFromLeft _ _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrFromRight _ _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrSelectVariable _ _ _ _ |- _ => progress (hnf in H) end; shelve
  : break_down_crrs.
Hint Extern 1 (CrSelectVariable _ _ _ _) => progress hnf; shelve
  : break_down_crrs.

Create HintDb simplify_crs.
Ltac simplify_crs :=
  let P := fresh "P" in eassert (_ ⊆ _) as P;
    [|simple apply P; clear P]; [solve[auto 5 with simplify_crs]|].
Hint Extern 6 => progress simplify_crs; shelve
  : break_down_crrs.

Hint Resolve CrCompose_monotonic_left : simplify_crs.
Hint Resolve CrCompose_monotonic_right : simplify_crs.
Hint Resolve CrBranch_monotonic_left : simplify_crs.
Hint Resolve CrBranch_monotonic_right : simplify_crs.
Hint Resolve (CrSubset_of_CrEquiv u_dropleft_correct) : simplify_crs.
Hint Immediate u_branch_correct_subset : simplify_crs.


(* Create HintDb simplify_creqs. *)
Ltac simplify_creqs :=
  (eapply CrEquiv_trans; [solve[auto 5 with simplify_crs]|])
  ||
  (eapply CrEquiv_trans; [|apply CrEquiv_sym; solve[auto 5 with simplify_crs]]).
Hint Extern 6 => progress simplify_creqs; shelve
  : break_down_crrs.
Hint Resolve CrCompose_compatibility_left : simplify_crs.
Hint Resolve CrCompose_compatibility_right : simplify_crs.
Hint Resolve CrBranch_compatibility_left : simplify_crs.
Hint Resolve CrBranch_compatibility_right : simplify_crs.
Hint Immediate u_dropleft_correct : simplify_crs.
Hint Immediate u_branch_correct : simplify_crs.

Definition IsSimplification T (t : T) := t.
Ltac hint_simplify H := change ?S with (IsSimplification S) in H.
Ltac hint_simplify_with_hyps := repeat match goal with
  | H : _ ≡ _ |- _ => hint_simplify H
  end.
Hint Extern 1 => match goal with
  | H : IsSimplification ?S |- _ => exact H
  end : simplify_crs.


Lemma u_select_variable_correct wv :
  CRofUP (u_select_variable wv) ≡ CrSelectVariable wv.
  induction wv; cbn; split; intro; break_down_crrs.
Qed.
Hint Immediate u_select_variable_correct : break_down_crrs.
Hint Immediate u_select_variable_correct : simplify_crs.

Ltac print foo := idtac foo.

Lemma CrSelectVariable_only_selects_in wv gc x : 
  CrSelectVariable wv ct_gc gc x -> WVinGC gc wv.
  revert gc x.
  induction wv; break_down_crrs; constructor; eauto.
Qed.


Lemma CrSelectVariable_selects_mapped wv gc m x : 
  CrSelectVariable wv ct_gc gc x -> CrSelectVariable wv ct_gc (gc_map_vars m gc) (gc_map_vars m x).
  intro.
  pose (CrSelectVariable_only_selects_in _ _ _ H) as w;
    clearbody w; revert x H m.

  induction w; break_down_crrs; constructor; auto.
Qed.

Lemma CrSelectVariable_of_standard_layout vl wv (wvivl : WVinVL vl wv) {C} {CT:Context C} :
  CrSelectVariable wv _ (gc_standard_layout_of vl) (gc_var wv).
  induction wvivl; split; intros; break_down_crrs;
    apply (CrSelectVariable_selects_mapped _ _ _ _ IHwvivl).
Qed.

Lemma u_select_variable_of_standard_layout vl wv (wvivl : WVinVL vl wv) :
  CRofUP (u_select_variable wv) _ (gc_standard_layout_of vl) (gc_var wv).
  apply u_select_variable_correct.
  apply CrSelectVariable_of_standard_layout with GenericContext.
  assumption.
  exact _.
Qed.

Fixpoint u_gc gc : UnificationProgram :=
  match gc with
  | gc_var wv => u_select_variable wv
  | gc_branch l r => u_branch (u_gc l) (u_gc r)
  end
  .
Hint Extern 7 => progress change
  (u_gc (ct_branch ?a ?b)) with
  (u_branch (u_gc a) (u_gc b)) 
  in *; shelve : break_down_crrs.
Fixpoint CRofGC (gc : GenericContext) : ContextRelation :=
  match gc with
  | gc_var wv => CrSelectVariable wv
  | gc_branch l r => CrBranch (CRofGC l) (CRofGC r)
  end.
Hint Extern 7 => progress change
  (CRofGC (ct_branch ?a ?b)) with
  (CrBranch (CRofGC a) (CRofGC b)) 
  in *; shelve : break_down_crrs.


Lemma u_gc_correct gc :
  CRofUP (u_gc gc) ≡ CRofGC gc.
  induction gc; break_down_crrs.
  {
    hint_simplify_with_hyps.
    break_down_crrs.
  }
Qed.
Lemma u_gc_pulls_self_from_standard_layout vl gc :
  GCinVL vl gc ->
  CRofUP (u_gc gc) _ (gc_standard_layout_of vl) gc.
  intro giv.
  induction giv; break_down_crrs.
  apply u_select_variable_of_standard_layout; assumption.
Qed.


Definition u_canonical_gc_transform a b : UnificationProgram
  := (u_gc a)^T ∘ u_gc b.

Lemma compose_canonical_transforms vl a b c
  (giva : GCinVL vl a) (givb : GCinVL vl b) (givc : GCinVL vl c)
  : CRofUP ((u_canonical_gc_transform a b) ∘ (u_canonical_gc_transform b c))
  ≡ CRofUP (u_canonical_gc_transform a c).

  

