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

Inductive CrCompose (R S : ContextRelation) : ContextRelation :=
  | cr_compose {C} {CT: Context C} a b c
      : R _ _ a b -> S _ _ b c -> CrCompose R S _ a c
  .
Notation "P '∘' Q" := (CrCompose P Q) (at level 35, right associativity) : cr_scope. 

Inductive CrTransitiveClosure (R : ContextRelation) : ContextRelation :=
  | cr_tc_single {C} {CT: Context C} a b
      : R _ _ a b -> CrTransitiveClosure R _ a b
  | cr_tc_trans {C} {CT: Context C} a b c :
    CrTransitiveClosure R _ a b ->
    CrTransitiveClosure R _ b c ->
    CrTransitiveClosure R _ a c
    .

Inductive CrUnion (R S : ContextRelation) : ContextRelation :=
  | cr_union_left {C} {CT: Context C} a b
      : R _ _ a b -> CrUnion R S _ a b
  | cr_union_right {C} {CT: Context C} a b
      : S _ _ a b -> CrUnion R S _ a b
  .
Notation "P '∪' Q" := (CrUnion P Q) (at level 85, right associativity) : cr_scope. 

Inductive CrConverse (R : ContextRelation) : ContextRelation :=
  | cr_converse {C} {CT: Context C} a b
      : R _ _ a b -> CrConverse R _ b a
  .
Notation "P '^T'" := (CrConverse P) (at level 30) : cr_scope.

Inductive CrInLeft (R : ContextRelation) : ContextRelation :=
  | cr_in_left {C} {CT: Context C} a b c
      : R _ _ a b -> CrInLeft R _ (ct_branch a c) (ct_branch b c)
  .

Inductive CrRotateLeft : ContextRelation :=
  | cr_rotate_left {C} {CT: Context C} a b c : CrRotateLeft _
      (ct_branch a (ct_branch b c)) (ct_branch (ct_branch a b) c)
  .

Inductive CrSwap : ContextRelation :=
  | cr_swap {C} {CT: Context C} a b
      : CrSwap _ (ct_branch a b) (ct_branch b a)
  .

Inductive CrDup : ContextRelation :=
  | cr_dup {C} {CT: Context C} a : CrDup _ a (ct_branch a a)
  .

Inductive CrDrop : ContextRelation :=
  | cr_drop {C} {CT: Context C} a b : CrDrop _ (ct_branch a b) a
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

Hint Extern 6 (CRofUP _ _ _ _) => progress hnf; shelve
  : break_down_crrs.
Hint Extern 7 => match goal with
  | H : CRofUP _ _ _ _ |- _ => progress hnf in H
  end; shelve : break_down_crrs.
  
Hint Extern 1 (CrInLeft _ _ _ _) => simple apply cr_in_left; shelve
  : break_down_crrs.
Hint Extern 1 (CrConverse _ _ _ _) => simple apply cr_converse; shelve
  : break_down_crrs.
Hint Immediate cr_rotate_left : break_down_crrs.
Hint Immediate cr_swap : break_down_crrs.
Hint Immediate cr_dup : break_down_crrs.
Hint Immediate cr_drop : break_down_crrs.

Hint Extern 2 (CrCompose _ _ _ _ _) => progress cbn; shelve
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

(****************************************************
        Concrete usage of context relations
****************************************************)

Print CrDup_ind.
(* Scheme  *)

Definition u_id : UnificationProgram := u_dup ∘ u_dup^T.
Inductive CrId : ContextRelation :=
  | cr_id {C} {CT: Context C} a : CrId _ a a
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
  split; intro; break_down_crrs.
  {
    rewrite H.
    break_down_crrs.
  }
Qed.


Definition u_dropleft : UnificationProgram := u_swap ∘ u_drop.
Inductive CrDropleft : ContextRelation :=
  | cr_dropleft {C} {CT: Context C} a b : CrDropleft _ (ct_branch a b) b
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
  split; intro; break_down_crrs.
  {
    rewrite H.
    break_down_crrs.
  }
Qed.


Definition u_branch (a b : UnificationProgram) : UnificationProgram :=
  (u_dup ∘ (u_in_left b)) ∘ (u_swap ∘ (u_in_left a)).
Inductive CrBranch (R S : ContextRelation) : ContextRelation :=
  | cr_branch {C} {CT: Context C} a b c :
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

Lemma u_branch_correct a b :
  CRofUP (u_branch a b) ≡ CrBranch (CRofUP a) (CRofUP b).
  split; intro; break_down_crrs.
  {
    econstructor; break_down_crrs.
  }
  all: 
    repeat match goal with
    | H : _ = _ |- _ => rewrite H in *; clear H
    end;
    break_down_crrs.
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
Inductive CrFromLeft (R : ContextRelation) : ContextRelation :=
  | cr_from_left {C} {CT: Context C} a b c :
      R _ _ a c ->
      CrFromLeft R _ (ct_branch a b) c.
Inductive CrFromRight (R : ContextRelation) : ContextRelation :=
  | cr_from_right {C} {CT: Context C} a b c :
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


Lemma u_select_variable_correct wv :
  CRofUP (u_select_variable wv) ≡ CrSelectVariable wv.
  induction wv.

  split; intro; break_down_crrs.
  {
    rewrite H. break_down_crrs.
  }
  {
    split; intro; break_down_crrs.
  }
  {
    split; intro; break_down_crrs.
  }
  {
    induction H.
     break_down_crrs.
     break_down_crrs.
     break_down_crrs.
  }

  induction wv.
  {
    cbn.
    (* split; intro.
     destruct_crr H. *)
    
     break_down_crrs.
    apply cr_dup.
  }
  Set Debug Eauto.
  split; intro.
  induct_crr H.

  break_down_crrs.
  ; break_down_crrs.
Qed.

Ltac print foo := idtac foo.

Lemma u_select_variable_correct vl (wv : WhichVariable) (wvivl : WVinVL vl wv) :
  CRofUP (u_select_variable wv) (gc_standard_layout_of vl) (gc_var wv).
  induction wvivl;
    break_down_crrs.
  {
    induction wv; break_down_crrs; break_down_crrs.
    break_down_crrs.
    repeat match goal with
    | H : _ = _ |- _ => rewrite H in *; clear H
    end.
    break_down_crrs.

    (* probably lemma *)
    induction l; break_down_crrs.
    {
      (* cbn in *. break_down_crrs. *)
      dependent destruction wv; break_down_crrs; discriminate.
    }


      

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
    eapply CrCompose_monotonic_left; [apply u_dropleft_correct|].
    (* change (@gc_branch (vl_branch l r)) with
           (@ct_branch (GenericContext (vl_branch l r)) _). *)
    break_down_crrs.
  }
  cbn.
Qed.

Fixpoint u_gc vl (gc : GenericContext vl) : UnificationProgram :=
  match gc with
  | gc_var wv => u_select_variable wv
  | gc_branch l r => u_branch (u_gc l) (u_gc r)
  end
  .

Lemma u_gc_correct vl gc :
  CRofUP (u_gc gc) (gc_standard_layout_of vl) gc.
  induction gc.
  apply u_select_variable_correct.
  apply u_branch_correct; assumption.
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
