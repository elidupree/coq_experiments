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
Lemma CrConverse_monotonic (R R2 : ContextRelation) :
  R ⊆ R2 ->
  R ^T ⊆ R2 ^T.
  unfold CrSubset; intros. destruct H0.
  apply cr_converse; apply H; assumption.
Qed.
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
Lemma CrSubset_compatibility_left (R S R2 : ContextRelation) :
  R ≡ R2 ->
  (R2 ⊆ S) -> (R ⊆ S).
  unfold CrEquiv, CrSubset; intros. apply H. apply H0. assumption.
Qed.
Lemma CrSubset_compatibility_right (R S S2 : ContextRelation) :
  S ≡ S2 ->
  (R ⊆ S2) -> (R ⊆ S).
  unfold CrEquiv, CrSubset; intros. apply H0. apply H. assumption.
Qed.
Lemma CrEquiv_compatibility_left (R S R2 : ContextRelation) :
  R ≡ R2 ->
  (R2 ≡ S) -> (R ≡ S).
  intros. eapply CrEquiv_trans; eassumption.
Qed.
Lemma CrEquiv_compatibility_right (R S S2 : ContextRelation) :
  S ≡ S2 ->
  (R ≡ S2) -> (R ≡ S).
  intros. eapply CrEquiv_trans; [|apply CrEquiv_sym]; eassumption.
Qed.
Lemma CrConverse_compatibility (R R2 : ContextRelation) :
  R ≡ R2 ->
  R ^T ≡ R2 ^T.
  unfold CrEquiv; split; intros.
  all: destruct H0; apply cr_converse; apply H; assumption.
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
Hint Extern 8 => progress change (CRofUP (?a ∘ ?b)) with (CrCompose (CRofUP a) (CRofUP b)) in *; shelve
  : break_down_crrs.
  Hint Extern 8 => progress change (CRofUP (?a ^T)) with (CrConverse (CRofUP a)) in *; shelve
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

Definition u_any : UnificationProgram := (u_drop ^T) ∘ u_swap ∘ u_drop.
Inductive CrAny C (CT: Context C) : C -> C -> Prop :=
  | cr_any a b : CrAny _ a b
  .
Hint Immediate cr_any : break_down_crrs.
Hint Extern 5 => progress match goal with
  | H : CrAny _ _ _ |- _ => destruct_crr H
  end; shelve
  : break_down_crrs.

Lemma u_any_correct : CRofUP u_any ≡ CrAny.
  split; intro; repeat econstructor.
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

Class AsProgram T := {
    as_program : T -> UnificationProgram
  ; as_cr : T -> ContextRelation
  ; as_program_agrees_with_as_cr : ∀ t, CRofUP (as_program t) ≡ as_cr t
  }.

Inductive ConcreteContext Value :=
  | cc_val : Value -> ConcreteContext Value
  | cc_branch : ConcreteContext Value -> ConcreteContext Value -> ConcreteContext Value
  .

Instance ct_cc V : Context (ConcreteContext V).
  refine {|
    ct_branch := @cc_branch _
  |}.

  intros; split; injection H; trivial.
Defined.

Fixpoint cc_as_program V {_v:AsProgram V} cc : UnificationProgram :=
  match cc with
  | cc_val v => as_program v
  | cc_branch l r => u_branch (cc_as_program l) (cc_as_program r)
  end
  .
Hint Extern 7 => progress change
  (cc_as_program (ct_branch ?a ?b)) with
  (u_branch (cc_as_program a) (cc_as_program b)) 
  in *; shelve : break_down_crrs.
Hint Extern 7 => progress change
  (cc_as_program (cc_val ?v)) with
  (as_program v) 
  in *; shelve : break_down_crrs.

Fixpoint cc_as_cr V {_v:AsProgram V} cc : ContextSet :=
  match cc with
  | cc_val v => as_cr v
  | cc_branch l r => CrBranch (cc_as_cr l) (cc_as_cr r)
  end.
Hint Extern 7 => progress change
  (cc_as_cr (ct_branch ?a ?b)) with
  (u_branch (cc_as_cr a) (cc_as_cr b)) 
  in *; shelve : break_down_crrs.
Hint Extern 7 => progress change
  (cc_as_cr (cc_val ?v)) with
  (as_cr v) 
  in *; shelve : break_down_crrs.

Instance cc_AsProgram V {_v:AsProgram V} : AsProgram (ConcreteContext V).
  refine {|
    as_program := cc_as_program (_v:=_)
  ; as_cr := cc_as_cr (_v:=_)
  |}.
  intro t; induction t; break_down_crrs.
  apply as_program_agrees_with_as_cr.
  {
    hint_simplify_with_hyps.
    break_down_crrs.
  }
  

(* Inductive VariableLocations :=
  | vl_val : VariableLocations
  | vl_branch : VariableLocations -> VariableLocations -> VariableLocations
  . *)
Definition VariableLocations := ConcreteContext unit.

Inductive WhichVariable :=
  | wv_here : WhichVariable
  | wv_left : WhichVariable -> WhichVariable
  | wv_right : WhichVariable -> WhichVariable
  .

Inductive WVgetsValInCC Value : ConcreteContext Value -> WhichVariable -> Prop :=
  | wvgv_val v : WVgetsValInCC (cc_val v) wv_here
  | wvgv_left l r wv : WVgetsValInCC l wv -> WVgetsValInCC (cc_branch l r) (wv_left wv)
  | wvgv_right l r wv : WVgetsValInCC r wv -> WVgetsValInCC (cc_branch l r) (wv_right wv)
  .

Inductive WVgetsSubtreeOfCC Value : ConcreteContext Value -> WhichVariable -> Prop :=
  | wvgs_val cc : WVgetsSubtreeOfCC cc wv_here
  | wvgs_left l r wv : WVgetsSubtreeOfCC l wv -> WVgetsSubtreeOfCC (cc_branch l r) (wv_left wv)
  | wvgs_right l r wv : WVgetsSubtreeOfCC r wv -> WVgetsSubtreeOfCC (cc_branch l r) (wv_right wv)
  .

(* Fixpoint get_val_in_cc wv V (cc : ConcreteContext V)
  (wvgv : WVgetsValInCC cc wv) : V :=
  match wvgv with
  | wvgv_val v => v
  | wvgv_left l r wv wl => get_val_in_cc wl
  | wvgv_right l r wv wr => get_val_in_cc wr
  (* | wvgv_left l r wv : WVgetsValInCC l wv -> WVgetsValInCC (cc_branch l r) (wv_left wv)
  | wvgv_right l r wv : WVgetsValInCC r wv -> WVgetsValInCC (cc_branch l r) (wv_right wv)
   *)
  end. *)

Definition GenericContext := ConcreteContext WhichVariable.
(* Inductive GenericContext :=
  | gc_var : WhichVariable -> GenericContext
  | gc_branch : GenericContext -> GenericContext -> GenericContext
  . *)

Inductive AllVals V (P : V -> Prop) : ConcreteContext V -> Prop :=
  | av_val v : P v -> AllVals P (cc_val v)
  | av_branch l r : AllVals P l -> AllVals P r -> AllVals P (cc_branch l r)
  .
(* Inductive GCinCC (vl : VariableLocations) : GenericContext -> Prop :=
  | gcivl_var wv : WVgetsValInCC vl wv -> GCinCC vl (cc_val wv)
  | gcicc_branch l r : GCinCC vl l -> GCinCC vl r -> GCinCC vl (cc_branch l r)
  . *)
Definition GCinCC V (cc : ConcreteContext V) : GenericContext -> Prop
 := AllVals (WVgetsValInCC cc).

(* Inductive WVinGC : GenericContext -> WhichVariable -> Prop :=
  | wvigc_here gc : WVinGC gc wv_here
  | wvigc_left l r wv : WVinGC l wv -> WVinGC (cc_branch l r) (wv_left wv)
  | wvigc_right l r wv : WVinGC r wv -> WVinGC (cc_branch l r) (wv_right wv)
  . *)

Hint Extern 5 => progress (
    change (@cc_branch ?V)
      with (@ct_branch (ConcreteContext V) (ct_cc V)) in *
  ); shelve : break_down_crrs.

Fixpoint cc_map_vals
  V W
  (m : V -> W)
  (cc : ConcreteContext V)
  : ConcreteContext W :=
  match cc with
  | cc_val v => cc_val (m v)
  | cc_branch l r => cc_branch (cc_map_vals m l) (cc_map_vals m r)
  end.

(* Fixpoint cc_map_vals
  (vl0 vl1 : VariableLocations)
  (m : WhichVariable -> WhichVariable)
  (gc : GenericContext)
  : GenericContext :=
  match gc with
  | cc_val wv => cc_val (m wv)
  | cc_branch l r => cc_branch (cc_map_vals m l) (cc_map_vals m r)
  end. *)

Definition gc_huddle_left : GenericContext -> GenericContext :=
  cc_map_vals wv_left.

Definition gc_huddle_right : GenericContext -> GenericContext :=
  cc_map_vals wv_right.

(* Definition gc_huddle_left l r
  : GenericContext l -> GenericContext (cc_branch l r) :=
  cc_map_vals (@wv_left _ _).

Definition gc_huddle_right l r
  : GenericContext r -> GenericContext (cc_branch l r) :=
  cc_map_vals (@wv_right _ _). *)

Fixpoint gc_standard_layout_of (vl : VariableLocations) :=
  match vl with
  | cc_val _ => cc_val wv_here
  | cc_branch l r => cc_branch
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
Ltac simplify_crs_in_goal :=
  let P := fresh "P" in eassert (_ ≡ _) as P;
    [|simple apply (CrSubset_of_CrEquiv P); clear P];
    [solve[auto 8 with simplify_crs]|].
Hint Extern 6 => progress simplify_crs_in_goal; shelve
  : break_down_crrs.

Ltac simplify_crs_in_hyp H :=
  let P := fresh "P" in eassert (_ ≡ _) as P;
    [|simple apply (CrSubset_of_CrEquiv (CrEquiv_sym P)) in H; clear P];
    [solve[auto 8 with simplify_crs]|].
    
Ltac simplify_crs_in_hyps :=
  match goal with
  | H: ?CR _ _ _ _ |- _ => match (type of CR) with
    | ContextRelation => simplify_crs_in_hyp H
    end
  end.
Hint Extern 7 => progress simplify_crs_in_hyps; shelve
  : break_down_crrs.

(* Hint Resolve CrSubset_of_CrEquiv : simplify_crs. *)

(* Hint Resolve CrSubset_compatibility_left : simplify_crs.
Hint Resolve CrSubset_compatibility_right : simplify_crs. *)
Hint Resolve CrConverse_compatibility : simplify_crs.
Hint Resolve CrCompose_compatibility_left : simplify_crs.
Hint Resolve CrCompose_compatibility_right : simplify_crs.
Hint Resolve CrBranch_compatibility_left : simplify_crs.
Hint Resolve CrBranch_compatibility_right : simplify_crs.
Hint Resolve u_dropleft_correct : simplify_crs.
Hint Immediate u_any_correct : simplify_crs.
Hint Immediate u_branch_correct : simplify_crs.


(* Create HintDb simplify_creqs. *)
Ltac simplify_crs_in_relation :=
  (eapply CrSubset_compatibility_left +
   eapply CrSubset_compatibility_right +
   eapply CrEquiv_compatibility_left +
   eapply CrEquiv_compatibility_right);
   [solve[auto 8 with simplify_crs]|].
Hint Extern 6 => progress simplify_crs_in_relation; shelve
  : break_down_crrs.

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
(* Lemma u_select_variable_correct_subset wv :
  CRofUP (u_select_variable wv) ⊆ CrSelectVariable wv.
  intro; apply u_select_variable_correct.
Qed. *)
Hint Immediate u_select_variable_correct : break_down_crrs.
Hint Immediate u_select_variable_correct : simplify_crs.
(* Hint Immediate u_select_variable_correct_subset : simplify_crs. *)

Ltac print foo := idtac foo.

Lemma CrSelectVariable_only_selects_in wv V (cc : ConcreteContext V) x : 
  CrSelectVariable wv _ cc x -> WVgetsSubtreeOfCC cc wv.
  revert cc x.
  induction wv; break_down_crrs; constructor; eauto.
Qed.


Lemma CrSelectVariable_selects_mapped wv V W (cc : ConcreteContext V) (m : V -> W) x : 
  CrSelectVariable wv _ cc x -> CrSelectVariable wv _ (cc_map_vals m cc) (cc_map_vals m x).
  intro.
  pose (CrSelectVariable_only_selects_in _ _ _ H) as w;
    clearbody w; revert x H m.

  induction w; break_down_crrs; constructor; auto.
Qed.

Lemma CrSelectVariable_of_standard_layout vl wv (wvgv : WVgetsValInCC vl wv) :
  CrSelectVariable wv _ (gc_standard_layout_of vl) (cc_val wv).
  induction wvgv; split; intros; break_down_crrs;
    apply (CrSelectVariable_selects_mapped _ _ _ _ IHwvgv).
Qed.
Hint Immediate CrSelectVariable_of_standard_layout : break_down_crrs.

Lemma u_select_variable_of_standard_layout vl wv (wvgv : WVgetsValInCC vl wv) :
  CRofUP (u_select_variable wv) _ (gc_standard_layout_of vl) (cc_val wv).
  break_down_crrs.
Qed.

Fixpoint u_gc gc : UnificationProgram :=
  match gc with
  | cc_val wv => u_select_variable wv
  | cc_branch l r => u_branch (u_gc l) (u_gc r)
  end
  .
Hint Extern 7 => progress change
  (u_gc (ct_branch ?a ?b)) with
  (u_branch (u_gc a) (u_gc b)) 
  in *; shelve : break_down_crrs.
Fixpoint CRofGC (gc : GenericContext) : ContextRelation :=
  match gc with
  | cc_val wv => CrSelectVariable wv
  | cc_branch l r => CrBranch (CRofGC l) (CRofGC r)
  end.
Hint Extern 7 => progress change
  (CRofGC (ct_branch ?a ?b)) with
  (CrBranch (CRofGC a) (CRofGC b)) 
  in *; shelve : break_down_crrs.
Hint Extern 7 => progress change
  (CRofGC (cc_val ?v)) with
  (CrSelectVariable v) 
  in *; shelve : break_down_crrs.


Lemma u_gc_correct gc :
  CRofUP (u_gc gc) ≡ CRofGC gc.
  induction gc; break_down_crrs.
  {
    hint_simplify_with_hyps.
    break_down_crrs.
  }
Qed.
(* Lemma u_gc_correct_subset gc :
  CRofUP (u_gc gc) ⊆ CRofGC gc.
  intro; apply u_gc_correct.
Qed. *)
Hint Immediate u_gc_correct : break_down_crrs.
Hint Immediate u_gc_correct : simplify_crs.
(* Hint Immediate u_gc_correct_subset : simplify_crs. *)





Lemma CRofGC_of_standard_layout vl gc :
  GCinCC vl gc ->
  CRofGC gc _ (gc_standard_layout_of vl) gc.
  induction 1; break_down_crrs.
Qed.
Hint Immediate CRofGC_of_standard_layout : break_down_crrs.
Lemma u_gc_pulls_self_from_standard_layout vl gc :
  GCinCC vl gc ->
  CRofUP (u_gc gc) _ (gc_standard_layout_of vl) gc.
  break_down_crrs.
Qed.


Definition u_canonical_gc_transform a b : UnificationProgram
  := (u_gc a)^T ∘ u_gc b.

Lemma compose_canonical_transforms (vl : VariableLocations) a b c
  (giva : GCinCC vl a) (givb : GCinCC vl b) (givc : GCinCC vl c)
  : CRofUP ((u_canonical_gc_transform a b)
          ∘ (u_canonical_gc_transform b c)) ⊆
    CRofUP (u_canonical_gc_transform a c)  
  .
  unfold u_canonical_gc_transform in *.
  break_down_crrs.
  intro; intros.
  break_down_crrs.
  repeat econstructor; try eassumption.
  split.
  Set Debug Auto.
  auto 8 with simplify_crs.
  simple eapply CrSubset_compatibility_left.

  (* induction vl. *)
  induction vl; break_down_crrs.
  2: {
    destruct giva.
    constructor.
  }


 intro; intros.
 break_down_crrs.
 unfold u_canonical_gc_transform in *.
 break_down_crrs.
 