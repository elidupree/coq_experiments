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

(****************************************************
                   Tree structure
****************************************************)

Inductive Location :=
  | l_root : Location
  | l_left : Location -> Location
  | l_right : Location -> Location
  .
(* Definition ℒ := l_left. *)
Notation "'𝕃,' l" := (l_left l) (at level 5, format "'𝕃,' l").
Notation "'ℝ,' l" := (l_right l) (at level 5).
Notation "'𝕃'" := (l_left l_root) (at level 5).
Notation "'ℝ'" := (l_right l_root) (at level 5).

Fixpoint l_extend (l extension : Location) := match l with 
  | l_root => extension
  | l_left l => l_left (l_extend l extension)
  | l_right l => l_right (l_extend l extension)
  end.

Definition l_left_child := l_extend (l_left l_root).
Definition l_right_child := l_extend (l_right l_root).

(****************************************************
                   Unifications
****************************************************)

Notation "P '⊆1' Q" := (∀ x, P x -> Q x) (at level 70, no associativity)
  : type_scope.
Notation "P '≡1' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity)
  : type_scope.
Notation "P '⊆2' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity)
  : type_scope.
Notation "P '≡2' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity)
  : type_scope.

Definition LRel :=
  Location -> Location -> Prop.

(* Inductive View R a b : LRel :=
  | view_cons x y : R (l_extend a x) (l_extend b y) -> View R a b x y.
Print View_ind.

Definition ViewRefl R a b :=
  ∀ P,
    (∀ x y, R (l_extend a x) (l_extend b y) → P x y) →
    (∀ x, P x x).
Definition ViewRefl2 R a b :=
  (∀ x, R (l_extend a x) (l_extend b x)). *)

(* Definition RewriteThingy R a b := *)

(* Inductive SameDescendant  : Location -> Location -> LRel :=
  | sd_same x : SameDescendant l_root x l_root x
  | sd_cons ax dx ay dy : SameDescendant ax dx ay dy -> SameDescendant (𝕃,ax) (𝕃,dx) ay dy. *)

Definition LeftPrefixRewrites (R : LRel) x y :=
  ∀ z w, R (l_extend x z) w -> R (l_extend y z) w.

Definition Unif (R : LRel) := 
  R ≡2 LeftPrefixRewrites R.

Class LRRefl (R : LRel) := {
  lr_refl : ∀ a, R a a
  }.
Class LRSym (R : LRel) := {
  lr_sym : ∀ a b, R a b -> R b a
  }.
Class LRTrans (R : LRel) := {
  lr_trans : ∀ a b c, R a b -> R b c -> R a c
  }.
Class LREquivalence (R : LRel) := lre_cons {
    lre_refl :: LRRefl R
  ; lre_sym :: LRSym R
  ; lre_trans :: LRTrans R
  }.
Hint Immediate lre_cons : typeclass_instances.
Definition RewritesPossibleInLR (R : LRel) : LRel :=
  λ l m, ∀ n, (R n l -> R n m) ∧ (R l n -> R m n).
Definition PrefixRewritesPossibleInLR (R : LRel) : LRel :=
  λ l m, ∀ n, (R n l? -> R n m?) ∧ (R l? n -> R m? n).
Definition PairsWithChildrenRelatedBy (R : LRel) : LRel :=
  λ l m, (R (l_left_child l) (l_left_child m) ∧
        R (l_right_child l) (l_right_child m)).

Class LRIncludesAllWaysToRewriteItself (R : LRel) := {
  lr_includes_all_ways_to_rewrite_itself : RewritesPossibleInLR R ⊆2 R
  }.
Class LRCanRewriteItself (R : LRel) := {
  lr_can_rewrite_itself : R ⊆2 RewritesPossibleInLR R
  }.
Class LRRelatesLocsWhoseChildrenItRelates (R : LRel) := {
  lr_relates_locs_whose_children_it_relates : PairsWithChildrenRelatedBy R ⊆2 R
  }.
Class LRRelatesLocsWhoseParentItRelates (R : LRel) := {
  lr_relates_locs_whose_parent_it_relates : R ⊆2 PairsWithChildrenRelatedBy R
  }.

Instance lre_rewrites R : LREquivalence R -> LRCanRewriteItself R.
  constructor. split; intro.
  eapply lr_trans; eassumption.
  eapply lr_trans; [apply lr_sym|]; eassumption.
Qed.
Instance lre_includes_rewrites R : LRRefl R -> LRIncludesAllWaysToRewriteItself R.
  constructor. intros.
  apply H0. apply lr_refl.
Qed.

Class Unifications (R : LRel) := u_cons {
    u_equiv :: LREquivalence R
  ; u_children_parent :: LRRelatesLocsWhoseChildrenItRelates R
  ; u_parent_children :: LRRelatesLocsWhoseParentItRelates R
  }.
Hint Immediate u_cons : typeclass_instances.

(* Definition LRCanRewriteWithLR (R Rewriter : LRel) :=
  ∀ 
Definition LRMeansItCanRewritesItself R :=
  
Definition LRCanRewriteWithLR (Rewriter R : LRel) :=
  ∀  *)

Class Derives A B := {
    derives : A -> B -> Prop
  }.
Notation "P '⊢' Q" := (derives P Q) (at level 70, no associativity)
  : type_scope.
Definition equiv A B {_dab : Derives A B} {_dba : Derives B A} (a:A) (b:B) := derives a b ∧ derives b a.
Notation "P '⊣⊢' Q" := (equiv P Q) (at level 70, no associativity)
  : type_scope.

(* Class Unifications (U : LRel) : Prop := {
      uv_means_you_can_rewrite : ∀ l m,
        U l m <-> (
          ∀ n, (U n l -> U n m) ∧ (U l n -> U m n)
        )
    ; uv_respects_subtrees : ∀ l m,
        U l m <->
        (U (l_left_child l) (l_left_child m) ∧
        U (l_right_child l) (l_right_child m))
  }. *)

(* Definition UNaiveSubset (A B : LRel) :=
  ∀ l m, A l m -> B l m. *)
  
Instance d_u : Derives LRel LRel := {
    derives := λ A B, A ⊆2 B
  }.

Definition MinimumUSuperset (R : LRel) : LRel
  := λ l m, ∀ U, R ⊢ U -> Unifications U -> U l m.

Lemma MUC_Superset R : R ⊆2 MinimumUSuperset R.
  unfold MinimumUSuperset; intros. apply H0; assumption.
Qed.
Instance MUC_Refl R : LRRefl (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  apply lr_refl.
Qed.
Instance MUC_Sym R : LRSym (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  apply lr_sym; apply H; assumption.
Qed.
Instance MUC_Trans R : LRTrans (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  eapply lr_trans; [apply H|apply H0]; eassumption.
Qed.
Instance MUC_children_parent R : LRRelatesLocsWhoseChildrenItRelates (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  apply lr_relates_locs_whose_children_it_relates.
  destruct H.
  constructor; [apply H|apply H2]; assumption.
Qed.
Instance MUC_parent_children R : LRRelatesLocsWhoseParentItRelates (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  split; intros; apply (@lr_relates_locs_whose_parent_it_relates U _ _ _); apply H; assumption.
Qed.
Instance MUC_Equiv R : LREquivalence (MinimumUSuperset R) := _.
Instance MUC_U R : Unifications (MinimumUSuperset R) := _.

Inductive LRelSingleton x y : LRel :=
  lr_singleton : LRelSingleton x y x y.
Definition MinimumURelating x y := MinimumUSuperset (LRelSingleton x y).

Definition LRSet := LRel -> Prop.

Class USet (US : LRSet) := {
    uset_members_are_unifications : US ⊆1 Unifications
  }.
Class UPossibilities (US : LRSet) := {
    upo_uset :: USet US
  ; upo_includes_supersets : 
      ∀ U1 U2, Unifications U2 -> U1 ⊆2 U2 -> US U1 -> US U2
  }.
  
(* Definition USNaiveSuperset (A B : LRSet) :=
  ∀ u, B u -> A u. *)

Instance d_us : Derives LRSet LRSet := {
    derives := λ A B, B ⊆1 A
  }.

Inductive MinimumUPosContaining (U : LRel) : LRSet :=
  | muc_cons V : Unifications V -> U ⊆2 V -> MinimumUPosContaining U V.

Lemma MUSC_U U : Unifications U -> MinimumUPosContaining U U.
  constructor; trivial.
Qed.
Instance MUSC_USet R : USet (MinimumUPosContaining R).
  constructor; intros; destruct H. assumption.
Qed.
Instance MUSC_UPoss R : UPossibilities (MinimumUPosContaining R).
  constructor; [exact _|]. intros; destruct H.
  constructor; [exact _|]. destruct H1.
  intros l m Rlm. apply H0. apply H1. assumption.
Qed.

(****************************************************
                Reified unifications
****************************************************)

(* Reified Finite Unifications *)
Inductive RFU :=
  | rfu_L_R
  | rfu_L_RL
  | rfu_pushL (_:RFU)
  | rfu_pullR (_:RFU)
  | rfu_require_both (_ _:RFU)
  .

(* Reified Unifications Set *)
Inductive RUS :=
  | rus_L_R
  | rus_L_RL
  | rus_pushL (_:RUS)
  | rus_pullR (_:RUS)
  | rus_intersection (_ _:RUS)
  (* | rus_union (_ _:RUS) *)
  | rus_iterate (base step:RUS)
  .
Declare Scope rus_scope.
Bind Scope rus_scope with RUS.

Definition U_L_R := MinimumURelating 𝕃 ℝ.
Definition U_L_RL := MinimumURelating 𝕃 ℝ,𝕃.

Definition US_L_R := MinimumUPosContaining U_L_R.
Definition US_L_RL := MinimumUPosContaining U_L_RL.

Inductive UPushL (U : LRel) : LRel :=
  | u_pushL l m : U l m -> UPushL U (𝕃,l) (𝕃,m)
  | u_pushL_refl l : UPushL U l l.

Inductive UPullR (U : LRel) : LRel :=
  | u_pullR l m : U (ℝ,l) (ℝ,m) -> UPullR U l m.

Instance UPushL_Refl U : LRRefl (UPushL U).
  constructor. apply u_pushL_refl.
Qed.
Instance UPullR_Refl U : LRRefl U -> LRRefl (UPullR U).
  constructor; intros. constructor. apply lr_refl.
Qed.
Instance UPushL_Sym U : LRSym U -> LRSym (UPushL U).
  constructor; intros. destruct H0; [constructor|apply u_pushL_refl].
  apply lr_sym; assumption.
Qed.
Instance UPullR_Sym U : LRSym U -> LRSym (UPullR U).
  constructor; intros. constructor. destruct H0.
  apply lr_sym; assumption.
Qed.
Instance UPushL_Trans U : LRTrans U -> LRTrans (UPushL U).
  constructor; intros. destruct H0. remember 𝕃,m. destruct H1. injection Heql0 as ->; econstructor; eapply lr_trans; eassumption.
  rewrite Heql0; constructor; assumption.
  assumption.
Qed.
Instance UPullR_Trans U : LRTrans U -> LRTrans (UPullR U).
  constructor; intros. constructor. destruct H0. destruct H1.
  eapply lr_trans; eassumption.
Qed.
Instance UPushL_Equiv U : LREquivalence U -> LREquivalence (UPushL U).
  constructor; exact _.
Qed.
Instance UPullR_Equiv U : LREquivalence U -> LREquivalence (UPullR U).
  constructor; exact _.
Qed.
Instance UPushL_children_parent U : LRRelatesLocsWhoseChildrenItRelates (UPushL U).
  constructor; intros. destruct H.
  remember (l_left_child x). remember (l_left_child y).
  remember (l_right_child x). remember (l_right_child y).
  destruct H, H0.

  apply lr_relates_locs_whose_children_it_relates.
  destruct H.
  constructor; [apply H|apply H2]; assumption.
  all: apply cheat.
Qed.

Instance UPushL_parent_children U : LRRelatesLocsWhoseParentItRelates U -> LRRelatesLocsWhoseParentItRelates (UPushL U).
  intro; constructor; intros l m UUlm.
  destruct UUlm.
  destruct (lr_relates_locs_whose_parent_it_relates _ _ H0).
   constructor.
  constructor; assumption.
  split; intros; apply (@lr_relates_locs_whose_parent_it_relates U _ _ _); apply H; assumption.
Qed.


(* Definition LocationCorrespondence := Location -> Location -> Prop. *)
(* Inductive LRChangeLocations (R : LRel) (U : LRel) : LRel :=
  | lr_change_locations_in l1 l2 m1 m2 :
    R l1 l2 -> R m1 m2 -> U l1 m1 ->
      LRChangeLocations R U l2 m2.

Inductive LRInSomeSubtree (R : LRel) : LRel :=
  | lriss_r : R ⊆2 LRInSomeSubtree R
  | lriss_in_left a b : LRInSomeSubtree R a b -> LRInSomeSubtree R (l_left a) (l_left b)
  | lriss_in_right a b : LRInSomeSubtree R a b -> LRInSomeSubtree R (l_right a) (l_right b)
  .
Inductive LDisjoint : LRel :=
  | ld_split a b : LDisjoint (l_left a) (l_right b)
  | ld_in_left a b : LDisjoint a b -> LDisjoint (l_left a) (l_left b)
  | ld_in_right a b : LDisjoint a b -> LDisjoint (l_right a) (l_right b)
  .


Lemma UCL_Sym R U : LRSym U -> LRSym (LRChangeLocations R U).
  constructor; intros.
  destruct H0.
  econstructor; [eassumption|eassumption|].
  apply lr_sym; assumption.
Qed.
Lemma UCL_Trans R U : R ⊆2 LDisjoint -> LRTrans U -> LRTrans (LRChangeLocations R U).
  constructor; intros.
  destruct H0 as (a1, a2, b1, b2, Ra, Rb, Uab).
  destruct H1 as (bb1, bb2, c1, c2, Rbb, Rc, Ubc).
  econstructor; [eassumption|eassumption|].
  eapply lr_trans.
  rename n3 into m3.
  rename l3 into m2.

Lemma UCL_U R U : Unifications U -> Unifications (UChangeLocations R U).
  intro UU.
  repeat constructor; intros.
  admit.
  {
    destruct H.
    econstructor.
  }

Inductive PushLL : LRel :=
  | pushll_left l : PushLL (l_left l) (l_left (l_left l))
  | pushll_right l : PushLL (l_right l) (l_right l).

Inductive PushLR : LRel :=
  | pushlr_left l : PushLR (l_left l) (l_left (l_right l))
  | pushlr_right l : PushLR (l_right l) (l_right l).

Inductive PushR : LRel := pushr l : PushR l (l_right l).
Inductive PullL : LRel := pulll l : PullL (l_left l) l. *)

(* Inductive UMapLocations (map : Location -> Location) (U : LRel) : LRel :=
  | u_pulldownLLin l m : U l m -> UMapLocations map U (map l) (map m). *)

(* Definition UPullL := UChangeLocations PullL.
Definition UPushR := UChangeLocations PushR.
Definition UPushLL := UChangeLocations PushLL.
Definition UPushLR := UChangeLocations PushLR. *)

Inductive USApplyInAllCases (map : LRel -> LRel) (US : LRSet) : LRSet :=
  us_apply_in_all_cases u : US u -> USApplyInAllCases map US (map u).
Definition USPullL := USApplyInAllCases UPullL.
Definition USPushR := USApplyInAllCases UPushR.
Definition USPushLL := USApplyInAllCases UPushLL.
Definition USPushLR := USApplyInAllCases UPushLR.

Definition USUnion (A B : LRSet) : LRSet := λ u, A u ∨ B u.
Definition USIntersection (A B : LRSet) : LRSet := λ u, A u ∧ B u.
(* Definition USRequireBoth (A B : LRSet) : LRSet := λ u, A u ∨ B u. *)
(* Definition URequireBoth (A B : LRel) : LRel := λ l m, A u ∨ B u. *)
Inductive URequireBoth (A B : LRel) : LRel :=
  | urb_left : UNaiveSubset A (URequireBoth A B)
  | urb_right : UNaiveSubset B (URequireBoth A B)
  | urb_trans : LRTrans (URequireBoth A B)
  .
(* Inductive USRequireBoth (A B : LRSet) : LRSet :=
  | us_require_both a b c :
      A a -> B b -> (a ⊢ c) -> (b ⊢ c) ->
      LRTrans c -> USRequireBoth A B c. *)


Inductive USIterate (Base Step : LRSet) : LRSet :=
  (* | usi_base Base :
      Base B -> USIterate Base Step B *)
  (* | usi_base : (USIterate Base Step) ⊢ Base *)
  | usi_base :
      USNaiveSuperset (USIterate Base Step) Base
  (* | usi_iterate :
      USNaiveSuperset (USIterate Base Step)
        (λ Tail, USRequireBoth Step (USPushR Tail)) *)
  (* | usi_iterate Tail S Combined :
      Step S -> USIterate Base Step Tail ->
      (S ⊢ Combined) -> (UPushR Tail ⊢ Combined) ->
      USIterate Base Step Combined *)
  | usi_iterate :
      USNaiveSuperset (USIterate Base Step) 
        (USIntersection Step (USPushR (USIterate Base Step)))
  .

Fixpoint URfu rfu : LRel := match rfu with
  | rfu_unify_children => UUnifyChildren
  | rfu_pullL a => UPullL (URfu a)
  | rfu_pushR a => UPushR (URfu a)
  | rfu_pushLL a => UPushLL (URfu a)
  | rfu_pushLR a => UPushLR (URfu a)
  | rfu_require_both a b => URequireBoth (URfu a) (URfu b)
  end.

Fixpoint UsRus rus : LRSet := match rus with
  | rus_unify_children => USUnifyChildren
  | rus_pullL a => USPullL (UsRus a)
  | rus_pushR a => USPushR (UsRus a)
  | rus_pushLL a => USPushLL (UsRus a)
  | rus_pushLR a => USPushLR (UsRus a)
  | rus_union a b => USUnion (UsRus a) (UsRus b)
  | rus_intersection a b => USIntersection (UsRus a) (UsRus b)
  | rus_iterate base step => USIterate (UsRus base) (UsRus step)
  end.

Fixpoint rus_rfu rfu : RUS := match rfu with
  | rfu_unify_children => rus_unify_children
  | rfu_pullL a => rus_pullL (rus_rfu a)
  | rfu_pushR a => rus_pushR (rus_rfu a)
  | rfu_pushLL a => rus_pushLL (rus_rfu a)
  | rfu_pushLR a => rus_pushLR (rus_rfu a)
  | rfu_require_both a b => rus_intersection (rus_rfu a) (rus_rfu b)
  end.

  
(****************************************************
                      Something
****************************************************)

Lemma mapped_set_transpose U map : Unifications U -> USApplyInAllCases map (MinimumUPosContaining U) ⊣⊢ MinimumUPosContaining (map U).
  (* unfold USApplyInAllCases. *)
  split; repeat intro.
  destruct H, H0.
  
  constructor.
Qed.

Lemma rus_rfu_correct rfu : UsRus (rus_rfu rfu) ⊣⊢ (MinimumUPosContaining (URfu rfu)).
  red.
  induction rfu; cbn.
  split; repeat intro; assumption.
  split; repeat intro.




Inductive FiniteTree T :=
  | ft_leaf (_:T)
  | ft_branch (_ _ : FiniteTree T)
  .

Inductive FtEqualities : FiniteTree T -> LRel :=
  λ l m, 