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

(* Definition ℒ := l_left. *)
(* Notation "'𝕃,' l" := (l_left l) (at level 5, format "'𝕃,' l").
Notation "'ℝ,' l" := (l_right l) (at level 5).
Notation "'𝕃'" := (l_left l_root) (at level 5).
Notation "'ℝ'" := (l_right l_root) (at level 5). *)

(* Fixpoint l_extend (l extension : Location) := match l with 
  | l_root => extension
  | l_left l => l_left (l_extend l extension)
  | l_right l => l_right (l_extend l extension)
  end. *)

(* Notation  *)

(* Definition l_left_child := l_extend (l_left l_root).
Definition l_right_child := l_extend (l_right l_root). *)

(****************************************************
                   Unif
****************************************************)

Notation "P '⊆1' Q" := (∀ x, P x -> Q x) (at level 70, no associativity) : type_scope.
Notation "P '∧1' Q" := (λ x, P x ∧ Q x) (at level 80, right associativity) : type_scope.
Notation "P '∨1' Q" := (λ x, P x ∨ Q x) (at level 85, right associativity) : type_scope.
(* Notation "P '⊇1' Q" := (Q ⊆1 P) (at level 70, no associativity) : type_scope. *)
Notation "P '≡1' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity) : type_scope.
Notation "P '⊆2' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
(* Notation "P '⊇2' Q" := (Q ⊆2 P) (at level 70, no associativity) : type_scope. *)
Notation "P '≡2' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.

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
(* Definition RewritesPossibleInLR (R : LRel) : LRel :=
  λ l m, ∀ n, (R n l -> R n m) ∧ (R l n -> R m n).
Definition PrefixRewritesPossibleInLR (R : LRel) : LRel :=
  λ l m, ∀ n, (R n l? -> R n m?) ∧ (R l? n -> R m? n).
Definition PairsWithChildrenRelatedBy (R : LRel) : LRel :=
  λ l m, (R (l_left_child l) (l_left_child m) ∧
        R (l_right_child l) (l_right_child m)). *)

(* Class LRIncludesAllWaysToRewriteItself (R : LRel) := {
  lr_includes_all_ways_to_rewrite_itself : RewritesPossibleInLR R ⊆2 R
  }.
Class LRCanRewriteItself (R : LRel) := {
  lr_can_rewrite_itself : R ⊆2 RewritesPossibleInLR R
  }. *)
(* Class LRRelatesLocsWhoseChildrenItRelates (R : LRel) := {
  lr_relates_locs_whose_children_it_relates : PairsWithChildrenRelatedBy R ⊆2 R
  }.
Class LRRelatesLocsWhoseParentItRelates (R : LRel) := {
  lr_relates_locs_whose_parent_it_relates : R ⊆2 PairsWithChildrenRelatedBy R
  }. *)

(* Instance lre_rewrites R : LREquivalence R -> LRCanRewriteItself R.
  constructor. split; intro.
  eapply lr_trans; eassumption.
  eapply lr_trans; [apply lr_sym|]; eassumption.
Qed. *)

Definition LeftPrefixRewrites (R : LRel) : LRel :=
  λ x y, ∀ z w, R (x++z) w -> R (y++z) w.

(* "IsUnificationPredicate" perhaps, but that's long *)
Class Unif (R : LRel) := {
  unif : R ≡2 LeftPrefixRewrites R
}.

Lemma left_rewrite_exact R [x y z] :
  LeftPrefixRewrites R x y -> R x z -> R y z.
  intros.
  rewrite <- (app_nil_r y).
  apply H.
  rewrite (app_nil_r x).
  assumption.
Qed.
Lemma uhhhh R : (LeftPrefixRewrites R ⊆2 R) -> LRRefl R.
  unfold LeftPrefixRewrites; constructor; intros.
  apply H; intros; assumption.
Qed.
Lemma rewrites_sym R : (R ⊆2 LeftPrefixRewrites R) -> LRRefl R -> LRSym R.
  constructor. intros.
  apply (left_rewrite_exact (H _ _ H1)).
  apply lr_refl.
Qed.
Lemma lrr_includes_rewrites R : (R ⊆2 LeftPrefixRewrites R) -> LRRefl R -> (LeftPrefixRewrites R ⊆2 R).
  intros.
  apply rewrites_sym; trivial.
  apply (left_rewrite_exact H1).
  apply lr_refl.
Qed.
Lemma u_from_rewrites_and_refl R {rrefl : LRRefl R} : (R ⊆2 LeftPrefixRewrites R) -> Unif R.
  constructor; split; intros.
  apply H; assumption.
  apply lrr_includes_rewrites; assumption.
Qed.

Lemma u_refl R : Unif R -> LRRefl R.
  intros. apply uhhhh. apply unif.
Qed.
Hint Immediate u_refl : typeclass_instances.
Lemma u_sym R : Unif R -> LRSym R.
  intros. apply rewrites_sym. apply unif. apply u_refl; assumption.
Qed.
Hint Immediate u_sym : typeclass_instances.
Lemma u_trans R : Unif R -> LRTrans R.
  constructor; intros.
  apply lr_sym in H0.
  apply unif in H0.
  apply (left_rewrite_exact H0).
  assumption.
Qed.
Hint Immediate u_trans : typeclass_instances.
Lemma u_equiv R : Unif R -> LREquivalence R.
  constructor; exact _.
Qed.
Hint Immediate u_equiv : typeclass_instances.

(* Class Unif (R : LRel) := u_cons {
    u_equiv :: LREquivalence R
  ; u_children_parent :: LRRelatesLocsWhoseChildrenItRelates R
  ; u_parent_children :: LRRelatesLocsWhoseParentItRelates R
  }.
Hint Immediate u_cons : typeclass_instances. *)

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

(* Class Unif (U : LRel) : Prop := {
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
  := λ l m, ∀ U, R ⊆2 U -> Unif U -> U l m.

Lemma MUS_Superset R : R ⊆2 MinimumUSuperset R.
  unfold MinimumUSuperset; intros. apply H0; assumption.
Qed.
Instance MUS_Refl R : LRRefl (MinimumUSuperset R).
  unfold MinimumUSuperset; constructor; intros.
  apply lr_refl.
Qed.
Instance MUS_U R : Unif (MinimumUSuperset R).
  apply u_from_rewrites_and_refl; [exact _|].
  unfold MinimumUSuperset; unfold LeftPrefixRewrites; intros.
  specialize (H _ H1 H2).
  specialize (H0 _ H1 H2).
  apply unif in H. apply H; assumption.
Qed.

(* Instance MUC_Refl R : LRRefl (MinimumUSuperset R).
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
Instance MUC_U R : Unif (MinimumUSuperset R) := _. *)

Inductive LRSingleton x y : LRel :=
  lr_singleton : LRSingleton x y x y.
Definition MinimumURelating x y := MinimumUSuperset (LRSingleton x y).

Definition LRSet := LRel -> Prop.
Inductive LSSingleton x : LRSet :=
  ls_singleton : LSSingleton x x.

Class USet (US : LRSet) := {
    uset_members_are_unifications : US ⊆1 Unif
  }.
Class UPossibilities (US : LRSet) := {
    upo_uset :: USet US
  ; upo_includes_supersets : 
      ∀ U1 U2, Unif U2 -> U1 ⊆2 U2 -> US U1 -> US U2
  }.
  
(* Definition USNaiveSuperset (A B : LRSet) :=
  ∀ u, B u -> A u. *)

Instance d_us : Derives LRSet LRSet := {
    derives := λ A B, B ⊆1 A
  }.

Inductive MinimumUPosSuperset (US : LRSet) : LRSet :=
  | muc_cons U V : US U -> Unif V -> U ⊆2 V -> MinimumUPosSuperset US V.
(* Inductive MinimumUPosContaining (U : LRel) : LRSet :=
  | muc_cons V : Unif V -> U ⊆2 V -> MinimumUPosContaining U V. *)
(* Definition MinimumUPosSuperset (US : LRSet) : LRSet
  := λ u, ∀ VS, US ⊆1 VS -> UPossibilities VS -> VS u. *)
Definition MinimumUPosContaining (U : LRel) := MinimumUPosSuperset (LSSingleton U).

Lemma MUSC_U U : Unif U -> MinimumUPosContaining U U.
  econstructor. constructor. assumption. trivial.
Qed.
Instance MUSC_USet R : USet (MinimumUPosSuperset R).
  constructor; intros; destruct H. assumption.
Qed.
Instance MUSC_UPoss R : UPossibilities (MinimumUPosSuperset R).
  constructor; [apply MUSC_USet|]. intros. destruct H1.
  econstructor; trivial. exact H1. intros l m Ulm. apply H0. apply H3. assumption.
Qed.

(****************************************************
                Reified unifications
****************************************************)

(* Reified Finite Unif *)
Inductive RFU :=
  | rfu_LL_RL
  | rfu_LR_RRL
  | rfu_LR_RRR
  | rfu_pushL (_:RFU)
  | rfu_pullR (_:RFU)
  | rfu_require_both (_ _:RFU)
  .

(* Reified Unif Set *)
Inductive RUS :=
  | rus_LL_RL
  | rus_LR_RRL
  | rus_LR_RRR
  | rus_pushL (_:RUS)
  | rus_pullR (_:RUS)
  | rus_intersection (_ _:RUS)
  (* | rus_union (_ _:RUS) *)
  | rus_iterate (base step:RUS)
  .
Declare Scope rus_scope.
Bind Scope rus_scope with RUS.

Locate "[]".
Definition U_LL_RL := MinimumURelating (𝕃::𝕃::nil) (ℝ::𝕃::nil).
Definition U_LR_RRL := MinimumURelating (𝕃::ℝ::nil) (ℝ::ℝ::𝕃::nil).
Definition U_LR_RRR := MinimumURelating (𝕃::ℝ::nil) (ℝ::ℝ::ℝ::nil).

Definition US_LL_RL := MinimumUPosContaining U_LL_RL.
Definition US_LR_RRL := MinimumUPosContaining U_LR_RRL.
Definition US_LR_RRR := MinimumUPosContaining U_LR_RRR.

Inductive UPushL (U : LRel) : LRel :=
  | u_pushL l m : U l m -> UPushL U (𝕃::l) (𝕃::m)
  | u_pushL_refl l : UPushL U l l.

Inductive UPullR (U : LRel) : LRel :=
  | u_pullR l m : U (ℝ::l) (ℝ::m) -> UPullR U l m.
Hint Extern 1 (UPullR _ _ _) => progress apply u_pullR; shelve : simplify.
Hint Extern 5 => progress match goal with
  | H : UPullR _ ?x ?y |- _ => dontforget x; dontforget y; destruct H
  end; shelve : simplify.

Instance UPushL_Refl U : LRRefl (UPushL U).
  constructor; apply u_pushL_refl.
Qed.
Instance UPushL_U U : Unif U -> Unif (UPushL U).
  intro. apply u_from_rewrites_and_refl; [exact _|].
  unfold LeftPrefixRewrites; intros.
  
  remember (x ++ z).
  remember (y ++ z).
  destruct H0, H1.
  {
    rewrite <- app_comm_cons in Heql.
    rewrite <- app_comm_cons in Heql0.
    injection Heql as ->.
    rewrite Heql0; clear Heql0.
    apply u_pushL.
    apply unif in H0. apply H0. assumption.
  }
  {
    rewrite <- app_comm_cons in Heql.
    rewrite <- app_comm_cons in Heql0.
    rewrite Heql; clear Heql.
    rewrite Heql0; clear Heql0.
    apply u_pushL.
    apply unif in H0. apply H0. apply lr_refl.
  }
  {
    rewrite <- Heql0 in Heql; clear Heql0.
    rewrite <- Heql; clear Heql.
    apply u_pushL; assumption.
  }
  {
    rewrite Heql; clear Heql.
    rewrite Heql0; clear Heql0.
    apply u_pushL_refl.
  }
Qed.
Lemma UPushL_monotonic [U V : LRel] : U ⊆2 V -> UPushL U ⊆2 UPushL V.
  intros U_V l m UUlm.
  destruct UUlm.
  apply u_pushL; apply U_V; assumption.
  apply u_pushL_refl.
Qed.

Instance UPullR_Refl U : LRRefl U -> LRRefl (UPullR U).
  constructor. constructor. apply lr_refl.
Qed.
Instance UPullR_U U : Unif U -> Unif (UPullR U).
  intro. apply u_from_rewrites_and_refl; [exact _|].
  unfold LeftPrefixRewrites; intros.
  
  remember (x ++ z).
  remember (y ++ z).
  destruct H0, H1.
  constructor.
  
  rewrite Heql in H1; clear l Heql.
  rewrite Heql0; clear l0 Heql0.
  apply unif in H0. apply H0. assumption.
Qed.
Lemma UPullR_monotonic [U V : LRel] : U ⊆2 V -> UPullR U ⊆2 UPullR V.
  intros U_V l m UUlm.
  destruct UUlm.
  apply u_pullR; apply U_V; assumption.
Qed.

(* Inductive USApplyInAllCases (map : LRel -> LRel) (US : LRSet) : LRSet :=
  us_apply_in_all_cases u v : US u -> (map u) ⊆2 v -> USApplyInAllCases map US v. *)
Inductive MappedLRSets (map : LRel -> LRel) (US : LRSet) : LRSet :=
  mapped_lrset u : US u -> MappedLRSets map US (map u).
Definition USApplyInAllCases (map : LRel -> LRel) US := MinimumUPosSuperset (MappedLRSets map US).
Definition USPushL := USApplyInAllCases UPushL.
Definition USPullR := USApplyInAllCases UPullR.

Lemma USApplyInAllCases_monotonic map (map_monotonic : ∀ U V, U ⊆2 V -> map U ⊆2 map V) :
  (∀ US VS, US ⊆1 VS -> USApplyInAllCases map US ⊆1  USApplyInAllCases map VS).
  intros.
  destruct H0. destruct H0.
  econstructor. econstructor.
  apply H. apply H0.
  assumption. assumption.
Qed.

(* Definition USUnion (A B : LRSet) : LRSet := λ u, A u ∨ B u.
Definition USIntersection (A B : LRSet) : LRSet := λ u, A u ∧ B u. *)
(* Definition USRequireBoth (A B : LRSet) : LRSet := λ u, A u ∨ B u. *)
(* Definition URequireBoth (A B : LRel) : LRel := λ l m, A u ∨ B u. *)
Inductive URequireBoth (A B : LRel) : LRel :=
  | urb_left : A ⊆2 URequireBoth A B
  | urb_right : B ⊆2 URequireBoth A B
  (* | urb_trans : LRTrans (URequireBoth A B) *)
  | urb_trans x y z : URequireBoth A B x y -> URequireBoth A B y z -> URequireBoth A B x z
  .
Instance URequireBoth_Refl A B : LRRefl A -> LRRefl (URequireBoth A B).
  constructor; intros. apply urb_left. apply lr_refl.
Qed.
Instance URequireBoth_U A B : Unif A -> Unif B -> Unif (URequireBoth A B).
  intros. apply u_from_rewrites_and_refl; [exact _|].
  intros l m UABlm.

  (* intros j k UABxjk. *)
  induction UABlm; intros j k UABxjk.
  3: {
    apply IHUABlm2.
    apply IHUABlm1.
    assumption.
  }
  {
    apply unif in H1.
    pose (H1 j _ (lr_refl _)) as Ayjxj.
    eapply urb_trans.
    apply urb_left; apply Ayjxj.
    assumption.
  }
  {
    apply unif in H1.
    pose (H1 j _ (lr_refl _)) as Byjxj.
    eapply urb_trans.
    apply urb_right; apply Byjxj.
    assumption.
  }
Qed.

Instance Intersection_USet A B : USet A -> USet (A ∧1 B).
  constructor; intros.
  apply uset_members_are_unifications.
  apply H0.
Qed.
Instance Intersection_UPoss A B : UPossibilities A -> UPossibilities B -> UPossibilities (A ∧1 B).
  constructor; [exact _|].
  intros.
  destruct H3. split; eapply upo_includes_supersets; eassumption.
Qed.

(* Inductive USRequireBoth (A B : LRSet) : LRSet :=
  | us_require_both a b c :
      A a -> B b -> (a ⊆2 c) -> (b ⊆2 c) ->
      LRTrans c -> USRequireBoth A B c. *)


Inductive USIterate (Base Step : LRSet) : LRSet :=
  (* | usi_base Base :
      Base B -> USIterate Base Step B *)
  (* | usi_base : (USIterate Base Step) ⊢ Base *)
  | usi_base : Base ⊆1 USIterate Base Step
  (* | usi_iterate :
      USNaiveSuperset (USIterate Base Step)
        (λ Tail, USRequireBoth Step (USPushR Tail)) *)
  (* | usi_iterate Tail S Combined :
      Step S -> USIterate Base Step Tail ->
      (S ⊢ Combined) -> (UPushR Tail ⊢ Combined) ->
      USIterate Base Step Combined *)
  | usi_iterate :
      (Step ∧1 (USPushL (USIterate Base Step)))
      ⊆1 USIterate Base Step
  .

Instance USIterate_USet Base Step : UPossibilities Base -> UPossibilities Step -> USet (USIterate Base Step).
  constructor; intros.
  induction H1.
  { apply (@uset_members_are_unifications Base). exact _. assumption. }
  { destruct H1. apply (@uset_members_are_unifications Step). exact _. assumption. }
Qed.
Instance USIterate_UPoss Base Step : UPossibilities Base -> UPossibilities Step -> UPossibilities (USIterate Base Step).
  constructor; [exact _|].
  intros.
  induction H3.
  apply usi_base; eapply upo_includes_supersets; eassumption.
  {
    apply usi_iterate.
    destruct H3. split; eapply upo_includes_supersets; eassumption.
  }
Qed.

Fixpoint URfu rfu : LRel := match rfu with
  | rfu_LL_RL => U_LL_RL
  | rfu_LR_RRL => U_LR_RRL
  | rfu_LR_RRR => U_LR_RRR
  | rfu_pushL a => UPushL (URfu a)
  | rfu_pullR a => UPullR (URfu a)
  | rfu_require_both a b => URequireBoth (URfu a) (URfu b)
  end.

Fixpoint UsRus rus : LRSet := match rus with
  | rus_LL_RL => US_LL_RL
  | rus_LR_RRL => US_LR_RRL
  | rus_LR_RRR => US_LR_RRR
  | rus_pushL a => USPushL (UsRus a)
  | rus_pullR a => USPullR (UsRus a)
  (* | rus_union a b => USUnion (UsRus a) (UsRus b) *)
  | rus_intersection a b => (UsRus a) ∧1 (UsRus b)
  | rus_iterate base step => USIterate (UsRus base) (UsRus step)
  end.

Fixpoint rus_rfu rfu : RUS := match rfu with
  | rfu_LL_RL => rus_LL_RL
  | rfu_LR_RRL => rus_LR_RRL
  | rfu_LR_RRR => rus_LR_RRR
  | rfu_pushL a => rus_pushL (rus_rfu a)
  | rfu_pullR a => rus_pullR (rus_rfu a)
  | rfu_require_both a b => rus_intersection (rus_rfu a) (rus_rfu b)
  end.

Instance RFU_U rfu : Unif (URfu rfu).
  induction rfu; exact _.
Qed.

Instance RUS_U rus : UPossibilities (UsRus rus).
  induction rus; exact _.
Qed.
  
(****************************************************
                      Something
****************************************************)

Lemma minupos_applymap_agrees map (map_monotonic : ∀ U V, U ⊆2 V -> map U ⊆2 map V) As B (UB: Unif B) :
  As ≡1 MinimumUPosContaining B ->
  USApplyInAllCases map As ≡1 MinimumUPosContaining (map B).
  intro AeB.
  split; intro As_x.
  {
    eapply USApplyInAllCases_monotonic in As_x; [|apply map_monotonic|apply AeB].

    destruct As_x. destruct H. destruct H. destruct H.
    econstructor; [constructor|assumption|].
    intros l m UUlm.
    apply H1.
    apply (map_monotonic _ _ H3).
    assumption.
  }
  {
    destruct As_x. destruct H.
    eapply USApplyInAllCases_monotonic.
    apply map_monotonic.
    apply AeB.
    econstructor.
    constructor. econstructor. constructor.
    3: exact _.
    3: eassumption.
    exact _.
    trivial.
  }
Qed.

Lemma rus_rfu_correct rfu : UsRus (rus_rfu rfu) ≡1 MinimumUPosContaining (URfu rfu).
  induction rfu; cbn.
   
  (* Base cases *)
  1-3: split; intros; assumption.

  (* UPushL *)
  apply minupos_applymap_agrees; [apply UPushL_monotonic|exact _|assumption].

  (* UPullR *)
  apply minupos_applymap_agrees; [apply UPullR_monotonic|exact _|assumption].

  (* Intersection *)
  {
    intro U.
    split; intros.
    {
      destruct H as (URU1, URU2).
      pose (uset_members_are_unifications _ URU1) as UU; clearbody UU.
      econstructor; [constructor|exact UU|].
      {
        intros l m Ulm.
        induction Ulm.
        {
          apply IHrfu1 in URU1.
          destruct URU1. destruct H0.
          apply H2.
          assumption.
        }
        {
          apply IHrfu2 in URU2.
          destruct URU2. destruct H0.
          apply H2.
          assumption.
        }
        {
          assert (LRTrans U).

          exact _.
          eapply lr_trans; eassumption.
        }
      }
    }
    {
      destruct H. destruct H.
      split; [apply IHrfu1|apply IHrfu2].
      all: econstructor; [constructor|assumption|]; intros l m Ulm; apply H1.
      apply urb_left; assumption.
      apply urb_right; assumption.
    }
  }
Qed.

Inductive DisjointLocations :=
  | dl_root
  | dl_branch (l r : DisjointLocations).

Inductive InDL : DisjointLocations -> Location -> Prop :=
  | idl_root : InDL dl_root nil
  | idl_left l r x : InDL l x -> InDL (dl_branch l r) (𝕃::x)
  | idl_right l r x : InDL r x -> InDL (dl_branch l r) (ℝ::x)
  .

Inductive UniteDL (dl : DisjointLocations) : LRel :=
  | udl_refl x : UniteDL dl x x
  | udl_cousins (x y d : Location) :
      InDL dl x -> InDL dl y -> UniteDL dl (x++d) (y++d)
  .

Instance UniteDL_Refl dl : LRRefl (UniteDL dl).
  constructor. intros. apply udl_refl.
Qed.

Lemma DLs_same_suffix [dl x y d0 d1] :
  InDL dl x -> InDL dl y -> (x ++ d0) = (y ++ d1) -> d0 = d1.
  revert x y d0 d1.
  induction dl.
  intros.
  dependent destruction H;
  dependent destruction H0.
  rewrite 2 app_nil_l in H1; assumption.

  intros.
  dependent destruction H;
  dependent destruction H0;
  rewrite <- 2 app_comm_cons in H1;
  try discriminate.

  {
    injection H1 as H2.
    refine (IHdl1 _ _ _ _ _ _ H2); assumption.
  }
  {
    injection H1 as H2.
    refine (IHdl2 _ _ _ _ _ _ H2); assumption.
  }
Qed.
  

Instance UniteDL_U dl : Unif (UniteDL dl).
  apply u_from_rewrites_and_refl; [exact _|].

  intros xd yd Uxyd l m Uxdm.
  destruct Uxyd; simplify.
  remember ((x ++ d) ++ l).
  destruct Uxdm; simplify.
  {
    rewrite <- 2 app_assoc.
    apply udl_cousins; assumption.
  }
  {
    rewrite <- app_assoc in Heql0.
    rewrite (DLs_same_suffix H1 H Heql0).
    rewrite <- app_assoc.
    apply udl_cousins; assumption.
  }
Qed.

Inductive ReflOrCousins (x y xd yd : Location) : Prop :=
  | cor_refl : xd = yd -> ReflOrCousins x y xd yd
  | cor_cousins_xy (d : Location) : xd = x++d -> yd = y++d -> ReflOrCousins x y xd yd
  | cor_cousins_yx (d : Location) : xd = y++d -> yd = x++d -> ReflOrCousins x y xd yd
  .

Instance ReflOrCousins_Refl x y : LRRefl (ReflOrCousins x y).
  constructor. intros. apply cor_refl. reflexivity.
Qed.
Instance ReflOrCousins_U x y : Unif (ReflOrCousins x y).
  apply u_from_rewrites_and_refl; [exact _|].
  intros xd yd Rxyd l m R.
  destruct Rxyd; simplify.
  {
    destruct R; simplify.
    apply cor_cousins_yx with (d ++ l); apply eq_sym; apply app_assoc.
    {
      rewrite <- app_assoc in H.
      apply app_inv_head_iff in H.
      rewrite <- H.
      apply cor_refl.
      apply eq_sym; apply app_assoc.
    }
    apply cor_cousins_xy with (d ++ l).
    ; apply eq_sym; apply app_assoc.
    {
      rewrite <- app_assoc in H.
      apply app_inv_head_iff in H.
      rewrite <- H.
      apply cor_refl.
      apply eq_sym; apply app_assoc.
    }
  }
  
  ; apply eq_sym; apply app_assoc.

  destruct R; simplify.
  apply cor_cousins with (d ++ l).
  simplify.
  remember (x0 ++ z). destruct H0. assumption.
Qed.
Lemma MUR_cousins_or_refl x y xd yd :
  MinimumURelating x y xd yd -> ReflOrCousins x y xd yd.
  intro H.
  unfold MinimumURelating,MinimumUSuperset in H.
  apply H.
  intros x0 y0 l. destruct l.
  apply cor_cousins with nil; apply eq_sym; apply app_nil_r.


Definition rfu_L_R := rfu_pullR (rfu_pullR (rfu_require_both rfu_LR_RRL rfu_LR_RRR)).
Lemma rfu_L_R_correct : URfu rfu_L_R ≡2 MinimumURelating (𝕃::nil) (ℝ::nil).
  split; cbn; intro.
  {
    simplify.
  }
  {
    simplify.
  }




    remember (ℝ :: ℝ :: l). remember (ℝ :: ℝ :: m).
    destruct H; simplify.
    
    (* destruct H. *)
    (* simplify. *)
    (* cbv in H. *)
    {
      assert (l=m).
      unfold U_LR_RRL,MinimumURelating,MinimumUSuperset in H.
      apply H.
      admit.
      rewrite H0.
      apply lr_refl.
    }
    {
      admit.
    }
    {
      assert (Unif (URequireBoth U_LR_RRL U_LR_RRR)); [exact _|].
      pose (lr_trans _ _ _ H H0).
    }

    exfalso.
    refine (H (λ x y, ¬ LRSingleton (ℝ :: ℝ :: l) (ℝ :: ℝ :: m) x y) _ _ _).
    {
      intros.
      destruct H0.
      intro.
      dependent destruction H0.
    }

    pose (H eq).
    intros.
    (* remember (𝕃 :: ℝ :: nil).
    remember (ℝ :: ℝ :: 𝕃 :: nil). *)
    destruct H0.
    destruct H.
  

Definition rfu_pushR (r : RFU) : RFU :=
  rfu_require_both rfu_L_R (rfu_pushL r).

(* Definition rfu_LR_RR (l m : Location) :=
  rfu_require_both rfu_LR_RL () *)
Fixpoint rfu_L_Rx (x : Location) :=
  match x with
  | nil => rfu_L_R
  | c::x => rfu_pullR (rfu_require_both
      (rfu_require_both
        rfu_LL_RL
        (rfu_pushL (rfu_L_Rx x)) (* i.e. LL=LRx *)
      )  
      match c with 
    | 𝕃 => rfu_LR_RRL (* RL=LL=LRx=RRLx, so after pullR, L=RLx*)
    | ℝ => rfu_LR_RRR (* RL=LL=LRx=RRRx, so after pullR, L=RRx*)
    end)
  end.
Definition rfu_unify (a b : Location) :=
  (* Ra=L=Rb, so after pullR, a=b*)
  rfu_pullR (rfu_require_both (rfu_L_Rx a) (rfu_L_Rx b)).
Definition rfu_LL_R := rfu_unify (𝕃::𝕃::nil) (ℝ::nil).

Definition rus_pullL (s : RUS) : RUS :=
  rus_pullR (rus_intersection (rus_pushL s) (rus_LL_R)).

Definition rus_union (a b : RUS) : RUS :=
  rus_pullL (rus_iterate (rus_pushL a) (rus_pushL b)).


Inductive FiniteTree T :=
  | ft_leaf (_:T)
  | ft_branch (_ _ : FiniteTree T)
  .

Inductive FtEqualities : FiniteTree T -> LRel :=
  λ l m, 