Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
(* Require Import List. *)

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.


(****************************************************
                      Rulesets
****************************************************)

Definition AtomIndex := nat.
Definition VarIndex := list bool.
(* Inductive Formula : Type :=
  | f_atom : AtomIndex -> Formula
  | f_apply : Formula -> Formula -> Formula. *)
Class Formula F := {
    f_atom : AtomIndex -> F
  ; f_apply : F -> F -> F
  }.

Notation "[ x y ]" := (f_apply x y)
 (at level 0, x at next level, y at next level).
Notation "[ x y .. z ]" := (f_apply .. (f_apply x y) .. z)
 (at level 0, x at next level, y at next level).
 
Inductive GenericFormula : Type :=
  | gf_atom : AtomIndex -> GenericFormula
  | gf_var : VarIndex -> GenericFormula
  | gf_apply : GenericFormula -> GenericFormula -> GenericFormula.

Instance fgf : Formula GenericFormula := {
    f_atom := gf_atom
  ; f_apply := gf_apply
  }.

Inductive Ruleset :=
  | r_rule : GenericFormula -> GenericFormula -> Ruleset
  | r_plus : Ruleset -> Ruleset -> Ruleset
  .

(* no need to be inductive or coinductive: *)
(* Parameter InfiniteContext : Type -> Type.
Parameter context_arbitrary : ∀ F, InfiniteContext F.
Parameter context_cons : ∀ F, F -> InfiniteContext F -> InfiniteContext F. *)

Definition InfiniteContext F := VarIndex -> F.

Fixpoint specialize F {_f : Formula F} gf ctx : F :=
  match gf with
  | gf_atom a => f_atom a
  | gf_var v => ctx v
  | gf_apply f x => f_apply (specialize f ctx) (specialize x ctx) 
  end.

Notation "x / y" := (specialize x y).
(* 
Inductive Specializes F {_f : Formula F}
  : GenericFormula -> InfiniteContext F -> F -> Prop
  :=
  | sgf_atom xs a : Specializes (gf_atom a) xs (f_atom a)
  | sgf_usage x xs : Specializes (gf_usage) (context_cons x xs) x
  | sgf_pop F x xs f :
      Specializes F xs f ->
      Specializes (gf_pop F) (context_cons x xs) f
  | sgf_apply A B a b xs :
      Specializes A xs a ->
      Specializes B xs b ->
      Specializes (gf_apply A B) xs (f_apply a b)
  . *)

Definition specialize_chain F {_f : Formula F} ctx cty : InfiniteContext F :=
  λ v, specialize (ctx v) cty.

Lemma specialize_chain_correct F {_f : Formula F} ctx cty a :
  (specialize a (specialize_chain ctx cty) = (specialize (specialize a ctx) cty)).
  induction a; trivial.
  cbn; rewrite IHa1, IHa2; reflexivity.
Qed.
Lemma specialize_self_correct a :
  (specialize a gf_var) = a.
  induction a; trivial.
  cbn; rewrite IHa1, IHa2; reflexivity.
Qed.


Inductive RulesetStatesSingle F {_f : Formula F}
  : Ruleset -> F -> F -> Prop :=
  | rss_plus_left r s a b : 
    RulesetStatesSingle r a b ->
    RulesetStatesSingle (r_plus r s) a b
  | rss_plus_right r s a b : 
    RulesetStatesSingle s a b ->
    RulesetStatesSingle (r_plus r s) a b
  | rss_rule P C ctx :
    RulesetStatesSingle (r_rule P C) (P/ctx) (C/ctx)
  .

Inductive Chain F (Step : F -> F -> Prop) : F -> F -> Prop :=
  | chain_refl a : Chain Step a a
  | chain_step_then a b c :
    Step a b ->
    Chain Step b c ->
    Chain Step a c
    .

Lemma chain_step [F Step a b] : 
    Step a b ->
    @Chain F Step a b.
  intro.
  apply chain_step_then with b. assumption. apply chain_refl.
Qed.

Lemma chain_trans F Step a b c : @Chain F Step a b ->
    Chain Step b c ->
    Chain Step a c.
  intros.
  induction H; trivial.
  apply chain_step_then with b; trivial.
  apply IHChain; assumption.
Qed.

Lemma chain_then_step F Step a b c : @Chain F Step a b ->
    Step b c ->
    Chain Step a c.
  intros.
  apply chain_trans with b; trivial.
  apply chain_step; trivial.
Qed.

Lemma chain_map F Step1 Step2 (a b : F) : (∀ x y, Step1 x y -> Step2 x y) -> Chain Step1 a b -> Chain Step2 a b.
  intros.
  induction H0.
  apply chain_refl.
  apply chain_step_then with b; trivial.
  apply H; assumption.
Qed.

Lemma chain_flat_map F Step1 Step2 (a b : F) : (∀ x y, Step1 x y -> Chain Step2 x y) -> Chain Step1 a b -> Chain Step2 a b.
  intros.
  induction H0.
  apply chain_refl.
  apply chain_trans with b; trivial.
  apply H; assumption.
Qed.

Lemma chain_map_mapf [F G Step1 Step2] (a b : F) (map_f : F -> G) (map_step : ∀ x y, Step1 x y -> Step2 (map_f x) (map_f y)) : Chain Step1 a b -> Chain Step2 (map_f a) (map_f b).
  intros.
  induction H.
  apply chain_refl.
  apply chain_step_then with (map_f b); trivial.
  apply map_step; assumption.
Qed.

Lemma chain_flat_map_mapf F G Step1 Step2 (a b : F) (map_f : F -> G) (map_step : ∀ x y, Step1 x y -> Chain Step2 (map_f x) (map_f y)) : Chain Step1 a b -> Chain Step2 (map_f a) (map_f b).
  intros.
  induction H.
  apply chain_refl.
  apply chain_trans with (map_f b); trivial.
  apply map_step; assumption.
Qed.


Definition RulesetStates F {_f : Formula F} (r : Ruleset)
  : F -> F -> Prop := Chain (@RulesetStatesSingle F _f r).

Definition rs_refl F {_f : Formula F} (r : Ruleset) a : @RulesetStates F _f r a a := chain_refl _ _.
Definition rs_single F {_f : Formula F} (r : Ruleset) a b : @RulesetStatesSingle F _f r a b ->
    RulesetStates r a b := λ step, chain_step step.
Definition rs_trans F {_f : Formula F} (r : Ruleset) a b c : @RulesetStates F _f r a b ->
    RulesetStates r b c ->
    RulesetStates r a c := λ ab bc, chain_trans ab bc.
(* Inductive RulesetStates F {_f : Formula F} (r : Ruleset)
  : F -> F -> Prop :=
  | rs_refl a : RulesetStates r a a
  | rs_trans a b c :
    RulesetStates r a b ->
    RulesetStates r b c ->
    RulesetStates r a c
  | rs_single a b :
    RulesetStatesSingle r a b ->
    RulesetStates r a b
    
  (* | rs_rule_then a b c :
    RulesetStatesSingle r a b ->
    RulesetStates r b c ->
    RulesetStates r a c *)
  . *)

(* Inductive RulesetStates F {_f : Formula F} 
  : Ruleset -> F -> F -> Prop :=
  | rs_refl r a : RulesetStates r a a
  | rs_trans r a b c :
    RulesetStates r a b ->
    RulesetStates r b c ->
    RulesetStates r a c
  | rs_plus_left r s a b : 
    RulesetStates r a b ->
    RulesetStates (r_plus r s) a b
  | rs_plus_right r s a b : 
    RulesetStates s a b ->
    RulesetStates (r_plus r s) a b
  | rs_rule P C x p c :
    Specializes P x p ->
    Specializes C x c ->
    RulesetStates (r_rule P C) p c
  . *)

(* Lemma rss_rs F _f R a b : @RulesetStatesSingle F _f R a b -> RulesetStates R a b.
  intro. induction H.
  apply rs_plus_left; assumption.
  apply rs_plus_right; assumption.
  apply rs_rule with x; assumption.
Qed. *)

(* Lemma rs_rs F _f R a b : @RulesetStates F _f R a b -> RulesetStates R a b.
  intro. induction H; try constructor.
  apply rs_trans with b; assumption.
  apply rss_rs; assumption.
Qed. *)

Lemma rs_plus_left F _f r s a b : @RulesetStates F _f r a b ->
    RulesetStates (r_plus r s) a b.
  apply chain_map.
  apply rss_plus_left.
Qed.

Lemma rs_plus_right F _f r s a b : @RulesetStates F _f s a b ->
    RulesetStates (r_plus r s) a b.
  apply chain_map.
  apply rss_plus_right.
Qed.

Lemma rs_rule F _f P C ctx :
    @RulesetStates F _f (r_rule P C) (P/ctx) (C/ctx).
  apply chain_step; apply rss_rule.
Qed.

(* Lemma rs_rs F _f R a b : @RulesetStates F _f R a b -> RulesetStates R a b.
  intro. induction H.
  apply rs_refl.
  apply rs_trans with b; assumption.
  {
    (* TODO reduce duplicate code ID 920605944 *)
    induction IHRulesetStates.
    apply rs_refl.
    apply rs_trans with b; [apply IHIHRulesetStates1 | apply IHIHRulesetStates2]; apply rs_rs; assumption.
    apply rs_single; apply rss_plus_left; assumption.
  }
  {
    (* TODO reduce duplicate code ID 920605944 *)
    induction IHRulesetStates.
    apply rs_refl.
    apply rs_trans with b; [apply IHIHRulesetStates1 | apply IHIHRulesetStates2]; apply rs_rs; assumption.
    apply rs_single; apply rss_plus_right; assumption.
  }
  apply rs_single; apply rss_rule with x; assumption.
Qed. *)

Definition AuthoritativeRulesetDerives R S :=
  ∀ F _f a b, @RulesetStates F _f S a b -> RulesetStates R a b.
(* Definition AuthoritativeRulesetDerivesSingle R S :=
  ∀ F _f a b, @RulesetStatesSingle F _f S a b -> RulesetStatesSingle R a b. *)

Inductive RulesetDerives (r : Ruleset)
  : Ruleset -> Prop :=
  | rd_rule p c :
    RulesetStates r p c ->
    RulesetDerives r (r_rule p c)
  | rd_plus s t :
    RulesetDerives r s ->
    RulesetDerives r t ->
    RulesetDerives r (r_plus s t)
  .

(* Lemma ARD_ARDSingle R S : AuthoritativeRulesetDerives R S -> AuthoritativeRulesetDerivesSingle R S.
  unfold AuthoritativeRulesetDerives, AuthoritativeRulesetDerivesSingle; intros. *)


Lemma RulesetDerivesCorrect_plus R S T :
  AuthoritativeRulesetDerives R S ->
  AuthoritativeRulesetDerives R T ->
  AuthoritativeRulesetDerives R (r_plus S T).
  unfold AuthoritativeRulesetDerives; intros.
  apply chain_flat_map with (RulesetStatesSingle (r_plus S T)); trivial.
  intros.
  dependent destruction H2.
  apply H. apply chain_step; assumption.
  apply H0. apply chain_step; assumption.
Qed.

Lemma RulesetDerivesCorrect_rule R p c :
  RulesetStates R p c ->
  AuthoritativeRulesetDerives R (r_rule p c).
  unfold AuthoritativeRulesetDerives; intros.

  (* "How did (r_rule p c) state a |- b? Just do the same thing using R" *)
  refine (chain_flat_map _ H0); intros.

  (* "How did (r_rule p c) singly-state a |- b? Only one way is possible" *)
  dependent destruction H1.

  (* "How did R state p |- c? Use the same chain to say p/ctx |- c/ctx" *)
  refine (chain_flat_map_mapf (λ f, f / ctx) _ H); intros.
  
  (* clear some things so induction doesn't get confused *)
  clear p c H H0 a b.

  (* "Which rule did R use to singly-state x |- y? Use that same rule" *)
  induction H1.
  apply rs_plus_left; assumption.
  apply rs_plus_right; assumption.

  (* Now all that's left is 2 specializations in series *)
  rewrite <- 2 (specialize_chain_correct ctx0 ctx).
  apply rs_rule.
Qed.

Theorem RulesetDerivesCorrect R S :
  RulesetDerives R S -> AuthoritativeRulesetDerives R S.

  intro H; induction H.
  apply RulesetDerivesCorrect_rule; assumption.
  apply RulesetDerivesCorrect_plus; assumption.
Qed.

Theorem RulesetDerivesComplete R S :
  AuthoritativeRulesetDerives R S -> RulesetDerives R S.
  unfold AuthoritativeRulesetDerives.
  (* break the goal down into parts... *)
  induction S; intros.
  {
    (* rule case *)
    apply rd_rule.
    apply H.
    rewrite <- (specialize_self_correct g) at 2.
    rewrite <- (specialize_self_correct g0) at 2.
    apply rs_rule.
  }
  {
    (* plus case *)
    apply rd_plus;
      [apply IHS1 | apply IHS2];
      intros; apply H;
      [apply rs_plus_left | apply rs_plus_right];
      assumption.
  }
  (* Show Proof. *)
Qed.


Class Context F C := {
    ctx_branch : F -> C -> C -> C
  ; ctx_formula :: Formula F
  }.

Definition ContextRelation := ∀ F C (_fc : Context F C), C -> C -> Prop.
Definition ContextRelationDerives
  (Premise Conclusion : ContextRelation)
  := ∀ F C (_fc : Context F C) a b,
  Conclusion F C _fc a b ->
     Premise F C _fc a b.

Inductive GenericContext :=
  | gc_use_subtree : VarIndex -> GenericContext
  | gc_branch :
      GenericFormula ->
      GenericContext ->
      GenericContext ->
      GenericContext
  .

Instance gcic : Context GenericFormula GenericContext := {
    ctx_branch := gc_branch
  }.

Definition gc_root_value (gc : GenericContext) : GenericFormula :=
  match gc with
  | gc_use_subtree i => gf_var i 
  | gc_branch x L R => x
  end.

Definition gc_child_left (gc : GenericContext) : GenericContext :=
  match gc with
  | gc_use_subtree i => gc_use_subtree (cons false i) 
  | gc_branch x L R => L
  end.

Definition gc_child_right (gc : GenericContext) : GenericContext :=
  match gc with
  | gc_use_subtree i => gc_use_subtree (cons true i) 
  | gc_branch x L R => R
  end.

Fixpoint gc_subtree (gc : GenericContext) (i : VarIndex) : GenericContext :=
  match i with
  | nil => gc
  | cons false tail => gc_subtree (gc_child_left gc) tail
  | cons true tail => gc_subtree (gc_child_right gc) tail 
  end.

Definition gc_get_value (gc : GenericContext) (i : VarIndex) : GenericFormula :=
  gc_root_value (gc_subtree gc i).

Fixpoint compose_gc_gf (gc : GenericContext) (gf : GenericFormula) : GenericFormula :=
  match gf with
  | gf_atom a => gf_atom a
  | gf_var i => gc_get_value gc i
  | gf_apply f x => gf_apply (compose_gc_gf gc f) (compose_gc_gf gc x) 
  end.

Fixpoint compose_gc_gc (A B : GenericContext) : GenericContext :=
  match B with
  | gc_use_subtree i => gc_subtree A i
  | gc_branch x L R => gc_branch
      (compose_gc_gf A x)
      (compose_gc_gc A L)
      (compose_gc_gc A R)
  end.

Inductive GenericContextChoices :=
  | gcc_gc : GenericContext -> GenericContextChoices
  | gcc_choice : GenericContextChoices -> GenericContextChoices -> GenericContextChoices
  .

Inductive GenericFormulaSpecializes F C {_fc : Context F C}
  : GenericFormula -> C -> F -> Prop :=
  | gfs_atom a ctx : GenericFormulaSpecializes
    (gf_atom a) ctx (f_atom a)
  | gfs_use x L R : GenericFormulaSpecializes
    (gf_var nil) (ctx_branch x L R) x
  | gfs_left x i L R :
    GenericFormulaSpecializes (gf_var i) L x ->
    GenericFormulaSpecializes
      (gf_var (cons false i)) (ctx_branch x L R) x
  | gfs_right x i L R :
    GenericFormulaSpecializes (gf_var i) R x ->
    GenericFormulaSpecializes
      (gf_var (cons true i)) (ctx_branch x L R) x
  | gfs_branch ctx pa pb ca cb :
    GenericFormulaSpecializes pa ctx ca ->
    GenericFormulaSpecializes pb ctx cb ->
    GenericFormulaSpecializes
      (gf_apply pa pb) ctx (f_apply ca cb)
  .

Inductive GenericContextSpecializes F C {_fc : Context F C}
  : GenericContext -> C -> C -> Prop :=
  | gcs_whole_tree ct : GenericContextSpecializes
    (gc_use_subtree nil) ct ct
  | gcs_left a b x0 x1 i :
    GenericContextSpecializes
      (gc_use_subtree i) a b ->
    GenericContextSpecializes
      (gc_use_subtree (cons false i)) (ctx_branch x0 a x1) b
  | gcs_branch x L R p lc rc xc :
    GenericFormulaSpecializes x p xc ->
    GenericContextSpecializes L p lc ->
    GenericContextSpecializes R p rc ->
    GenericContextSpecializes
      (gc_branch x L R) p (ctx_branch xc lc rc)
  .

Inductive GenericContextChoicesSpecializes F C {_fc : Context F C}
  : GenericContextChoices -> C -> C -> Prop :=
  | gccs_gc gc a b :
      GenericContextSpecializes gc a b -> 
      GenericContextChoicesSpecializes (gcc_gc gc) a b 
  | gccs_choice_left L R a b :
      GenericContextChoicesSpecializes L a b ->
      GenericContextChoicesSpecializes (gcc_choice L R) a b
  | gccs_choice_right L R a b :
      GenericContextChoicesSpecializes R a b ->
      GenericContextChoicesSpecializes (gcc_choice L R) a b
  .

Definition gc_to_cr (gc : GenericContext) : ContextRelation :=
  λ _ _ _, GenericContextSpecializes gc.
Definition gcc_to_cr (gcc : GenericContextChoices) : ContextRelation :=
  λ _ _ _, GenericContextChoicesSpecializes gcc.
(* Set Printing Implicit.
Print gc_to_cr. *)

Inductive GenericContextChoicesDerives (r : GenericContextChoices)
  : GenericContextChoices -> Prop :=
  | gccd_gc a b :
    GenericContextChoicesSpecializes r a b ->
    GenericContextChoicesDerives r (gcc_gc b)
  | gccd_choice s t :
    GenericContextChoicesDerives r s ->
    GenericContextChoicesDerives r t ->
    GenericContextChoicesDerives r (gcc_choice s t)
  .

Inductive ContextTransformation :=
  | ct_compose : ContextTransformation -> ContextTransformation -> ContextTransformation
  | ct_star : ContextTransformation -> ContextTransformation
  | ct_inverse : ContextTransformation -> ContextTransformation
  | ct_in_left : ContextTransformation -> ContextTransformation
  | ct_rotate_left : ContextTransformation
  | ct_swap : ContextTransformation
  | ct_drop : ContextTransformation
  | ct_formula_atom : ContextTransformation
  | ct_formula_branch : ContextTransformation
  .

Inductive ContextTransformationSpecializes F C {_fc : Context F C}
  : ContextTransformation -> C -> C -> Prop :=
  | cts_compose A B x y z :
    ContextTransformationSpecializes A x y ->
    ContextTransformationSpecializes B y z ->
    ContextTransformationSpecializes (ct_compose A B) x z
  | cts_star_refl A x :
    ContextTransformationSpecializes (ct_star A) x x
  | cts_star_chain A x y z :
    ContextTransformationSpecializes A x y ->
    ContextTransformationSpecializes (ct_star A) y z ->
    ContextTransformationSpecializes (ct_star A) x z
  | cts_inverse A x y :
    ContextTransformationSpecializes A x y ->
    ContextTransformationSpecializes (ct_inverse A) y x
  | cts_in_left A x y z w :
    ContextTransformationSpecializes A x y ->
    ContextTransformationSpecializes
      (ct_in_left A) (ctx_branch w x z) (ctx_branch w y z)
  | cts_rotate_left A B C x y :
    ContextTransformationSpecializes ct_rotate_left
      (ctx_branch x A (ctx_branch y B C))
      (ctx_branch y (ctx_branch x A B) C)
  | cts_swap A B x :
    ContextTransformationSpecializes ct_swap
      (ctx_branch x A B)
      (ctx_branch x B A)
  | cts_drop x A B :
    ContextTransformationSpecializes ct_drop
      (ctx_branch x A B)
      A
  | cts_formula_atom A :
    ContextTransformationSpecializes ct_formula_atom
      A
      (ctx_branch (f_atom 0) A A)
  | cts_formula_branch x y A B C :
    ContextTransformationSpecializes ct_formula_branch
      (ctx_branch y (ctx_branch x A B) C)
      (ctx_branch (f_apply x y) (ctx_branch x A B) C)
  .

Inductive CtRepresentsGc :
  ContextTransformation -> GenericContext -> Prop :=
  | ctrgc_compose A a B b :
      CtRepresentsGc A a ->
      CtRepresentsGc B b ->
      CtRepresentsGc (ct_compose A B) (compose_gc_gc a b)
  | ctrgc_inverse A a B b :
      CtRepresentsGc A a ->
      CtRepresentsGc B b ->
      CtRepresentsGc (ct_compose A B) (compose_gc_gc a b)
  .

(* Interactive Generic Formula or something *)
Inductive IGF :=
  | igf_apply : IGF -> IGF -> IGF
  | igf_atom : IGF
  | igf_popatom : IGF -> IGF
  | igf_var : IGF
  | igf_popvar : IGF -> IGF
  | igf_pushvar : IGF -> IGF -> IGF
  .


Fixpoint index_to_igf_atom (a : AtomIndex) : IGF :=
  match a with
  | 0 => igf_atom
  | S p => igf_popvar (index_to_igf_atom p)
  end.

Instance figf : Formula IGF := {
    f_atom := index_to_igf_atom
  ; f_apply := igf_apply
  }.

Fixpoint gf_increment_vars (gf : GenericFormula) : GenericFormula :=
  match gf with
  | gf_atom a => gf_atom a
  | gf_var v => gf_var (S v)
  | gf_apply a b => gf_apply (gf_increment_vars a) (gf_increment_vars b) 
  end.
Fixpoint gf_increment_atoms (gf : GenericFormula) : GenericFormula :=
  match gf with
  | gf_atom a => gf_atom (S a)
  | gf_var v => gf_var v
  | gf_apply a b => gf_apply (gf_increment_atoms a) (gf_increment_atoms b) 
  end.
Fixpoint gf_specialize_one (gf : GenericFormula) (x : GenericFormula) : GenericFormula :=
  match gf with
  | gf_atom a => gf_atom a
  | gf_var v => match v with
    | 0 => x
    | S p => gf_var p
    end
  | gf_apply a b => gf_apply (gf_specialize_one a x) (gf_specialize_one b x) 
  end.

Fixpoint igf_to_gf (igf : IGF) : GenericFormula :=
  match igf with
  | igf_apply f x => gf_apply (igf_to_gf f) (igf_to_gf x)
  | igf_atom => gf_atom 0
  | igf_popatom f => gf_increment_atoms (igf_to_gf f)
  | igf_var => gf_var 0
  | igf_popvar f => gf_increment_vars (igf_to_gf f)
  | igf_pushvar x f => gf_specialize_one (igf_to_gf f) (igf_to_gf x)
  end.
Fixpoint atom_to_canonical_igf (i : AtomIndex) : IGF :=
  match i with
  | 0 => igf_atom
  | S p => igf_popatom (atom_to_canonical_igf p)
  end.
Fixpoint var_to_canonical_igf (i : VarIndex) : IGF :=
  match i with
  | 0 => igf_var
  | S p => igf_popvar (var_to_canonical_igf p)
  end.
Fixpoint gf_to_canonical_igf (gf : GenericFormula) : IGF :=
  match gf with
  | gf_atom a => atom_to_canonical_igf a
  | gf_var v => var_to_canonical_igf v
  | gf_apply a b => igf_apply (gf_to_canonical_igf a) (gf_to_canonical_igf b)
  end.

Definition igf_stash A B := igf_pushvar A (igf_popvar B).

Inductive IgfUnfoldStep : IGF -> IGF -> Prop :=
  | its_forget_var A : IgfUnfoldStep (igf_stash igf_var A) A
  | its_forget_pop A B : IgfUnfoldStep (igf_stash (igf_popvar A) B) B
  | its_forget_apply A B C : IgfUnfoldStep
    (igf_stash [A B] C)
    (igf_stash A (igf_stash B C))
  (* | its_unfold_push_push A B C : IgfUnfoldStep
    (igf_pushvar (igf_pushvar A B) C)
    (igf_pushvar A (igf_pushvar B C)) *)
  | its_distribute_popvar A B : IgfUnfoldStep
    (igf_popvar [A B]) [(igf_popvar A) (igf_popvar B)]
  | its_distribute_popatom A B : IgfUnfoldStep
    (igf_popatom [A B]) [(igf_popatom A) (igf_popatom B)]
  .

Inductive IgfUhhhStep : IGF -> IGF -> Prop :=
  | ius_splay_apply A B C : IgfUhhhStep
    (igf_pushvar [A B] C)
    (igf_pushvar (igf_pushvar A (igf_pushvar B [_])) C)
    (igf_pushvar (igf_pushvar A [igf_var (igf_popvar B)]) C)
    (igf_pushvar (igf_pushvar B [(igf_popvar A) igf_var]) C)
    (igf_pushvar [A B] C)
  .

Lemma atoms_vars_unrelated A : gf_increment_vars
  (gf_increment_atoms A) = gf_increment_atoms
  (gf_increment_vars A).
  induction A; cbn; try (rewrite IHA1); try (rewrite IHA2); trivial.
Qed.

Lemma specialize_ignored A B : gf_specialize_one
  (gf_increment_vars A) B = A.
  induction A; cbn; try (rewrite IHA1); try (rewrite IHA2); trivial.
Qed.

(* Lemma igf_stash_ignored A B : igf_to_gf (igf_stash A B) = igf_to_gf B.
cbn.
  apply specialize_ignored.
Qed. *)

Lemma IgfUnfoldStep_Correct P C : IgfUnfoldStep P C -> (igf_to_gf P = igf_to_gf C).
  intro. destruct H; cbn; try apply specialize_ignored.
Qed.

Lemma IgfUnfoldStep_Complete igf : Chain IgfUnfoldStep igf
  (gf_to_canonical_igf (igf_to_gf igf)).
  
Qed.


Inductive IRule := ⇝*

Inductive IOp :=
  | iop_add_right_sibling : IGF -> IOp
  | iop_add_left_sibling : IGF -> IOp
  .

Record IRule {
  focused : IGF -> list IOp -> IRule

  }.














(* Inductive FormulaThunk F : Type :=
  | ft_done : F -> FormulaThunk F
  | ft_force_then : FormulaThunk F -> FTContinuation F -> FormulaThunk F
with FTContinuation F : Type :=
  | ft_then_done : FTContinuation F
  | ft_then_force_right_sibling_then : FormulaThunk F -> FTContinuation F -> FTContinuation F
  | ft_then_use_as_right_sibling_of_then : F -> FTContinuation F -> FTContinuation F
  . *)

Inductive FillableFormulaThunk F : Type :=
  | fft_any : FillableFormulaThunk F
  | fft_done : F -> FillableFormulaThunk F
  | fft_force_then : FillableFormulaThunk F -> FFTContinuation F -> FillableFormulaThunk F
with FFTContinuation F : Type :=
  | fft_then_done : FFTContinuation F
  | fft_then_force_right_sibling_then : FillableFormulaThunk F -> FFTContinuation F -> FFTContinuation F
  | fft_then_use_as_right_sibling_of_then : F -> FFTContinuation F -> FFTContinuation F
  .

Inductive SpecializationState F : Type :=
  | ss_premise_with_context : GenericFormula -> InfiniteContext F -> SpecializationState F
  | ss_conclusion : F -> SpecializationState F
  | ss_making_subformula : SpecializationState F -> SSContinuation F -> SpecializationState F
with SSContinuation F : Type :=
  | ss_then_done : SSContinuation F
  | ss_then_make_right_sibling_then : SpecializationState F -> SSContinuation F -> SSContinuation F
  | ss_then_use_as_right_sibling_of_then : F -> SSContinuation F -> SSContinuation F
  .

Fixpoint SSSpecializes F {_f : Formula F}
  (SS : SpecializationState F) (xs:InfiniteContext F) (output: F) : Prop :=
  match SS with
  | ss_premise_with_context gf xs0 => ((xs0 = context_arbitrary _) ∧ Specializes gf xs output) ∨ (∃ h t, xs0 = (context_cons h t) ∧ SSSpecializes gf (context_cons h ))
  | ss_conclusion f => output = f
  | ss_making_subformula sg cont => ∃ g,
    SSSpecializes sg xs g ∧ SSCSpecializes g cont xs output
  end
with SSCSpecializes F {_f : Formula F}
  (input : F) (SSC : SSContinuation F) (xs:InfiniteContext F) (output: F) : Prop :=
  match SSC with
  | ss_then_done => True
  | ss_then_make_right_sibling_then sb cont => ∃ b, SSSpecializes sb xs b ∧ output = (f_apply input b)
  | ss_then_use_as_right_sibling_of_then a cont => output = (f_apply a input)
  end
  .
  
(* Inductive SSSpecializes F {_f : Formula F}
  : SpecializationState F -> InfiniteContext F -> F -> Prop
  :=
  | sss_premise_with_context gf xs rest f :
    (* Specializes gf (xs++rest) f -> *)
    SSSpecializes (ss_premise_with_context gf xs) rest f
  | sss_conclusion f xs : SSSpecializes (ss_conclusion f) xs f
  | sss_making_subformula ss cont xs f g : 
    SSSpecializes ss xs g ->
    SSCSpecializes f cont xs g ->
    SSSpecializes (ss_making_subformula ss cont) xs g
with SSCSpecializes F {_f : Formula F}
  : F -> SSContinuation F -> InfiniteContext F -> F -> Prop :=
  | sss_then_done f xs : SSCSpecializes f (ss_then_done F) xs f
  | sss_then_make_right_sibling_then f sg g cont xs :
      SSSpecializes sg xs g ->
      SSCSpecializes f (ss_then_make_right_sibling_then sg cont) xs (f_apply g f)
  | sss_then_use_as_right_sibling_of_then f g cont xs :
      SSCSpecializes f (ss_then_use_as_right_sibling_of_then g cont) xs (f_apply g f)
  . *)

Inductive SpecializationStep F {_f : Formula F} : SpecializationState F -> SpecializationState F -> Prop :=
  (* | sst_specialize p x xs : SpecializationStep (ss_premise_with_context p xs) (ss_premise_with_context p (context_cons x xs)) *)
  (* | sst_commit ss : SpecializationStep ss (ss_making_subformula ss (ss_then_done _)) *)
  (* | sst_finish f : SpecializationStep (ss_making_subformula (ss_conclusion f) (ss_then_done _)) (ss_conclusion f) *)
  | sst_eliminate_usage x xs cont : SpecializationStep
    (ss_making_subformula (ss_premise_with_context gf_usage (context_cons x xs)) cont)
    (ss_making_subformula (ss_conclusion x) cont)
  | sst_eliminate_pop f x xs cont : SpecializationStep
    (ss_making_subformula (ss_premise_with_context (gf_pop f) (context_cons x xs)) cont)
    (ss_making_subformula (ss_premise_with_context f xs) cont)
  | sst_atom a xs cont : SpecializationStep
    (ss_making_subformula (ss_premise_with_context (gf_atom a) xs) cont)
    (ss_making_subformula (ss_conclusion (f_atom a)) cont)
  | sst_branch a b xs cont : SpecializationStep
    (ss_making_subformula (ss_premise_with_context (gf_apply a b) xs) cont)
    (ss_making_subformula (ss_premise_with_context a xs) (ss_then_make_right_sibling_then (ss_premise_with_context b xs) cont))
  | sst_branch2 a b cont : SpecializationStep
    (ss_making_subformula (ss_conclusion a) (ss_then_make_right_sibling_then b cont))
    (ss_making_subformula b (ss_then_use_as_right_sibling_of_then a cont))
  | sst_branch3 a b cont : SpecializationStep
    (ss_making_subformula (ss_conclusion b) (ss_then_use_as_right_sibling_of_then a cont))
    (ss_making_subformula (ss_conclusion (f_apply a b)) cont)
  .

Lemma SpecializationStepsValid F {_f : Formula F} P C ctx f : SpecializationStep P C -> SSSpecializes C ctx f -> SSSpecializes P ctx f.
  intros step H. destruct step; cbn in *.
  {
    destruct H as (g, (eq, sc)).
    exists g; split; trivial.
  }
  {
    destruct H as (g, (uh, (hg,(c,d)))).
    exists g; split; trivial.
    rewrite d.

    apply sss_making_subformula with f.
    apply sss_premise_with_context.
  }

  {}
  {}
Qed.

  

Inductive WorkableGenericFormulaWithContext :=
  | wgr_with_context : WorkableContext -> WorkableGenericFormula -> WorkableGenericFormulaWithContext
with WorkableGenericFormula : Type :=
  | wgr_atom : AtomIndex -> WorkableGenericFormula
  (* | wgr_pop : WorkableGenericFormula *)
  (* | wgr_with_context n : WorkableContext n -> WorkableGenericFormula n -> WorkableGenericFormula 0 *)
  | wgr_chain : WorkableGenericFormula -> WorkableContinuation -> WorkableGenericFormula
with WorkableContinuation : Type :=
  | done : WorkableContinuation
  | make_right_sibling : WorkableGenericFormula -> WorkableContinuation -> WorkableContinuation
  (* | combine : WorkableGenericFormula -> WorkableGenericFormula -> WorkableContinuation -> WorkableContinuation *)
with WorkableContext : Type := 
  | wc_rest : WorkableContext
  | wc_cons : WorkableGenericFormula -> WorkableContext -> WorkableContext
  .

Fixpoint wgr_to_gr (wgr: WorkableGenericFormula) : GenericFormula :=
  match wgr with 
  | wgr_atom a => gf_atom a 
  (* | wgr_with_context n ctx cont => wgr_to_gr () *)
  | wgr_chain f cont => wcont_to_gr (wgr_to_gr f) cont
  end
with wcont_to_gr (f: GenericFormula) (wcont: WorkableContinuation) : GenericFormula :=
  match wcont with
  | done => f
  | make_right_sibling g cont => gf_apply f (wgr_to_gr g)
  end
  .


Inductive WorkableRule :=
  | wr_
  .

Inductive WorkableRuleset :=
  | wrs_rule : WorkableRule -> WorkableRuleset
  | wrs_plus : WorkableRuleset -> WorkableRuleset -> WorkableRuleset
  .
Inductive WgrRepresents
  : WorkableGenericFormula -> GenericFormula -> Prop
  :=
  .
Inductive PartiallySpecializes
  : WorkableGenericFormula -> (* which may already contain a InfiniteContext WorkableGenericFormula *)
    WorkableGenericFormula ->
    Prop
  :=
  .
   

(* Inductive GenericFormula : Type :=
  | gf_usage : GenericFormula
  | gf_var : GenericFormula -> GenericFormula
  (* | gf_let : GenericFormula -> GenericFormula -> GenericFormula *)
  | gf_pop : GenericFormula -> GenericFormula
  | gf_apply : GenericFormula -> GenericFormula -> GenericFormula
  . *)

(* Inductive Ruleset : Type :=
  | r_implies : Ruleset -> Ruleset -> Ruleset
  | r_var : Ruleset *)

(* 
Inductive Locations : Type :=
  | l_nowhere : Locations
  | l_here : Locations
  | l_apply : Locations -> Locations -> Locations
  .

Inductive Ruleset : Type :=
  | r_atom : AtomIndex -> Locations -> Ruleset
  | r_var : Locations -> Ruleset
  | r_and : Ruleset -> Ruleset -> Ruleset
  | r_or : Ruleset -> Ruleset -> Ruleset
  . *)

Inductive Ruleset : Type :=
  | r_atom : AtomIndex -> Ruleset
  | r_apply : Ruleset -> Ruleset -> Ruleset
  | r_usage : Ruleset
  | r_pop : Ruleset -> Ruleset
  | r_var : Ruleset -> Ruleset
  | r_let : Ruleset -> Ruleset -> Ruleset
  (* | r_and : Ruleset -> Ruleset -> Ruleset *)
  | r_or : Ruleset -> Ruleset -> Ruleset
  .

Inductive RulesetIncludesFormula : Ruleset -> Formula -> Prop :=
  | rif_atom a :
      RulesetIncludesFormula (r_atom a) (f_atom a)
  | rif_apply A B a b :
      RulesetIncludesFormula A a ->
      RulesetIncludesFormula B b ->
      RulesetIncludesFormula (r_apply A B) (f_apply a b)    
  | rif_usage F f :
      RulesetIncludesFormula F f ->
      RulesetIncludesFormula (r_let F r_usage) f
  | rif_pop R F f :
      RulesetIncludesFormula F f ->
      RulesetIncludesFormula (r_let R (r_pop F)) f
  | rif_specialize R F g :
      RulesetIncludesFormula (r_let F R) g ->
      RulesetIncludesFormula (r_var R) g
  | rif_let_apply X A B f :
      RulesetIncludesFormula (r_apply (r_let X A) (r_let X B)) f ->
      RulesetIncludesFormula (r_let X (r_apply A B)) f
  (* | rif_let_let X A B f :
      RulesetIncludesFormula (r_let (r_let X A) (r_let X B)) f ->
      RulesetIncludesFormula (r_let X (r_let A B)) f *)
  | rif_or_left F G f :
      RulesetIncludesFormula F f ->
      RulesetIncludesFormula (r_or F G) f
  | rif_or_right F G f :
      RulesetIncludesFormula F f ->
      RulesetIncludesFormula (r_or G F) f
  .


CoInductive InfiniteContext : Type :=
  | ctx_cons : Formula -> InfiniteContext -> InfiniteContext.
Notation "x :: xs" := (ctx_cons x xs).
CoFixpoint ascending_context n : InfiniteContext := (f_atom n) :: ascending_context (S n).
Definition default_context := ascending_context 0.

(* Definition Rule := Formula. *)
Definition Ruleset := Formula.
Definition r_atom_apply : AtomIndex := 0.
Definition r_atom_var : AtomIndex := 1.
Definition r_atom_let : AtomIndex := 2.
Definition r_atom_pop : AtomIndex := 3.
Definition r_atom_usage : AtomIndex := 4.
Definition r_atom_implies : AtomIndex := 5.
Definition r_atom_plus : AtomIndex := 6.
(* Definition r_atom_times : AtomIndex := 7.
Definition r_atom_star : AtomIndex := 8. *)

Definition r_apply a b := [(f_atom r_atom_apply) a b].
Definition r_var a := [(f_atom r_atom_var) a].
Definition r_let a b := [(f_atom r_atom_let) a b].
Definition r_pop a := [(f_atom r_atom_pop) a].
Definition r_usage := (f_atom r_atom_usage).
Definition r_implies a b := [(f_atom r_atom_implies) a b].
Definition r_plus a b := [(f_atom r_atom_plus) a b].
(* Definition r_times a b := [(f_atom r_atom_times) a b].
Definition r_star a := [(f_atom r_atom_star) a]. *)

(* Fixpoint r_subst : Ruleset -> Formula -> Ruleset := *)
(* Inductive RSubst : Ruleset -> Ruleset -> Ruleset -> Prop :=
  | rs_usage f : RSubst r_usage f f
  | rs_pop r f : RSubst (r_pop r) f r
  | rs_apply a b f a2 b2 :
    RSubst a f a2 ->
    RSubst b f b2 ->
    RSubst (r_apply a b) f (r_apply a2 b2)
  .
Inductive Incatoms : Formula -> Formula -> Prop :=
  | ia_atom a : Incatoms (f_atom a) (f_atom (S a))
  | ia_apply a b a2 b2 :
    Incatoms a a2 ->
    Incatoms b b2 ->
    Incatoms [a b] [a2 b2]
  .

Inductive RulesetIncludesFormula : Ruleset -> Formula -> Prop :=
  | rif_usage : RulesetIncludesFormula r_usage (f_atom 0)
  | rif_var r f g : RulesetIncludesFormula (r_let r g) f ->
    RulesetIncludesFormula (r_var r) f
  | rif_let r x r2 f : RSubst r x r2 ->
    RulesetIncludesFormula r2 f ->
    RulesetIncludesFormula (r_let r x) f
  | rif_pop r a b :
    Incatoms a b ->
    RulesetIncludesFormula r a ->
    RulesetIncludesFormula (r_pop r) b
  . *)


Inductive RulesetIncludesFormula : Ruleset -> InfiniteContext -> Formula -> Prop :=
  | rif_usage x xs :
      RulesetIncludesFormula r_usage (x::xs) x
  | rif_var r x xs f :
      RulesetIncludesFormula r (x::xs) f ->
      RulesetIncludesFormula (r_var r) xs f
  | rif_let r rx x xs f :
      RulesetIncludesFormula rx xs x ->
      RulesetIncludesFormula r (x::xs) f ->
      RulesetIncludesFormula (r_let r x) xs f
  | rif_pop r x xs f :
      RulesetIncludesFormula r xs f ->
      RulesetIncludesFormula (r_pop r) (x::xs) f
  .

Inductive RulesetIncludesImplication
      : Ruleset -> InfiniteContext -> Formula -> Formula -> Prop :=
  | rii_var r x xs p c :
      RulesetIncludesImplication r (x::xs) p c ->
      RulesetIncludesImplication (r_var r) xs p c
  | rii_let r rx x xs p c :
      RulesetIncludesFormula rx xs x ->
      RulesetIncludesImplication r (x::xs) p c ->
      RulesetIncludesImplication (r_let r x) xs p c
  | rii_implies rp rc xs p c :
      RulesetIncludesFormula rp xs p ->
      RulesetIncludesFormula rc xs c ->
      RulesetIncludesImplication (r_implies rp rc) xs p c
  | rii_plus_left ra rb xs p c :
      RulesetIncludesImplication ra xs p c ->
      RulesetIncludesImplication (r_plus ra rb) xs p c
  | rii_plus_right ra rb xs p c : RulesetIncludesImplication rb xs p c ->
      RulesetIncludesImplication (r_plus ra rb) xs p c
  (* | rii_times rab rbc xs a b c :
      RulesetIncludesImplication rab xs a b ->
      RulesetIncludesImplication rbc xs b c ->
      RulesetIncludesImplication (r_times rab rbc) xs a c
  | rii_star_none r xs f :
      RulesetIncludesImplication (r_star r) xs f f
  | rii_star_succ r xs p c :
      RulesetIncludesImplication (r_times r (r_star r)) xs p c ->
      RulesetIncludesImplication (r_star r) xs p c *)
      .
  
Inductive WellFormedFormula : Ruleset -> Prop :=
  | wff_usage :
      WellFormedFormula r_usage
  | wff_var r :
      WellFormedFormula r ->
      WellFormedFormula (r_var r)
  | wff_let r x :
      WellFormedFormula r ->
      WellFormedFormula x ->
      WellFormedFormula (r_let r x)
  | wff_pop r :
      WellFormedFormula r ->
      WellFormedFormula (r_pop r)
  .


Inductive WellFormedRuleset : Ruleset -> Prop :=
  | wfr_var r :
      WellFormedRuleset r ->
      WellFormedRuleset (r_var r)
  | wfr_implies rp rc :
      WellFormedFormula rp ->
      WellFormedFormula rc ->
      WellFormedRuleset (r_implies rp rc)
  | wfr_plus ra rb :
      WellFormedRuleset ra ->
      WellFormedRuleset rb ->
      WellFormedRuleset (r_plus ra rb)
  (* | wfr_times rab rbc :
      WellFormedRuleset rab ->
      WellFormedRuleset rbc ->
      WellFormedRuleset (r_times rab rbc)
  | wfr_star r :
      WellFormedRuleset r ->
      WellFormedRuleset (r_star r) *)
  .

(* Inductive RuleIncludesImplication
      : Rule -> Formula -> Formula -> Prop :=
  | rif_var r f p c : RuleIncludesImplication (r_let r f) p c ->
    RuleIncludesImplication (r_var r) p c
  | rif_let r p c : RuleIncludesImplication (r_subst r g) p c ->
    RuleIncludesImplication (r_let r g) p c
  | rii_implies rp rc p c : uhh -> RuleIncludesImplication p c
  . *)
(* 
Inductive RulesetIncludesImplication
      : Ruleset -> Formula -> Formula -> Prop :=
  | rii_var r f p c : RulesetIncludesImplication (r_let r f) p c ->
    RulesetIncludesImplication (r_var r) p c
  | rii_let r x r2 p c : RSubst r x r2 ->
    RulesetIncludesImplication r2 p c ->
    RulesetIncludesImplication (r_let r x) p c
  | rii_implies rp rc p c : uhh -> RulesetIncludesImplication p c
  (* | rii_rule r p c : RuleIncludesImplication r p c ->
      RulesetIncludesImplication r p c *)
  | rii_plus_left ra rb p c : RulesetIncludesImplication ra p c ->
      RulesetIncludesImplication (r_plus ra rb) p c
  | rii_plus_right ra rb p c : RulesetIncludesImplication rb p c ->
      RulesetIncludesImplication (r_plus ra rb) p c
  | rii_times rab rbc a b c :
      RulesetIncludesImplication rab a b ->
      RulesetIncludesImplication rbc b c ->
      RulesetIncludesImplication (r_times rab rbc) a c
  | rii_star_none r f :
      RulesetIncludesImplication (r_star r) f f
  | rii_star_succ r p c :
      RulesetIncludesImplication (rii_times r (r_star r)) p c
      RulesetIncludesImplication (r_star r) p c
      . *)

(* Definition RuleDerives P C : Prop :=
  ∀(x y : Formula), RuleIncludesImplication C x y -> RuleIncludesImplication P x y. *)


(* Parameter RuleDerivesRules : Ruleset.

Theorem RuleDerivesRulesValid P C :
  (RuleIncludesImplication RuleDerivesRules P C) -> RuleDerives P C.

Qed.

Theorem RuleDerivesRulesComplete P C :
  RuleDerives P C -> (RuleIncludesImplication RuleDerivesRules P C)

Qed. *)

Definition RulesetDerives P C : Prop :=
  ∀ ctx (x y : Formula),
    RulesetIncludesImplication C ctx x y ->
    RulesetIncludesImplication P ctx x y.

Parameter ProofRules : Ruleset.



Theorem ProofRulesValid P C :
  (RulesetIncludesImplication ProofRules default_context P C) -> RulesetDerives P C.
  intro e; induction e; trivial.

Qed.

Lemma ProofRulesComplete_WellFormed P C :
  WellFormedRuleset C ->
  RulesetDerives P C -> (RulesetIncludesImplication ProofRules default_context P C).
  intros.
  (* break down into individual rules, then reabstract each rule *)
  induction H.
  {}
  {
  (* { reabstract} *)
  }
  {
    (* plus case: *)
    (* "if P derives A+B then P derives A and P derives B, so, 
        recurse to get those proofs and then combine them" *)
  }
  (* {
    (* times case: *)
    (* "if P derives A*B then ??????? TODO" *)
  }
  {
     (* star case: *)
     (* ?????? *)
  } *)

  unfold RulesetDerives in H.
  specialize (H _ P C).
  intro e; induction e; trivial.
Qed.

Theorem ProofRulesComplete P C :
  RulesetDerives P C -> (RulesetIncludesImplication ProofRules default_context P C).
  intro.
  (* break down into individual rules, then reabstract each rule *)
  induction C.

  unfold RulesetDerives in H.
  specialize (H _ P C).
  intro e; induction e; trivial.
Qed.

  (RulesetIncludesImplication ProofRules P C) ∨ ¬(RulesetDerives P C).

Qed.

Theorem ProofRulesComplete P C :
  ¬(RulesetDerives P C ∧ ¬RulesetIncludesImplication ProofRules P C).
  
Qed.

