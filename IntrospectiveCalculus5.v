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

Inductive Program :=
  | p_compose : Program -> Program -> Program
  | p_iterate : Program -> Program
  | p_choice : Program -> Program -> Program
  | p_inverse : Program -> Program
  | p_in_left : Program -> Program
  | p_rotate_left : Program
  | p_swap : Program
  | p_dup : Program
  | p_drop : Program
  (* | p_branch : Program *)
  .

Notation "P '∘' Q" := (p_compose P Q) (at level 35, right associativity). 

CoInductive ProgramContext Value :=
  (* | pc_nil : ProgramContext Value *)
  | pc_value : Value -> ProgramContext Value
  | pc_branch : ProgramContext Value -> ProgramContext Value -> ProgramContext Value
  .
(* Arguments pc_nil {Value}. *)

(* Print PC2_. *)

(* Class ProgramContext C := {
      pc_branch : C -> C -> C
    ; pc_nil : C
  }. *)
Inductive ProgramExecution Value
  : Program -> ProgramContext Value -> ProgramContext Value -> Prop :=
  | pe_compose A B x y z :
    ProgramExecution A y z ->
    ProgramExecution B x y ->
    ProgramExecution (A ∘ B) x z
  | pe_iterate_refl A x :
    ProgramExecution (p_iterate A) x x
  | pe_iterate_chain A x y z :
    ProgramExecution A y z ->
    ProgramExecution (p_iterate A) x y ->
    ProgramExecution (p_iterate A) x z
  | pe_choice_left A B x y :
    ProgramExecution A x y ->
    ProgramExecution (p_choice A B) x y
  | pe_choice_right A B x y :
    ProgramExecution B x y ->
    ProgramExecution (p_choice A B) x y
  | pe_inverse A x y :
    ProgramExecution A x y ->
    ProgramExecution (p_inverse A) y x
  | pe_in_left A x y z :
    ProgramExecution A x y ->
    ProgramExecution
      (p_in_left A) (pc_branch x z) (pc_branch y z)
  | pe_rotate_left A B C :
    ProgramExecution p_rotate_left
      (pc_branch A (pc_branch B C))
      (pc_branch (pc_branch A B) C)
  | pe_swap A B :
    ProgramExecution p_swap
      (pc_branch A B)
      (pc_branch B A)
  | pe_dup A :
    ProgramExecution p_dup A (pc_branch A A)
  | pe_drop A B :
    ProgramExecution p_drop (pc_branch A B) A
  (* | pe_branch : ProgramExecution p_branch pc_nil (pc_branch pc_nil pc_nil) *)
  .

Definition AuthoritativeProgramDerives R S :=
  ∀ Val a b, @ProgramExecution Val S a b -> @ProgramExecution Val R a b.
Definition ProgramImplements P (relation : ∀ V (a b : ProgramContext V), Prop) :=
  ∀ V a b, @ProgramExecution V P a b <-> relation V a b.
Definition ProgramsEquivalent R S :=
  AuthoritativeProgramDerives R S ∧ AuthoritativeProgramDerives S R.

Inductive VarExecution Value
  : VarIndex -> ProgramContext Value -> ProgramContext Value -> Prop :=
  | ve_nil c : VarExecution nil c c
  | ve_left tail a b c :
    VarExecution tail a c ->
    VarExecution (cons false tail) (pc_branch a b) c
  | ve_right tail a b c :
    VarExecution tail b c ->
    VarExecution (cons true tail) (pc_branch a b) c
  .

Inductive DeterministicProgram :=
  | dp_var : VarIndex -> DeterministicProgram
  | dp_branch : DeterministicProgram -> DeterministicProgram -> DeterministicProgram
  .
Inductive DeterministicProgramExecution Value
  : DeterministicProgram -> ProgramContext Value -> ProgramContext Value -> Prop :=
  | dpe_var i a b : @VarExecution Value i a b
    -> DeterministicProgramExecution (dp_var i) a b
  | dpe_branch L R a lb rb :
    DeterministicProgramExecution L a lb ->
    DeterministicProgramExecution R a rb ->
    DeterministicProgramExecution (dp_branch L R) a (pc_branch lb rb)
  .

Definition dp_child_left (dp : DeterministicProgram) : DeterministicProgram :=
  match dp with
  | dp_var i => dp_var (cons false i) 
  | dp_branch L R => L
  end.

Definition dp_child_right (dp : DeterministicProgram) : DeterministicProgram :=
  match dp with
  | dp_var i => dp_var (cons true i) 
  | dp_branch L R => R
  end.

Fixpoint dp_get_subtree (dp : DeterministicProgram) (i : VarIndex) : DeterministicProgram :=
  match i with
  | nil => dp
  | cons false tail => dp_get_subtree (dp_child_left dp) tail
  | cons true tail => dp_get_subtree (dp_child_right dp) tail 
  end.

Fixpoint dp_compose (a b : DeterministicProgram) : DeterministicProgram :=
  match a with
  | dp_var i => dp_get_subtree b i
  | dp_branch L R => dp_branch (dp_compose L b) (dp_compose R b)
  end.

Definition p_canonical_branch (a b : Program) : Program :=
  ((p_in_left a) ∘ p_swap) ∘ ((p_in_left b) ∘ p_dup)
  .

(* Create HintDb simple_programs. *)

Ltac autouse_shelving_db steps db :=
  (* unshelve debug eauto 99 with db. *)
  idtac steps; match steps with
    | S ?p => try ((progress (unshelve eauto 99 with db));
      autouse_shelving_db p db)
    | _ => idtac "Warning: steps ran out"
  end.
  (* tryif (idtac steps; guard steps <= 0)
    then (idtac "Warning: steps ran out")
    else (
      ). *)
Ltac shelving_db_entry tactic :=
  (progress (tactic)); shelve.

(* Create HintDb shelve.
Hint Extern 5 => shelve : shelve. *)
Create HintDb break_down_executions.
Hint Extern 5 => progress ltac:(
  match goal with
  | H : ProgramExecution ?P _ _ |- _ =>
    lazymatch (eval hnf in P) with
    | (p_compose _ _) => idtac
    | (p_iterate _) => idtac
    | (p_choice _ _) => idtac
    | (p_inverse _) => idtac
    | (p_in_left _) => idtac
    | p_rotate_left => idtac
    | p_swap => idtac
    | p_dup => idtac
    | p_drop => idtac
    end; dependent destruction H
  end); shelve
: break_down_executions.
Hint Extern 2 (ProgramExecution _ _ _) => progress constructor; shelve
: break_down_executions.
Hint Extern 1 (ProgramExecution (_ ∘ p_dup) ?a _) =>
progress ltac:(
  apply pe_compose with (pc_branch a a)
); shelve
: break_down_executions.
Hint Extern 1 (ProgramExecution (_ ∘ p_drop) (pc_branch ?a _) _) =>
progress ltac:(
  apply pe_compose with a
); shelve
: break_down_executions.
Hint Extern 1 (ProgramExecution (_ ∘ p_swap) (pc_branch ?a ?b) _) =>
progress ltac:(
  apply pe_compose with (pc_branch b a)
); shelve
: break_down_executions.
Ltac break_down_executions :=
  autouse_shelving_db 20 ident:(break_down_executions); trivial.
(* Ltac build_executions := solve [repeat econstructor; eassumption]. *)

Ltac split_and_break_down_peq :=
  unfold ProgramsEquivalent, AuthoritativeProgramDerives;
  split; intros; break_down_executions; try (repeat econstructor; eassumption).
(* Ltac progress_wrapper tactic := progress tactic. *)
(* Lemma test : True.
  progress_wrapper ltac:(match goal with | |- _ => exfalso end).
  progress ltac:(match goal with | |- _ => exfalso end). *)
Definition p_id := (p_inverse p_dup) ∘ p_dup.
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
(* Lemma compose_p_id :  *)
Hint Extern 5 => progress ltac:(
  match goal with
  | H : ProgramExecution p_id _ _ |- _ => apply p_id_correct in H; rewrite H
  end
); shelve
: break_down_executions.
Hint Extern 5 (ProgramExecution p_id ?a ?a)
=> solve [apply p_id_correct; reflexivity]
: break_down_executions.

Definition p_dropleft := p_drop ∘ p_swap.
Lemma pe_dropleft V A B : @ProgramExecution V p_dropleft (pc_branch A B) B.
  unfold p_dropleft.
  break_down_executions.
Qed.
Hint Immediate pe_dropleft : break_down_executions.
Hint Extern 1 (ProgramExecution (_ ∘ p_dropleft) (pc_branch _ ?b) _) =>
progress ltac:(
  apply pe_compose with b
); shelve
: break_down_executions.

Fixpoint p_canonical_var (i : VarIndex) : Program :=
  match i with
  | nil => p_id
  | cons false tail => (p_canonical_var tail) ∘ p_drop
  | cons true tail => (p_canonical_var tail) ∘ p_dropleft
  end.

Fixpoint p_canonical_dp (dp : DeterministicProgram) : Program :=
  match dp with
  | dp_var i => p_canonical_var i
  | dp_branch L R => p_canonical_branch (p_canonical_dp L) (p_canonical_dp R)
  end.

Hint Extern 1 =>
  match goal with
  | H : ProgramExecution (p_canonical_branch _ _) _ _ |- _ =>
          unfold p_canonical_branch in H
  end
: break_down_executions.

Lemma p_canonical_var_matches Value i a b :
  ProgramExecution (p_canonical_var i) a b <->
  @VarExecution Value i a b.
  refine ((fix f (i : VarIndex) a b :
      ProgramExecution (p_canonical_var i) a b <->
    @VarExecution Value i a b := 
    match i with
    | nil => _
    | cons false tail => _
    | cons true tail => _
    end) i a b); clear i0 a0 b0; split; intro.
  {
    break_down_executions.
    apply ve_nil.
  }
  {
    dependent destruction H.
    unfold p_canonical_var.
    break_down_executions.
  }
  {
    break_down_executions.
    apply ve_right. apply f. assumption.
  }
  {
    dependent destruction H.
    unfold p_canonical_var.
    break_down_executions.
    apply f; assumption.
  }
  {
    break_down_executions.
    apply ve_left. apply f. assumption.
  }
  {
    dependent destruction H.
    unfold p_canonical_var.
    break_down_executions.
    apply f; assumption.
  }
Qed.


Lemma p_canonical_dp_matches Value dp a b :
  ProgramExecution (p_canonical_dp dp) a b <->
  @DeterministicProgramExecution Value dp a b.
  refine ((fix f dp a b :
      ProgramExecution (p_canonical_dp dp) a b <->
    @DeterministicProgramExecution Value dp a b := 
    match dp with
    | dp_var i => _
    | dp_branch L R => _
    end) dp a b); clear dp0 a0 b0;
  (* induction dp; *)
    split; intro.
    
  (* induction dp. *)
  {
    apply dpe_var.
    apply p_canonical_var_matches. assumption.
  }
  {
    dependent destruction H.
    apply p_canonical_var_matches. assumption.
  }
  {
    break_down_executions.
    apply dpe_branch; apply f; assumption.
  }
  {
    dependent destruction H.
    repeat econstructor; apply f; assumption.
  }
Qed.

Fixpoint pc_dp (dp : DeterministicProgram) : ProgramContext VarIndex :=
  match dp with
  | dp_var i => pc_value i
  | dp_branch L R => pc_branch (pc_dp L) (pc_dp R)
  end.

Inductive SimpleProgramStep1 :=
  | sps1_rotate_left
  | sps1_rotate_left_in_left
  | sps1_swap
  | sps1_swap_in_left
  | sps1_dup
  | sps1_drop
  .

Inductive SimpleProgramStep :=
  | sps_forwards : SimpleProgramStep1 -> SimpleProgramStep
  | sps_backwards : SimpleProgramStep1 -> SimpleProgramStep
  .

Inductive SimpleProgramTree :=
  | spt_step : SimpleProgramStep -> SimpleProgramTree
  | spt_compose : SimpleProgramTree -> SimpleProgramTree -> SimpleProgramTree
  .

Definition SimpleProgramList := list SimpleProgramStep.

Definition p_sps1 sps1 :=
  match sps1 with
  | sps1_rotate_left => p_rotate_left
  | sps1_rotate_left_in_left => p_in_left p_rotate_left
  | sps1_swap => p_swap
  | sps1_swap_in_left => p_in_left p_swap
  | sps1_dup => p_dup
  | sps1_drop => p_drop
  end.

Definition p_sps sps :=
  match sps with 
  | sps_forwards s => p_sps1 s
  | sps_backwards s => p_inverse (p_sps1 s)
  end.

Definition sps_inverse sps :=
  match sps with 
  | sps_forwards s => sps_backwards s
  | sps_backwards s => sps_forwards s
  end.
Lemma sps_inverse_correct sps : ProgramsEquivalent
  (p_sps (sps_inverse sps))
  (p_inverse (p_sps sps)).
  destruct sps; split_and_break_down_peq.
Qed.

Fixpoint p_spt spt :=
  match spt with 
  | spt_step s => p_sps s
  | spt_compose a b => (p_spt a) ∘ (p_spt b)
  end.

Fixpoint p_spl spl :=
  match spl with 
  | nil => p_id
  | cons x xs => (p_spl xs) ∘ (p_sps x)
  end.

Create HintDb break_down_peq.
Ltac break_down_peq :=
  autouse_shelving_db 20 ident:(break_down_peq); trivial.

Lemma peq_rotate A B C : ProgramsEquivalent
  ((A ∘ B) ∘ C) (A ∘ (B ∘ C)).
  split_and_break_down_peq.
Qed.
Hint Immediate peq_rotate : break_down_peq.
Lemma peq_sym A B :
  ProgramsEquivalent A B ->
  ProgramsEquivalent B A.
  split_and_break_down_peq; apply H; assumption.
Qed.
Lemma peq_trans A B C :
  ProgramsEquivalent A B ->
  ProgramsEquivalent B C ->
  ProgramsEquivalent A C.
  split_and_break_down_peq.
  apply H. apply H0. assumption.
  apply H0. apply H. assumption.
Qed.
Lemma peq_compatibility_left A1 A2 B :
  ProgramsEquivalent A1 A2 ->
  ProgramsEquivalent (A1 ∘ B) (A2 ∘ B).
  split_and_break_down_peq.
  econstructor; [apply H|]; eassumption.
  econstructor; [apply H|]; eassumption.
Qed.
Lemma peq_compatibility_right A B1 B2 :
  ProgramsEquivalent B1 B2 ->
  ProgramsEquivalent (A ∘ B1) (A ∘ B2).
  split_and_break_down_peq.
  econstructor; [|apply H]; eassumption.
  econstructor; [|apply H]; eassumption.
Qed.
Lemma peq_compatibility_both A1 A2 B1 B2 :
  ProgramsEquivalent A1 A2 ->
  ProgramsEquivalent B1 B2 ->
  ProgramsEquivalent (A1 ∘ B1) (A2 ∘ B2).
  split_and_break_down_peq.
  econstructor; [apply H | apply H0]; eassumption.
  econstructor; [apply H | apply H0]; eassumption.
Qed.
Lemma peq_inverse_equivalent A B :
  ProgramsEquivalent A B <->
  ProgramsEquivalent (p_inverse A) (p_inverse B).
  split_and_break_down_peq.
  apply H; assumption.
  apply H; assumption.
  split; intros.
  {
    assert (ProgramExecution (p_inverse A) b a).
    apply H. apply pe_inverse. assumption.
    break_down_executions.
  }
  {
    assert (ProgramExecution (p_inverse B) b a).
    apply H. apply pe_inverse. assumption.
    break_down_executions.
  }
Qed.
Lemma peq_refl A : ProgramsEquivalent A A.
  split_and_break_down_peq.
Qed.
Hint Immediate peq_refl : break_down_peq.
Lemma peq_id_then A : ProgramsEquivalent (A ∘ p_id) A.
  split_and_break_down_peq.
Qed.
Hint Extern 1 (ProgramExecution (?P ∘ p_id) _ _) =>
  progress (apply (peq_id_then P)); shelve
: break_down_executions.
Hint Extern 5 =>
  progress (match goal with
  | H : (ProgramExecution (?P ∘ p_id) _ _) |- _ =>
          apply (peq_id_then P) in H
  end); shelve
: break_down_executions.
Lemma peq_then_id A : ProgramsEquivalent (p_id ∘ A) A.
  split_and_break_down_peq.
Qed.
Hint Extern 1 (ProgramExecution (p_id ∘ ?P) _ _) =>
  progress (apply (peq_then_id P)); shelve
: break_down_executions.
Hint Extern 5 =>
  progress (match goal with
  | H : (ProgramExecution (p_id ∘ ?P) _ _) |- _ =>
          apply (peq_then_id P) in H
  end); shelve
: break_down_executions.
Lemma peq_inleft_inverse A : ProgramsEquivalent
  (p_in_left (p_inverse A)) (p_inverse (p_in_left A)).
  split_and_break_down_peq.
Qed.
Lemma peq_inleft_compose A B : ProgramsEquivalent
  (p_in_left (A ∘ B)) ((p_in_left A) ∘ (p_in_left B)).
  split_and_break_down_peq.
Qed.

Definition spl_compose (a b : SimpleProgramList) := b ++ a.
Ltac fold_spl_compose := match goal with
    | |- context A [(?a ++ ?b)] => change (?a ++ ?b) with (spl_compose b a)
    end.
Lemma spl_compose_correct P Q : ProgramsEquivalent
  (p_spl (spl_compose P Q))
  ((p_spl P) ∘ (p_spl Q)).
  (* unfold ProgramsEquivalent, AuthoritativeProgramDerives. *)
  induction Q; cbn.
  {
    (* unfold spl_compose. *)
    split; intro; break_down_executions.
  }
  {
    eapply peq_trans; [|apply peq_rotate].
    apply peq_compatibility_both.
    exact IHQ.
    apply peq_refl.
  }
Qed.
Fixpoint spl_inverse spl :=
  match spl with
  | nil => nil
  | x::xs => (spl_inverse xs) ++ (sps_inverse x)::nil
  end.
Lemma spl_inverse_correct spl : ProgramsEquivalent
  (p_spl (spl_inverse spl))
  (p_inverse (p_spl spl)).
  unfold ProgramsEquivalent, AuthoritativeProgramDerives.
  
  induction spl; cbn; split; intros; break_down_executions.
  {
    apply spl_compose_correct.
    repeat econstructor.
    apply sps_inverse_correct; repeat econstructor; eassumption.
    apply IHspl; repeat econstructor; eassumption.
  }
  {
    apply spl_compose_correct in H.
    break_down_executions. repeat econstructor.
    apply IHspl in H0; break_down_executions; assumption.
    apply sps_inverse_correct in H; break_down_executions.
  }
Qed.

Definition spl_sps1_in_left sps1 :=
  match sps1 with 
  | sps1_rotate_left => (sps_forwards sps1_rotate_left_in_left)::nil
  | sps1_rotate_left_in_left =>
    (sps_backwards sps1_rotate_left)::
    (sps_forwards sps1_rotate_left_in_left)::
    (sps_forwards sps1_rotate_left)::
    nil
  | sps1_swap => (sps_forwards sps1_swap_in_left)::nil
  | sps1_swap_in_left => 
    (sps_backwards sps1_rotate_left)::
    (sps_forwards sps1_swap_in_left)::
    (sps_forwards sps1_rotate_left)::
    nil
  | sps1_dup =>
    (sps_forwards sps1_dup)::
    (sps_forwards sps1_rotate_left)::
    (sps_forwards sps1_drop)::
    (sps_forwards sps1_swap)::
    (sps_forwards sps1_rotate_left)::
    nil
  | sps1_drop => 
    (sps_forwards sps1_swap)::
    (sps_forwards sps1_rotate_left)::
    (sps_forwards sps1_swap_in_left)::
    (sps_forwards sps1_drop)::
    nil
  end.

Lemma spl_sps1_in_left_correct sps1 : ProgramsEquivalent
  (p_spl (spl_sps1_in_left sps1))
  (p_in_left (p_sps1 sps1)).
  (* unfold ProgramsEquivalent, AuthoritativeProgramDerives; *)
  destruct sps1; split_and_break_down_peq.
Qed.

Definition spl_sps_in_left sps :=
  match sps with 
  | sps_forwards s => spl_sps1_in_left s
  | sps_backwards s => spl_inverse (spl_sps1_in_left s)
  end.

Lemma spl_sps_in_left_correct sps : ProgramsEquivalent
  (p_spl (spl_sps_in_left sps))
  (p_in_left (p_sps sps)).
  
  destruct sps.
  apply spl_sps1_in_left_correct.
  cbn.
  eapply peq_trans; [apply spl_inverse_correct|].
  eapply peq_trans; [|split; apply peq_inleft_inverse].
  apply (proj1 (peq_inverse_equivalent _ _)).
  apply spl_sps1_in_left_correct.
Qed.

Definition p_force_branch p :=
  p ∘ (p_swap ∘ p_swap).

Lemma peq_force_branch_inleft p : ProgramsEquivalent
  (p_force_branch (p_in_left p))
  (p_in_left p).
  unfold p_force_branch.
  split_and_break_down_peq.
Qed.

Lemma peq_force_branch_sps_in_left sps P : ProgramsEquivalent
  (p_force_branch (P ∘ (p_spl (spl_sps_in_left sps))))
  ((p_force_branch P) ∘ (p_spl (spl_sps_in_left sps))).
  unfold p_force_branch.
  destruct sps; destruct s.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
  split_and_break_down_peq.
Qed.
  

Definition spl_in_left spl :=
  sps_forwards sps1_swap::
  sps_forwards sps1_swap::
  flat_map spl_sps_in_left spl.


Ltac rewrite_peq_subterm_impl A B AeqB :=
  lazymatch goal with
  | |- ProgramsEquivalent A _ => apply peq_trans with B; [exact AeqB|]
  | |- ProgramsEquivalent _ A => apply peq_trans with B; [|exact AeqB]
  | |- context Ctx [A ∘ ?C] =>
        rewrite_peq_subterm_impl (A ∘ C) (B ∘ C)
          (peq_compatibility_left C AeqB)
  | |- context Ctx [?C ∘ A] =>
        rewrite_peq_subterm_impl (C ∘ A) (C ∘ B)
          (peq_compatibility_right C AeqB)
  end.
Ltac rewrite_peq_subterm A B :=
  let AeqB := fresh "AeqB" in
  assert (ProgramsEquivalent A B) as AeqB;
  [break_down_peq|rewrite_peq_subterm_impl A B AeqB; clear AeqB].
Ltac rewrite_peq_subterm_with AeqB :=
  match (type of AeqB) with
  (ProgramsEquivalent ?A ?B) => rewrite_peq_subterm_impl A B AeqB
  end.

Ltac erewrite_peq_subterm A :=
  let B := fresh "B" in
  evar (B : Program);
  rewrite_peq_subterm A B.
  
Ltac in_peq_subterm_impl path :=
  match path with
  | EmptyString => idtac
  | String ?first ?rest =>
    match (eval compute in (String.ltb path "r")) with
    | true => apply peq_compatibility_left; in_peq_subterm_impl rest
    | false => apply peq_compatibility_right; in_peq_subterm_impl rest
    end
  end.
  
Ltac in_peq_subterm path :=
  match path with
  | String ?first ?rest =>
    match (eval compute in (String.ltb path "r")) with
    | true => eapply peq_trans; [in_peq_subterm_impl rest|]
    | false => eapply peq_trans; cycle 1; [in_peq_subterm_impl rest|]
    end
  end.

(* Ltac rewrite_peq_subterm_nosolve A B :=
  let AeqB := fresh "AeqB" in
  assert (ProgramsEquivalent A B) as AeqB;
  [|rewrite_peq_subterm_impl A B AeqB; clear AeqB]. *)

Lemma spl_in_left_correct spl : ProgramsEquivalent
  (p_spl (spl_in_left spl))
  (p_in_left (p_spl spl)).

  (* eapply peq_trans.
  2: apply peq_force_branch_inleft.

  induction spl.
  {
    unfold p_force_branch.
    split_and_break_down_peq.
  }
  unfold spl_in_left. *)
  (* rewrite_peq_subterm (p_spl (spl_in_left spl)) (p_spl (spl_in_left spl)). *)

  induction spl.
  split_and_break_down_peq.

  
  unfold spl_in_left.
  cbn.
  fold_spl_compose.
  
  (* Set Debug Eauto. *)

  match goal with
  |- (_ ((?A ∘ p_swap) ∘ p_swap) _) => rewrite_peq_subterm
    ((A ∘ p_swap) ∘ p_swap)
    (A ∘ (p_swap ∘ p_swap))
  end.

  (* in_peq_subterm "r"%string. *)
  
  match goal with
  |- context [(p_spl (spl_compose ?A ?B))] => rewrite_peq_subterm
    (p_spl (spl_compose A B))
    ((p_spl A) ∘ (p_spl B))
  end;
  [apply spl_compose_correct|].

  change (?A ∘ p_swap ∘ p_swap) with (p_force_branch A).
  eapply peq_trans.
  apply peq_force_branch_sps_in_left.

  rewrite_peq_subterm
    (p_force_branch (p_spl (flat_map spl_sps_in_left spl)))
    (p_spl (spl_in_left spl)).
  unfold p_force_branch.
  apply peq_trans with (((p_spl (flat_map spl_sps_in_left spl)
∘ p_swap) ∘ p_swap)). apply peq_sym. apply peq_rotate.
  (* unfold spl_in_left. cbn. *)
  apply peq_refl.

  eapply peq_trans.
  2: {apply peq_sym. apply peq_inleft_compose. }

  (* match (type of IHspl) with
  (ProgramsEquivalent ?A ?B) => rewrite_peq_subterm_impl A B AeqB
  end. *)
  rewrite_peq_subterm_with IHspl. 

  apply peq_compatibility_right.

  apply spl_sps_in_left_correct.
Qed.

Fixpoint spl_of_execution P Value a b
  (exe : @ProgramExecution Value P a b)
  : SimpleProgramList
  :=
  match exe with
  | pe_compose A B x y z Ayz Bxy =>
      spl_compose (spl_of_execution Ayz) (spl_of_execution Bxy)
  | pe_iterate_refl A x => nil
  | pe_iterate_chain A x y z Ayz Asxy =>
      spl_compose (spl_of_execution Azy) (spl_of_execution Asxy)
  | pe_choice_left A B x y Axy => spl_of_execution Axy
  | pe_choice_right A B x y Bxy => spl_of_execution Bxy
  | pe_inverse A x y Axy => spl_inverse (spl_of_execution Axy)
  | pe_in_left A x y z =>

    ProgramExecution A x y ->
    ProgramExecution
      (p_in_left A) (pc_branch x z) (pc_branch y z)
  | pe_rotate_left A B C :
    ProgramExecution p_rotate_left
      (pc_branch A (pc_branch B C))
      (pc_branch (pc_branch A B) C)
  | pe_swap A B :
    ProgramExecution p_swap
      (pc_branch A B)
      (pc_branch B A)
  | pe_dup A :
    ProgramExecution p_dup A (pc_branch A A)
  | pe_drop A B :
    ProgramExecution p_drop (pc_branch A B) A
  end.



CoInductive VarsInRightLocations (i : VarIndex) : ProgramContext VarIndex -> Prop :=
  | virl_here : VarsInRightLocations i (pc_value i)
  | virl_branch L R : 
    VarsInRightLocations (cons false i) L ->
    VarsInRightLocations (cons true i) R ->
    VarsInRightLocations i (pc_branch L R)
  .

Lemma p_dp_says_derives
  (inputs : ProgramContext VarIndex)
  (inr : VarsInRightLocations nil inputs)
  (p : Program)
  (dp : DeterministicProgram)
  (exec : ProgramExecution p inputs (pc_dp dp))
  :
  AuthoritativeProgramDerives p (p_canonical_dp dp).

  unfold AuthoritativeProgramDerives; intros.
  apply p_canonical_dp_matches in H.
  induction H.
  {
    cbn in *.
    induction exec.
  }
  

Definition Deterministic (P : Program) :=
  ∀ C _c i o1 o2, @ProgramExecution C _c P i o1 -> ProgramExecution P i o2 -> o1 = o2.

Remark ddup : Deterministic p_dup.
  unfold Deterministic.
  intros.
  dependent destruction H0.
  dependent destruction H.
  trivial.
Qed.

Definition d_p_dp (P : Program) (DP : Deterministic P) : DeterministicProgram.
  induction P.
  
  
  unfold Deterministic in DP.
Lemma d_p_dp (P : Program) :
  Deterministic P -> ∃ dp : DeterministicProgram, ProgramExecution P dp

Inductive Deterministic : Program -> Prop :=
  | pd_compose P Q :
      Deterministic P -> Deterministic Q -> (p_compose P Q)
  (* | pd_iterate P Q :
      Deterministic P -> Deterministic Q -> (p_compose P Q) *)
  .
with ()









Lemma programs_injective Value P :
  ∀ x y z w,
  @ProgramExecution Value P x y ->
  @ProgramExecution Value P z w ->
  ((x = z) <-> (y = w)).
  induction P; intros.
  (* ; split; intro firstEq.  *)
  (* ; rewrite <- firstEq in *. *)
  {
    dependent destruction H0.
    dependent destruction H.
    specialize (IHP1 x y x0 y0 H H0_).
    specialize (IHP2 y z y0 z0 H0 H0_0).
    tauto.
  }
  {
    dependent destruction H0; dependent destruction H.
    {
      split; intro.

      injection H; tauto.
      rewrite H; tauto.
    }
    {
      dependent destruction H0.
      split; intro.
      admit. admit.
    }
    {
      admit.
    }
    {

    }
  }
Qed.


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

