Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_pred_imp
  | atom_and.

Inductive Formula :=
  | formula_atom : Atom -> Formula
  | formula_apply: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (formula_apply .. (formula_apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := formula_atom atom_const.
Definition fuse := formula_atom atom_fuse.
Definition pred_imp := formula_atom atom_pred_imp.
Definition f_and := formula_atom atom_and.
(* Definition f_nil := const. *)

(* Record Inference F := makeInf
  { inf_premises: list F
  ; inf_conclusion: F
  }.

Notation "ps |- c" := {| inf_premises := ps; inf_conclusion := c |} (at level 80). *)

(* Print inf_conclusion. *)
(* Definition map_inf A B (f : A -> B) i :=
  ((map f (inf_premises i)) |- f (inf_conclusion i)).
Definition zipmap_inf A B C (f : A -> B -> C) i :=
  ((map f (inf_premises i)) |- f (inf_conclusion i)).
Definition map_inf_to_coq_prop A (f : A -> Prop) i :=
  ((Forall f (inf_premises i)) -> f (inf_conclusion i)). *)

(* Definition InternalPredicateToBeRepresentedAsAFormula := Inference Formula. *)
(* Definition InternalPredicate := Formula. *)
(* Definition InternalProposition := Formula. *)
(* Definition InferenceBetweenPropositions := Inference InternalProposition. *)
Definition Ruleset := Formula -> Formula -> Prop.

(* Fixpoint f_pred_list ps :=
  match ps with
    | nil => f_nil
    | cons x xs => [f_and x (f_pred_list xs)]
    end. *)
  
(* Definition f_prop (p : Inference InternalPredicate) : Formula :=
  [pred_imp (f_pred_list (inf_premises p)) (inf_conclusion p)]. *)
    
(* Definition f_pred_inf_transform i : Formula :=
  [pred_imp (f_pred_list (inf_premises i)) (inf_conclusion i)]. *)

Inductive Unfold : Formula -> Formula -> Prop :=
  | unfold_nothing f : Unfold f f
  | unfold_const f a b : Unfold f [const a] -> Unfold [f b] a
  | unfold_fuse f a b c : Unfold f [fuse a b] -> Unfold [f c] [[a c] [b c]]
  | unfold_pred_imp a b c d : Unfold a b -> Unfold c d -> Unfold [pred_imp a c] [pred_imp b d]
  | unfold_pred_and a b c d : Unfold a b -> Unfold c d -> Unfold [f_and a c] [f_and b d].

(* Definition UnfoldToProposition : Formula -> Inference InternalPredicate -> Prop :=
  λ f i, Unfold f (f_prop i). *)

Inductive RulesProveInference Rules : Formula -> Formula -> Prop :=
  | proof_by_rule a b : Rules a b -> RulesProveInference Rules a b
  | proof_by_transitivity a b c :
    RulesProveInference Rules a b ->
    RulesProveInference Rules b c ->
    RulesProveInference Rules a c.

Definition meaning
    (Rules : Ruleset)
    (UnknownMeanings : Formula -> Prop)
  : Formula -> Prop
  :=
    fix meaning (f : Formula) :=
      match f with
        (* [and a b] *)
        | formula_apply (formula_apply (formula_atom atom_and) a) b
          => meaning a /\ meaning b
        (* [pred_imp a b] *)
        | formula_apply (formula_apply (formula_atom atom_pred_imp) a) b
          => (∀ x, ∃ ap bp,
            Unfold [a x] ap /\ Unfold [b x] bp /\
            RulesProveInference Rules ap bp)
        | _ => UnknownMeanings f
        end.

(* Inductive IntrospectProp : Prop -> Formula -> Prop :=
  | introspect_pred_imp a b :
    IntrospectProp (∀x meanings ap bp,
      Unfold [a x] ap -> Unfold [b x] bp ->
      IntrospectProp A ap -> IntrospectProp B bp) [pred_imp a b]
  | introspect_and A a B b :
    IntrospectProp A a -> IntrospectProp B b -> 
    IntrospectProp (A /\ B) [f_and a b]. *)
  
(* Inductive MappedList A B f : list A -> list B -> Prop :=
  | MappedList_nil : MappedList f nil nil
  | MappedList_cons a b atl btl :
    f a b -> MappedList f atl btl -> MappedList f (a::atl) (b::btl).
  

Inductive RulesProvePropInf Rules : InferenceBetweenPropositions -> Prop :=
  | proof_by_premise ps c : In c ps -> RulesProvePropInf Rules (ps |- c)
  | proof_by_rule specialized ps :
    Rules specialized ->
    map_inf_to_coq_prop (λ f, RulesProvePropInf Rules (ps |- f)) specialized.
    (* Forall (λ spec_premise, RulesProvePropInf Rules (ps |- spec_premise)) (inf_premises specialized) ->
    RulesProvePropInf Rules (ps |- (inf_conclusion specialized)). *) *)

(* Definition RulesProvePropInfWthUnfolding Rules fi :=
  ∃ ps c, RulesProvePropInf Rules (ps |- c)
    /\ MappedList Unfold (inf_premises fi) ps
    /\ Unfold (inf_conclusion fi) c. *)
  
(* Definition RulesProveIntPredInf Rules (i : Inference InternalPredicate) :=
  ∀x, RulesProvePropInfWthUnfolding Rules (map_inf (λ p, [p x]) i). *)

(* "if these rules prove all inferences on the left...
    then they prove the inference on the right" *)
(* Definition RulesTransformIntPredInfs Rules
  (pred_infs : Inference (Inference InternalPredicate)) : Prop :=
  map_inf_to_coq_prop
    (λ pred_inf, RulesProveIntPredInf Rules pred_inf)
    pred_infs. *)

(* Definition IntPredInfTransformJustified pred_infs : Prop :=
  ∀Rules, RulesTransformIntPredInfs Rules pred_infs. *)

(* Definition pred_inf_transform_to_inf
  (pred_infs : Inference (Inference InternalPredicate))
  : Inference PropositionPreF
  := map_inf f_prop pred_infs. *)

Definition InferenceJustified a b : Prop :=
  ∀Rules UnknownMeanings,
    (meaning Rules UnknownMeanings a) ->
    (meaning Rules UnknownMeanings b).

(* Inductive InferenceJustified :  -> Prop :=
| inference_justified_by_premise ps c :
   In c ps -> InferenceJustified (ps |- c)
| inference_justified_by_pred_inf pred_infs :
  (IntPredInfTransformJustified pred_infs) ->
  InferenceJustified (map_inf f_prop pred_infs). *)

(* Lemma forall_in A P l (x:A) : Forall P l -> In x l -> P x.
  (* specialize Forall_forall with (A := A), P:=P). *)
Admitted. *)

Lemma provable_by_justified_rules_means_justified p c :
  RulesProveInference InferenceJustified p c
  ->
  InferenceJustified p c.
  intro.
  induction H; [assumption|clear H H0].
  unfold InferenceJustified in *.
  intros.
  specialize IHRulesProveInference1 with (Rules := Rules).
  specialize IHRulesProveInference1 with (UnknownMeanings := UnknownMeanings).
  specialize IHRulesProveInference2 with (Rules := Rules).
  specialize IHRulesProveInference2 with (UnknownMeanings := UnknownMeanings).
  exact (IHRulesProveInference2 (IHRulesProveInference1 H)).
Qed.

Definition f_id := [fuse const const].
Definition f_true := [pred_imp f_id f_id].
Definition f_false := [pred_imp [const f_true] f_id].

Lemma false_unjustified :
  InferenceJustified f_true f_false -> False.
  unfold InferenceJustified; intro.

  (* use the very weak rules "eq",
    so it'll be easy to show that the rules don't prove what False says. *)
  specialize H with (Rules := eq).
  specialize H with (UnknownMeanings := λ _, True). (* doesn't matter *)
  cbn in H.

  (* Right now we basically have (meaning True -> meaning False),
     and we want to simplify this by _providing_ (meaning True).
     So we just say hey look, id x = id x. *)
  assert (∀ x : Formula,
    ∃ ap bp : Formula,
        Unfold [(f_id) (x)] ap /\
        Unfold [(f_id) (x)] bp /\
        RulesProveInference eq ap
        bp).
  intro.
  apply ex_intro with [f_id x].
  apply ex_intro with [f_id x].
  split; [apply unfold_nothing|].
  split; [apply unfold_nothing|].
  apply proof_by_rule.
  unfold InferenceJustified; intros.
  reflexivity.

  assert (H := H H0); clear H0.

  (* Now, back to the main proving. *)
  (* Using "and" here just because it's a formula that doesn't unfold. *)
  specialize H with (x := f_and).
  destruct H as (ap, (bp, (ua, (ub, i)))).
  destruct i.
  subst b.

  destruct H.



  Unshelve.
  exact const.
  apply unfold_nothing.
  apply (exist _ [(f_id) (x)]).
  



Theorem justified_rules_make_justified_proofs :
  ∀ i,
    RulesProvePropInf InferenceJustified i
    ->
    InferenceJustified i.
  
  intro; destruct i as (original_ps, original_c).

  (* basically "induction H.", it's just that Coq didn't manage to get the right IH *)
  refine ((fix ind ps1 c1 H : InferenceJustified (ps1 |- c1) :=
    match H in RulesProvePropInf _ i return InferenceJustified i with
    | proof_by_premise ps c cinp => _
    | proof_by_rule specialized ps sj mid_prems_proved => _
    end) original_ps original_c); clear original_ps original_c H ps1 c1.
  
  (* premise case *)
  constructor; assumption.
  (* constructor; unfold IntPredInfTransformJustified; intros.
  unfold RulesTransformIntPredInfs. unfold map_inf_to_coq_prop. intros.
  (* cbn in H. *)
  apply (forall_in _ H).
  assumption. *)
  
  (* rule case *)
  destruct specialized as (mid_prems, c).

  (* finish doing induction; this is basically just boilerplate *)
  refine (let indH : Forall (λ f, InferenceJustified (ps |- f)) mid_prems := (fix fl
      (mid_prems_part: list InternalProposition)
      (mid_prems_proved_part: Forall (λ f : InternalProposition,
          RulesProvePropInf
          InferenceJustified
          (ps |- f)) mid_prems_part)
      : Forall (λ f, InferenceJustified (ps |- f)) mid_prems_part
    := match mid_prems_proved_part as m in (Forall _ l) return (Forall (λ f, InferenceJustified (ps |- f)) l) with
      | Forall_nil => Forall_nil _
      | Forall_cons head tail head_proof tail_proof => 
         Forall_cons _ (ind ps head head_proof) (fl tail tail_proof)
      end) mid_prems mid_prems_proved in _).
  clearbody indH.
  clear ind mid_prems_proved.

  (* Now back to the real proof logic for the "rule" case *)
  cbn in *.

  dependent destruction sj.

  (* Justified by premise? ok, sure, use that premise's justification *)
  pose (forall_in c indH H) as i; cbn in i; exact i.

  (* Justified by rule? *)
  destruct pred_infs as (l, r); cbn in *.
  unfold IntPredInfTransformJustified in H.
  specialize H with (Rules := InferenceJustified).
  unfold RulesTransformIntPredInfs in *.
  unfold map_inf_to_coq_prop in *; cbn in *.
  apply inference_justified_by_pred_inf.

  apply inference_justified_by_premise.

  apply forall_in.

  assert (Forall
    (λ f : InternalProposition,
    InferenceJustified
    (ps |- f))
    mid_prems).

  destruct H.
  apply inference_justified_by_pred_inf.
  unfold IntPredInfTransformJustified in *; intros.
  (* specialize H with InferenceJustified.  *)
  unfold RulesTransformIntPredInfs in *.
  unfold map_inf_to_coq_prop in *; intros; cbn in *.
  (* unfold RulesProveIntPredInf in *. *)

  
  dependent destruction sj.
  unfold IntPredInfTransformJustified in H.
  specialize H with Rules.
  unfold RulesTransformIntPredInfs in H.
  unfold map_inf_to_coq_prop in H; cbn in H.
  apply H; clear H.

  induction indH; [apply Forall_nil|].
  apply Forall_cons; [|assumption].
  clear l indH IHindH.

  dependent destruction H.
  unfold IntPredInfTransformJustified in H.
  specialize H with Rules.
  unfold RulesTransformIntPredInfs in H.
  unfold map_inf_to_coq_prop in H; cbn in H.
  apply H; clear H.
  assumption.
Admitted.


Definition f_fst := [fuse f_id const].
Definition f_snd := [fuse f_id [const f_id]].


Lemma false_unjustified :
  InferenceJustified (nil |- (f_fst::nil |- f_snd)) -> False.
  intro.
  dependent destruction H.
  unfold IntPredInfTransformJustified in H.
  specialize H with Rules.
  unfold RulesTransformIntPredInfs in H.
  unfold map_inf_to_coq_prop in H; cbn in H.
  specialize H with (Rules := (λ _, False)).
  assert (H := H (Forall_nil _)).
  unfold RulesProveIntPredInf in H.

  unfold RulesProveFormulaInf in H.
  specialize H with (x := const).
  destruct H as (ps,H).
  destruct H as (c,H).
  destruct H as (rule,H).
  destruct H as (ps_unf,c_unf).
  dependent destruction rule.

  destruct rule.
  dependent destruction H .
  dependent destruction H.


  
  
Lemma justified_to_any : 
Lemma justified_to_any : 
  ∀ metainf, 
    RulesProveDoublePredInf Justified metainf
    ->
    (∀Rules, RulesProveDoublePredInf Rules metainf).
  unfold RulesProveDoublePredInf in *.
  unfold map_inf_to_coq_prop in *.
  intros.
  specialize (H y).
  

Theorem justified_rules_make_justified_proofs :
  ∀ metainf,
    ((∀ y, (map_inf_to_coq_prop
      (λ i, RulesProvePredInf Justified (specialize_inf i y))
      metainf))
    ->
    Justified (map_inf f_pred_inf metainf)).
  intros.
  apply justified.
  unfold map_inf_to_coq_prop in *.
  intros.
  specialize (H y).
  cbn in H.

  induction H.
  constructor.


Definition f_id := [fuse const const].
Definition f_fst := [fuse f_id const].
Definition f_snd := [fuse f_id [const f_id]].
Definition f_false := [pred_imp f_fst f_snd].
Definition f_true := [pred_imp [pred_imp pred_imp] [pred_imp pred_imp]].

Theorem ic_is_consistent : (∀ i, RulesProve Justified (nil |- i)) -> False.
  intro.
  specialize H with (i := f_false).
  dependent induction H.

  (* "Can't be a premise, because there are none" *)
  unfold In in H; assumption.
  
  (* "How was the rule justified?" *)
  destruct H.

  destruct H0.

  cbv in H.


  
Parameter VariableIndex : Set.
Parameter VariableValues : Set.
Parameter get_variable_value: VariableValues-> VariableIndex ->Formula.

Inductive FormulaWithVariables :=
  | no_variables : Formula -> FormulaWithVariables
  | formula_variable : VariableIndex -> FormulaWithVariables
  | apply_with_variables:FormulaWithVariables -> FormulaWithVariables -> FormulaWithVariables.

Notation "v[ x y .. z ]" := (apply_with_variables .. (apply_with_variables x y) .. z)
 (at level 0, x at next level, y at next level).
Notation "n[ x ]" := (no_variables x)
 (at level 0, x at next level).

Fixpoint specialize_fwv f values :=
  match f with
    | no_variables f => f
    | formula_variable i => get_variable_value values i
    | apply_with_variables f x =>
        [(specialize_fwv f values) (specialize_fwv x values)]
    end.

Definition specialize_inf i values :=
  map_inf (λ p, specialize_fwv p values) i.

Inductive RuleSpecializes rule : Inference Formula -> Prop :=
  | rule_specializes values ps c :
    Forall2 (λ rule_p p, Unfold (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    Unfold (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).