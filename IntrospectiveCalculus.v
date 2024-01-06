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

Definition Ruleset := Formula -> Formula -> Prop.

Inductive Unfold : Formula -> Formula -> Prop :=
  | unfold_nothing f : Unfold f f
  | unfold_const f a b : Unfold f [const a] -> Unfold [f b] a
  | unfold_fuse f a b c : Unfold f [fuse a b] -> Unfold [f c] [[a c] [b c]]
  | unfold_pred_imp a b c d : Unfold a b -> Unfold c d -> Unfold [pred_imp a c] [pred_imp b d]
  | unfold_pred_and a b c d : Unfold a b -> Unfold c d -> Unfold [f_and a c] [f_and b d].

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

Definition InferenceJustified a b : Prop :=
  ∀Rules UnknownMeanings,
    (meaning Rules UnknownMeanings a) ->
    (meaning Rules UnknownMeanings b).

Definition RulesetJustified Rules : Prop :=
  ∀a b, Rules a b -> InferenceJustified a b.

Lemma provable_by_InferenceJustified_means_justified p c :
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

Lemma provable_by_justified_rules_means_justified R p c :
    RulesetJustified R ->
    RulesProveInference R p c ->
    InferenceJustified p c.
  unfold RulesetJustified in *.
  intros.
  induction H0.
  exact (H a b X).
  exact (provable_by_InferenceJustified_means_justified
    (proof_by_transitivity
      (proof_by_rule InferenceJustified a b IHRulesProveInference1)
      (proof_by_rule InferenceJustified b c IHRulesProveInference2)
    )).
Qed.

Lemma eq_justified : RulesetJustified eq.
  unfold RulesetJustified.
  unfold InferenceJustified.
  intros.
  subst b; assumption.
Qed.

Lemma provable_by_eq_means_eq p c :
  RulesProveInference eq p c -> p = c.
  intro.
  induction H; [assumption | ].
  subst b; assumption.
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
  assert (j := provable_by_eq_means_eq i); clear i.
  subst bp.

  (* Now all we have to do is prove that [const true and] and [id and]
     can never unfold to the same thing.
     There are only finitely many possible unfoldings;
     this tells Coq to exhaust them. *)
  repeat (dependent destruction ua || dependent destruction ub).
Qed.


Theorem justified_rulesets_are_consistent R :
    RulesetJustified R ->
    RulesProveInference R f_true f_false ->
    False.
  intros justified proved.
  exact (false_unjustified (provable_by_justified_rules_means_justified justified proved)).
Qed.




Definition f_fst := [fuse f_id const].
Definition f_snd := [fuse f_id [const f_id]].


(* Theorem ic_is_consistent : (∀ i, RulesProve Justified (nil |- i)) -> False.
  intro.
  specialize H with (i := f_false).
  dependent induction H.

  (* "Can't be a premise, because there are none" *)
  unfold In in H; assumption.
  
  (* "How was the rule justified?" *)
  destruct H. *)



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