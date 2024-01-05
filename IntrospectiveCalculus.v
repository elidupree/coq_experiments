Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_pred_imp
  | atom_pred_and.

Inductive Formula :=
  | formula_atom : Atom -> Formula
  | formula_apply: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (formula_apply .. (formula_apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := formula_atom atom_const.
Definition fuse := formula_atom atom_fuse.
Definition pred_and := formula_atom atom_pred_and.
Definition pred_imp := formula_atom atom_pred_imp.
Definition f_true := [pred_imp [pred_imp pred_imp] [pred_imp pred_imp]].

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

Record Inference F := makeInf
  { inf_premises: list F
  ; inf_conclusion: F
  }.

Notation "ps |- c" := {| inf_premises := ps; inf_conclusion := c |} (at level 80).

Print inf_conclusion.
Definition map_inf A B (f : A -> B) i :=
  ((map f (inf_premises i)) |- f (inf_conclusion i)).
Definition map_inf_to_coq_prop A (f : A -> Prop) i :=
  ((Forall f (inf_premises i)) -> f (inf_conclusion i)).

Definition Rule := Inference FormulaWithVariables.

Fixpoint specialize_fwv f values :=
  match f with
    | no_variables f => f
    | formula_variable i => get_variable_value values i
    | apply_with_variables f x =>
        [(specialize_fwv f values) (specialize_fwv x values)]
    end.

Definition specialize_inf i values :=
  map_inf (λ p, specialize_fwv p values) i.
  

Inductive Unfold : Formula -> Formula -> Prop :=
  | unfold_nothing f : Unfold f f
  | unfold_const f a b : Unfold f [const a] -> Unfold [f b] a
  | unfold_fuse f a b c : Unfold f [fuse a b] -> Unfold [f c] [[a c] [b c]]
  | unfold_pred_imp a b c d : Unfold a b -> Unfold c d -> Unfold [pred_imp a c] [pred_imp b d]
  | unfold_pred_and a b c d : Unfold a b -> Unfold c d -> Unfold [pred_and a c] [pred_and b d].

Inductive RuleSpecializes rule : Inference Formula -> Prop :=
  | rule_specializes values ps c :
    Forall2 (λ rule_p p, Unfold (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    Unfold (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).

Inductive RulesProve Rules : Inference Formula -> Prop :=
  | ProofByPremise ps c : In c ps -> RulesProve Rules (ps |- c)
  | ProofByRule rule specialized ps :
    Rules rule -> RuleSpecializes rule specialized ->
    Forall (λ spec_premise, RulesProve Rules (ps |- spec_premise)) (inf_premises specialized) ->
    RulesProve Rules (ps |- (inf_conclusion specialized)).

Fixpoint pred_and_chain ps :=
  match ps with
    | nil => no_variables f_true
    | cons x xs => v[n[pred_and] x (pred_and_chain xs)]
    end.
  
Definition internal_pred_inf i :=
  v[n[pred_imp] (pred_and_chain (inf_premises i)) (inf_conclusion i)].
  
Definition RulesProvePredInf Rules i :=
  ∀x, RulesProve Rules (map_inf (λ p, [p x]) i).

Definition RulesProveDoublePredInf Rules metainf :=
  ∀y, (map_inf_to_coq_prop
      (λ i, RulesProvePredInf Rules (specialize_inf i y))
      metainf).

Inductive Justified : Rule -> Prop :=
  | justified (metainf : Inference (Inference FormulaWithVariables)) :
    (∀Rules, RulesProveDoublePredInf Rules metainf)
    ->
    Justified (map_inf internal_pred_inf metainf).
  
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
    Justified (map_inf internal_pred_inf metainf)).
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