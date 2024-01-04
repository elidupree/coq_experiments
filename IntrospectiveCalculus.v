Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_pred_eq
  | atom_and.

Inductive Formula :=
  | formula_atom : Atom -> Formula
  | formula_apply: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (formula_apply .. (formula_apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := formula_atom atom_const.
Definition fuse := formula_atom atom_fuse.
Definition and := formula_atom atom_and.
Definition pred_eq := formula_atom atom_pred_eq.
Definition formula_true := [pred_eq [pred_eq pred_eq] [pred_eq pred_eq]].

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

Record Inference := makeInference
  { inference_premises: list Formula
  ; inference_conclusion: Formula
  }.

Record Rule := makeRule
  { rule_premises: list FormulaWithVariables
  ; rule_conclusion: FormulaWithVariables
  }.

Notation "ps |- c" := {| inference_premises := ps; inference_conclusion := c |} (at level 80).
Notation "ps |-! c" := {| rule_premises := ps; rule_conclusion := c |} (at level 80).

Fixpoint specialize f values :=
  match f with
    | no_variables f => f
    | formula_variable i => get_variable_value values i
    | apply_with_variables f x =>
        formula_apply (specialize f values) (specialize x values)
    end.

Inductive Unfold : Formula -> Formula -> Prop :=
  | unfold_nothing f : Unfold f f
  | unfold_const f a b : Unfold f [const a] -> Unfold [f b] a
  | unfold_fuse f a b c : Unfold f [fuse a b] -> Unfold [f c] [[a c] [b c]]
  | unfold_and a b c d : Unfold a b -> Unfold c d -> Unfold [and a c] [and b d]
  | unfold_pred_eq a b c d : Unfold a b -> Unfold c d -> Unfold [pred_eq a c] [pred_eq b d].

Inductive RuleProves rule : Inference -> Prop :=
  | rule_proves values ps c :
    Forall2 (λ rule_p p, Unfold (specialize rule_p values) p) (rule_premises rule) ps ->
    Unfold (specialize (rule_conclusion rule) values) c ->
    RuleProves rule {| inference_premises := ps; inference_conclusion := c |}.

Inductive RulesProve rules : Inference -> Set :=
  | ProofByPremise ps c : In c ps ->
    RulesProve rules {| inference_premises := ps; inference_conclusion := c |}
  | ProofByRule rule inference :
    In rule rules -> RuleProves rule inference -> RulesProve rules inference.

Fixpoint and_chain ps :=
  match ps with
    | nil => no_variables formula_true
    | cons x xs => v[n[and] x (and_chain xs)]
    end.
  
Definition internal_inference i :=
  v[n[pred_eq] (and_chain (rule_premises i)) (rule_conclusion i)].
  
Definition external_inference i y :=
  map (λ p, specialize p y) (rule_premises i) |- specialize (rule_conclusion i) y.


Inductive Justified : Rule -> Prop :=
  | justified ls r :
    (∀rules y,
      Forall (λ l, (∀x, RulesProve rules (external_inference l y))) ls
      ->
      RulesProve rules (external_inference r y))
    ->
    Justified ((
        map
          (λ l, (internal_inference l))
          ls
    ) |-! (internal_inference r)).
  