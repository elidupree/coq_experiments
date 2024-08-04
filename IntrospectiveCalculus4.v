Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import List.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.


(****************************************************
                      Rulesets
****************************************************)

(* FWM = Formula with metavariables *)
Inductive ConventionalFWM :=
  | conventional_atom : nat -> ConventionalFWM
  | conventional_variable : nat -> ConventionalFWM
  | conventional_apply : ConventionalFWM -> ConventionalFWM -> ConventionalFWM.

Record ConventionalInference := conventional_inference {
    conventional_premise : ConventionalFWM
    ; conventional_conclusion : ConventionalFWM
  }.

Notation "p 'c|-' c" := (conventional_inference p c) (at level 70).

Definition ConventionalRuleset := list ConventionalInference.

Definition ConventionalContext := nat -> ConventionalFWM.
Parameter specialize_conventional_inference : ConventionalInference -> ConventionalContext -> ConventionalInference.

Inductive ConventionalProof : ConventionalRuleset -> ConventionalInference -> Prop :=
  | conventional_proof_inference h t : ConventionalProof (h::t) h
  | conventional_proof_later h t i : ConventionalProof t i -> ConventionalProof (h::t) i
  | conventional_proof_specialize r i vs : ConventionalProof r i -> ConventionalProof r (specialize_conventional_inference i vs)
  | conventional_proof_transitivity r a b c : 
    ConventionalProof r (a c|- b) -> 
    ConventionalProof r (b c|- c) -> 
    ConventionalProof r (a c|- c)
  .


(* we aren't going to actually construct any infinite formulas, but we make this co-inductive because we don't need to commit to the assumption that they are finite *)
(* CoInductive Formula :=
  | mk_formula : option Formula -> option Formula -> Formula. *)

Class Formula F := {
    apply : option F -> option F -> F
  }.

Class ToOptionFormula T F := {
    to_option_formula : T -> option F
  }.

Instance toff F (_f : Formula F) : ToOptionFormula F F := {|
    to_option_formula := Some
  |}.

Instance tofof F (_f : Formula F) : ToOptionFormula (option F) F := {|
    to_option_formula := id
  |}.
  
Notation "[ x y ]" := (apply (to_option_formula x) (to_option_formula y))
 (at level 0, x at next level, y at next level).

(* Definition RecF := ∀ F (_f: Formula F), F.
Print map.
Instance recff : Formula RecF := {
    apply := λ f g F _f, apply (option_map (λ f, f F _f) f) (option_map (λ g, g F _f) g)
  }. *)

Inductive ElementaryRule :=
  | rule_swap : ElementaryRule
  | rule_drop_left : ElementaryRule
  | rule_dup_left : ElementaryRule
  | rule_rotate_left : ElementaryRule
  .
Inductive Ruleset :=
  | ruleset_elementary : ElementaryRule -> Ruleset
  | ruleset_chain : Ruleset -> Ruleset -> Ruleset
  | ruleset_choice : Ruleset -> Ruleset -> Ruleset.

Inductive ElementaryRuleTransformsFormula [F] [_f : Formula F] : ElementaryRule -> F -> F -> Prop :=
  | ertf_swap f g : ElementaryRuleTransformsFormula rule_swap [f g] [g f]
  | ertf_drop_left f g : ElementaryRuleTransformsFormula rule_drop_left [f g] g
  | ertf_dup_left f g : ElementaryRuleTransformsFormula rule_swap [f g] [[f f] g]
  | ertf_rotate_left f g h : ElementaryRuleTransformsFormula rule_rotate_left [f [g h]] [[f g] h]
  .

Inductive RulesetTransformsFormula [F] [_f : Formula F] : Ruleset -> F -> F -> Prop :=
  | rtf_elementary r f g : ElementaryRuleTransformsFormula r f g -> RulesetTransformsFormula (ruleset_elementary r) f g
  | rtf_chain r s f g h : RulesetTransformsFormula r f g -> RulesetTransformsFormula s g h -> RulesetTransformsFormula (ruleset_chain r s) f h
  | rtf_choice_left r s f g : RulesetTransformsFormula r f g -> RulesetTransformsFormula (ruleset_choice r s) f g
  | rtf_choice_right r s f g : RulesetTransformsFormula s f g -> RulesetTransformsFormula (ruleset_choice r s) f g
  .

Inductive Proof : Ruleset -> Ruleset -> Prop :=
  .

(* Lemma uhh r s : (∀ F (_f : Formula F) (f g : F), RulesetTransformsFormula s f g -> RulesetTransformsFormula r f g) -> (∀ f g : RecF, RulesetTransformsFormula s f g -> RulesetTransformsFormula r f g).
  intros.
  apply H.
  apply H0.
Qed. *)

Lemma proof_merge r a b : 
  Proof r a -> Proof r b -> Proof r (ruleset_choice a b).
Qed.

Lemma proofs_are_complete : ∀ (r s : Ruleset), (∀ F (_f : Formula F) (f g : F), RulesetTransformsFormula s f g -> RulesetTransformsFormula r f g) -> Proof r s.
  intros.
  induction s.
  3: {
    apply proof_merge; [apply IHs1 | apply IHs2]; intros; apply H;[apply rtf_choice_left | apply rtf_choice_right]; assumption.
  }
  all: {

  }




Inductive RulesetRepresentsConventionalRuleset : Ruleset -> ConventionalRuleset -> Prop :=
  | rrcr_
  .

Parameter conventional_formula_to_formula : ConventionalFWM -> Formula.
Parameter conventional_inference_to_ruleset : ConventionalInference -> Ruleset.
Parameter conventional_ruleset_to_ruleset : ConventionalRuleset -> Ruleset.

Parameter formula_to_conventional_formula : Formula -> ConventionalFWM.
Parameter ruleset_to_conventional_ruleset : Ruleset -> ConventionalRuleset.

Lemma conventional_proof_to_proof r i : ConventionalProof r i -> Proof (conventional_ruleset_to_ruleset r) (conventional_inference_to_ruleset i).
Qed.

Lemma proof_to_conventional_proofs p c : Proof p c -> Forall (λ i, ConventionalProof (ruleset_to_conventional_ruleset p) i) (ruleset_to_conventional_ruleset c).
Qed.