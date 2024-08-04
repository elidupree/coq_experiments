Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(****************************************************
              Typeclass practicalities
****************************************************)

(* We often want to view IC formulas as "extensible". That is, we know that the formula type has certain constructors, but don't guarantee that those are the ONLY constructors.

Theoretically, this is "simpler" than Coq's `Inductive` types (constructors come _before_ inductive instances), but in Coq, it's not elementary. So to represent a "set of constructors", we use typeclasses - first, one where the typeclass methods are the recursion cases, and then, one where the typeclasse methods are induction cases that refer to those recursion cases.

Here we must do some bureaucracy about how we'll use typeclasses. *)

(* Sometimes we need to pass a typeclass as a function argument. This is fine because a typeclass is an ordinary value, but Coq's features for using typeclasses _implicitly_ don't have a built-in way to treat a local variable as a typeclass. To work around this, we make a wrapper class "Class", which is technically the identity function but is always treated as a typeclass. So when we want a local variable `C` to be treated as a typeclass, we say `Class C` instead. This is the same thing, but counts as a typeclass for implicits. *)
Definition Class [P:Type] (p:P) := p.
Existing Class Class.
Hint Unfold Class : typeclass_instances.
(* Implicit Type C : Prop -> Prop. *)

(* Given such a class, the corresponding _formula type_ is the inductive type with those constructors. We start by representing the type of functions that can construct an arbitrary output by invoking the recursion cases: *)
Definition Rec (C : Prop -> Prop) := ∀ T (_:Class C T), T.

(* We also often want to extend a typeclass with additional constructors, while still leaving it open to still-further constructors. This gives us a _second typeclass_ that is a subclass of the first. It's useful to represent the subclass relation explicitly: *)
Definition Subclass (Subclass Superclass : Prop -> Prop) := ∀ T (_:Class Subclass T), Class Superclass T.
Existing Class Subclass.
Notation "A ⊆ B" := (Subclass A B) (at level 70).
Instance subclass_refl {A} : (A ⊆ A) := λ _ a, a.

(* Once we make an instance for subclass transitivity (A ⊆ B -> B ⊆ C -> A ⊆ C), we risk making instance-search diverge: The subgoal looking for (A ⊆ B) tries looking for some additional transitivity-instance (A ⊆ X) and (X ⊆ B), ad infinitum. So we have to set a limit on typeclass search. We will set this limit fairly low, and just implement "shortcut" instances as-needed: *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 3.
Instance subclass_trans {A B C}
  : (A ⊆ B) -> (B ⊆ C) -> (A ⊆ C)
  := λ ab bc, λ x xA, bc _ (ab _ xA).

Instance subclass_apply {A B} {RH}
  : (A ⊆ B) -> Class A RH -> Class B RH
  := λ ab AR, ab _ AR.

(* If you can construct something with certain constructors, you can also construct it with more constructors: *)
Definition rec_embed [C] (x : Rec C) {C2} {_c:C2 ⊆ C} : Rec C2
  := λ _ _, x _ _.

Definition InductionCases (RecursionCases : Prop -> Prop) := ∀ C, C ⊆ RecursionCases -> (Rec C -> Prop) -> Prop.
Existing Class InductionCases.

Definition Ind [C] [IndCases : InductionCases C] (x : Rec C) := ∀ (IH : Rec C -> Prop), IndCases C subclass_refl IH -> IH x.

(****************************************************
                      Rulesets
****************************************************)

(* Sets of inference rules are fundamental to mathematical truth.

The "forall" case can't be written as (Formula -> Ruleset), because you're not allowed to match on the value of the variable. Instead we have you describe a concrete ruleset on a formula-type with one more variable. *)

Class OneMoreConstructor (C:Prop->Prop) (RH : Prop) := {
    omc_embed_rec_case : Class C RH
  ; omc_new_rec_case : RH
  }.

Definition omc_new {C} : Rec (OneMoreConstructor C) := λ _ _r, @omc_new_rec_case _ _ _r.

Instance omc_class_unwrap [C RH] :
  Class (OneMoreConstructor C) RH ->
         OneMoreConstructor C RH := λ c, c.
Instance omc_subclass {C}
  : OneMoreConstructor C ⊆ C := λ _ _, omc_embed_rec_case.
Instance shortcut_omc_trans A B
  : (A ⊆ B) -> (OneMoreConstructor A ⊆ B)
  := _.
Instance shortcut_omc_trans_apply A B T
  : (A ⊆ B) -> (Class (OneMoreConstructor A) T) -> Class B T
  := λ _ _, _.

(* To keep our metatheory as simple as possible, we say that an inference always has one premise and one conclusion. (To represent multiple premises, you can have formulas that represent "and", and have each rule pass along a "context".) *)

Inductive Ruleset FC :=
  | ruleset_empty : Ruleset FC
  | ruleset_inference : Rec FC -> Rec FC -> Ruleset FC
  | ruleset_and : Ruleset FC -> Ruleset FC -> Ruleset FC
  | ruleset_forall_formulas : Ruleset (OneMoreConstructor FC) -> Ruleset FC.

(* Inductive Ruleset_specializes FC : Ruleset FC -> Ruleset (OneMoreConstructor FC) -> Prop := *)
  
(* A ruleset asserts that certain inferences must be valid. This means it expresses a predicate on inference-sets. *)

Inductive Proof FC FC2 (_f : FC2 ⊆ FC): Ruleset FC -> Rec FC2 -> Rec FC2 -> Prop :=
  | proof_inference p c : Proof _ (ruleset_inference p c) (rec_embed p) (rec_embed c)
  | proof_and_left a b p c : Proof _ a p c -> Proof _ (ruleset_and a b) p c
  | proof_and_right a b p c : Proof _ b p c -> Proof _ (ruleset_and a b) p c
  | proof_specialization r p c : Proof _ r p c -> Proof _ (ruleset_forall_formulas r) p c
  | proof_transitivity r p m c : Proof _ r p m -> Proof _ r m c -> Proof _ r p c.


(* A ruleset asserts that certain inferences must be valid. This means it expresses a predicate on inference-sets. *)

Definition InfSet C := Rec C -> Rec C -> Prop.
Existing Class InfSet.
Definition infset_embed [C] (infs : InfSet C) {C2} {_c:C ⊆ C2} : InfSet C2
  := λ p c, infs (rec_embed p) (rec_embed c).

Fixpoint InfSet_obeys_Ruleset [C] (R : Ruleset C) (infs : InfSet C) : Prop :=
  match R with
  | ruleset_empty => True
  | ruleset_inference p c => infs p c
  | ruleset_and A B => InfSet_obeys_Ruleset A _ ∧ InfSet_obeys_Ruleset B _
  | ruleset_forall_formulas F => ∀ (x : Rec C),
     InfSet_obeys_Ruleset F (infset_embed (_c := (λ _ _, {| omc_new_rec_case := (x _ _) |})) infs)
  end.
  
Fixpoint Ruleset_embed [C C2] [e : C2 ⊆ C] (R : Ruleset C)  : Ruleset C2 :=
  match R with
  | ruleset_empty => ruleset_empty _
  | ruleset_inference p c => ruleset_inference (rec_embed p) (rec_embed c)
  | ruleset_and A B => ruleset_and (Ruleset_embed A) (Ruleset_embed B)
  | ruleset_forall_formulas F => ruleset_forall_formulas (Ruleset_embed (e := λ _ _, {| omc_new_rec_case := omc_new_rec_case |}) F)
  end.

(* And we say that one ruleset is "derivable" from another if, whenever an inference-set obeys the first, it also obeys the second. (Also, inference-sets intrinsically obey transitivity.) *)

Definition transitivity [C] (infs : InfSet C) : Prop
  := ∀ a b c, infs a b -> infs b c -> infs a c.

Definition derivable C (R S : Ruleset C) := ∀ infs, transitivity infs -> InfSet_obeys_Ruleset R infs -> InfSet_obeys_Ruleset S infs.

Definition infs_provable_from C (rules : Ruleset C) : InfSet C
  := λ p c, ∀ infs, 
    transitivity infs ->
    InfSet_obeys_Ruleset rules infs ->
    infs p c.

(****************************************************
   Relations between internal and external meaning
****************************************************)

(* …but we want to view these formulas as not just objects, but representations of mathematical truths. Specifically, we introduce the concept of a "semantics", saying whether formulas mean _rulesets_.

In this case, we will be passing around _two_ formula-constructor-classes, which I call the "quoting type" (conventionally named Q, with constructors named QC) and the "judged type" (conventionally named J, with constructors named JC). *)

Definition Semantics QC JC := Rec QC -> Ruleset JC -> Prop.

Definition derivations_provable_from QC JC (S : Semantics QC JC) (R : Ruleset QC) : Ruleset JC -> Ruleset JC -> Prop 
  := λ p c, ∃ qp qc, S qp p ∧ S qc c ∧ infs_provable_from R qp qc.

(****************************************************
                    Goals of IC
****************************************************)


Definition IncludesInferencesBetweenRulesetsThatMatch QC JC
  (S : Semantics QC JC)
  (R : Ruleset QC)
  (CountsAsTrue : Ruleset JC -> Prop)
  := ∀ p c,
    ((CountsAsTrue p) -> (CountsAsTrue c))
    ->
    derivations_provable_from S R p c.


Definition ContainsOnlyTrueDerivations QC JC (S : Semantics QC JC)
  (R : Ruleset QC) := ∀ p c, derivations_provable_from S R p c -> derivable p c.
Definition ContainsAllTrueDerivations QC JC (S : Semantics QC JC)
  (R : Ruleset QC) := ∀ p c, derivable p c -> derivations_provable_from S R p c.

  (* ∀ P C, ((ContainsOnlyTrueDerivations S P) -> (ContainsOnlyTrueDerivations S C)) -> derivations_provable_from R P C. *)

(* Ordinal hierarchy of rule sets, each of which internalizes all meta-theoretic reasoning for all those below it. *)

Definition Level0 C (S : Semantics C C)
  (R : Ruleset C) :=
  IncludesInferencesBetweenRulesetsThatMatch S R (
    λ r, ContainsOnlyTrueDerivations S r).
  
Definition Internalizes C (S : Semantics C C)
  (R : Ruleset C)
  Index
  (Rs : Index -> Ruleset C) := 
  ∀ i,
  IncludesInferencesBetweenRulesetsThatMatch S R (
    λ r, derivable (Rs i) r).

  (* IncludesInferencesBetweenRulesetsThatMatch S R (
    λ r, ∃ i, derivable (Rs i) r). *)

Definition Internalizes C (S : Semantics C C)
  (R : Ruleset C)
  Index
  (Rs : Index -> Ruleset C) := IncludesInferencesBetweenRulesetsThatMatch S R (
    λ r, ∃ i,
      derivations_provable_from S (Rs i) (ruleset_empty _) r
    ).

Inductive RulesetSet C :=
  ruleset_set Index : (Index -> Ruleset C) -> RulesetSet C.

Definition Internalizes C
  (S : Semantics C C)
  (R : Ruleset C)
  (Rs : RulesetSet C) :=
    match Rs with
      ruleset_set Index Rs => ∀ i p c,
        ((derivations_provable_from S (Rs i) (ruleset_empty _) p) -> (derivations_provable_from S (Rs i) (ruleset_empty _) c))
        ->
        derivations_provable_from S R p c
      end.

(****************************************************
                     scratchpad
****************************************************)

Inductive Proposition FC :=
  | prop_inference : Ruleset FC -> Ruleset FC -> Proposition FC
  | prop_says_means : Ruleset FC -> Formula -> Ruleset FC -> Proposition FC
  | prop_and : Proposition FC -> Proposition FC -> Proposition FC
  | prop_forall_formulas : Proposition (OneMoreConstructor FC) -> Proposition FC.

Inductive _Type :=
  | _Proposition : _Type
  | Forall : _Type -> _Type -> _Type.


Inductive Ruleset :=
  | ruleset_inference : Formula -> Formula -> Ruleset
  | ruleset_semantics_says : Formula -> Formula -> Formula -> Ruleset
  | ruleset_and : Ruleset -> Ruleset -> Ruleset
  | ruleset_forall_formulas : (Formula -> Ruleset) -> Ruleset.



Inductive Semantics {FC} OC :=
  | semantics_represents : (Rec FC) -> (Rec OC) -> Semantics FC OC
  | semantics_and : Semantics FC OC -> Semantics FC OC -> Semantics FC OC
  | semantics_forall_formula : (Semantics (OneMoreConstructor (OneMoreConstructor FC)) OC) -> Semantics FC OC
  | semantics_forall_object : (Semantics (OneMoreConstructor FC) (OneMoreConstructor OC)) -> Semantics FC OC
with Object FC OC := 
  | object_formula : Formula -> Object FC OC
  | object_ruleset : Ruleset -> Object FC OC
  | object_semantics : Semantics FC OC -> Object FC OC.

Parameter represents : Formula -> Formula -> Formula.
Definition IC_semantics : Semantics :=
  (* semantics_forall_formula (λ qf f,
    semantics_forall_object (λ qo o,
      semantics_represents (represents qf qo) (semantics_represents f o)
    )
  ) *)
  [∀ , dfkjdjfsl]
  semantics_forall_formula (
     semantics_forall_object (
      semantics_represents (represents (FC.1) (FC.2)) (object_semantics (semantics_represents (FC.3) (OC.1)))
    )
  )
  semantics_forall_semantics (
     semantics_forall_semantics (
      semantics_represents (and (FC.1) (FC.2)) (object_semantics (semantics_and (SC.1) (SC.2))))
    )
  ).
  
Inductive Proposition :=
  | prop_derivable : Ruleset -> Ruleset -> Proposition
  | prop_semantics_says : Semantics -> Formula -> Object -> Proposition
  | prop_and : Proposition -> Proposition -> Proposition
  | prop_forall : (Formula -> Proposition) -> Proposition.



Definition FEnv := Ruleset -> Prop.
Definition PEnv := Proposition -> Prop.

Parameter fenv_obeys_ruleset : FEnv -> Ruleset -> Prop.
Definition prop_is_true (p : Proposition) : Prop := 
  match p with
    | prop_implies a b => ∀ e, env_obeys_ruleset e a -> env_obeys_ruleset e b
    | prop_semantics_says => 
    end.
