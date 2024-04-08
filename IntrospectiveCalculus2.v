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

Theoretically, this is "simpler" than Coq's `Inductive` types (constructors come _before_ inductive instances), but in Coq, it's not elementary. So to represent a "set of constructors", we use a typeclass, where the typeclass methods are the constructors. 

Here we must do some bureaucracy about how we'll use typeclasses. *)

(* Sometimes we need to pass a typeclass as a function argument. This is fine because a typeclass is an ordinary value, but Coq's features for using typeclasses _implicitly_ don't have a built-in way to treat a local variable as a typeclass. To work around this, we make a wrapper class "Class", which is technically the identity function but is always treated as a typeclass. So when we want a local variable `C` to be treated as a typeclass, we say `Class C` instead. This is the same thing, but counts as a typeclass for implicits. *)
Definition Class [P:Type] (p:P) := p.
Existing Class Class.
Hint Unfold Class : typeclass_instances.
(* Implicit Type C : Prop -> Prop. *)

(* Given such a class, the corresponding _formula type_ is the inductive type with those constructors, which we represent as the type of functions that can construct an arbitrary output by invoking the induction cases: *)
Definition Ind (C : Prop -> Prop) := ∀ T (_:Class C T), T.

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

Instance subclass_apply {A B} {R}
  : (A ⊆ B) -> Class A R -> Class B R
  := λ ab AR, ab _ AR.

(* If you can construct something with certain constructors, you can also construct it with more constructors: *)
Definition ind_embed [C] (x : Ind C) {C2} {_c:C2 ⊆ C} : Ind C2
  := λ _ _, x _ _.

(****************************************************
   Relations between internal and external meaning
****************************************************)

Class ApplyConstructor (R : Prop) := {
    apply_case : R -> R -> R
  }.

Class FunctionConstructors (R : Prop) := {
    const_case : R
  ; fuse_case : R
  ; func_apply_cases :: ApplyConstructor R
  }.

Class PropositionConstructors (R : Prop) := {
    prop_func_cases :: FunctionConstructors R
  ; implies_case : R
  ; and_case : R
  ; forall_quoted_formulas_case : R
  }.

Instance aplc_class_unwrap :
  ∀ [R], Class ApplyConstructor R ->
         ApplyConstructor R := λ _ b, b.
Instance funcc_class_unwrap :
  ∀ [R], Class FunctionConstructors R ->
         FunctionConstructors R := λ _ b, b.
Instance propc_class_unwrap :
  ∀ [R], Class PropositionConstructors R ->
         PropositionConstructors R := λ _ b, b.
Instance shortcut_funcc_aplc :
  ∀ [R], Class FunctionConstructors R ->
         ApplyConstructor R := λ _ _, _.
Instance shortcut_propc_funcc :
  ∀ [R], Class PropositionConstructors R ->
         FunctionConstructors R := λ _ _, _.
Instance shortcut_propc_aplc :
  ∀ [R], Class PropositionConstructors R ->
         ApplyConstructor R := λ _ _, _.
Instance subclass_funcc_aplc : FunctionConstructors ⊆ ApplyConstructor := λ _ _, _.
Instance subclass_propc_funcc : PropositionConstructors ⊆ FunctionConstructors := λ _ _, _.
Instance subclass_propc_aplc : PropositionConstructors ⊆ ApplyConstructor := _.
         
Definition apply [C] [_ : C ⊆ ApplyConstructor] (f x : Ind C) : Ind C := λ _ _, apply_case (f _ _) (x _ _).
Definition const {C} {_ : C ⊆ FunctionConstructors} : Ind C := λ _ _, const_case.
Definition fuse {C} {_ : C ⊆ FunctionConstructors} : Ind C := λ _ _, fuse_case.
Definition f_implies {C} {_ : C ⊆ PropositionConstructors} : Ind C := λ _ _, implies_case.
Definition f_and {C} {_ : C ⊆ PropositionConstructors} : Ind C := λ _ _, and_case.
Definition forall_quoted_formulas {C} {_ : C ⊆ PropositionConstructors} : Ind C := λ _ _, forall_quoted_formulas_case.

Notation "[ x y ]" := (apply x y)
 (at level 0, x at next level, y at next level).
Notation "[ x y .. z ]" := (apply .. (apply x y) .. z)
 (at level 0, x at next level, y at next level).
Notation "[ x -> y ]" := [f_implies x y] (at level 0, x at next level, y at next level).
Notation "[ x & y ]" := [f_and x y]
  (at level 0, x at next level, y at next level).
Notation "[ ⋀ x ]" := [forall_quoted_formulas x]
  (at level 0, x at next level).

Inductive UnfoldStep [C] [_cfn : C ⊆ FunctionConstructors] : Ind C -> Ind C -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c].

Inductive UnfoldPath [C] [_cfn : C ⊆ FunctionConstructors] : Ind C -> Ind C -> Prop :=
  | unfold_path_refl f : UnfoldPath f f
  | unfold_path_step_then f g h : UnfoldStep f g -> UnfoldPath g h -> UnfoldPath f h.

Class OneMoreConstructor (C:Prop->Prop) (R : Prop) := {
    omc_embed_case : Class C R
  ; omc_new_case : R
  }.

Definition omc_new {C} : Ind (OneMoreConstructor C) := λ _ _r, @omc_new_case _ _ _r.

Instance omc_class_unwrap [C R] :
  Class (OneMoreConstructor C) R ->
         OneMoreConstructor C R := λ c, c.
Instance omc_subclass {C}
  : OneMoreConstructor C ⊆ C := λ _ _, omc_embed_case.
Instance shortcut_omc_trans A B
  : (A ⊆ B) -> (OneMoreConstructor A ⊆ B)
  := _.
Instance shortcut_omc_trans_apply A B T
  : (A ⊆ B) -> (Class (OneMoreConstructor A) T) -> Class B T
  := λ _ _, _.
Instance shortcut_omc_func_aplc A T
  : (A ⊆ FunctionConstructors) -> (Class (OneMoreConstructor A) T) -> Class ApplyConstructor T
  := λ _ _, _.

(* Propositions are formulas that say things about other formulas, but there's no intrinsic reason those formulas have to use the _same grammar_. So we will often be passing around _two_ formula-constructor-classes, which I call the "viewing type" (conventionally named V, with constructors named VC) and the "target type" (conventionally named T, with constructors named TC). *)

Implicit Type VC : Prop -> Prop.
Implicit Type TC : Prop -> Prop.

(* We also deal with "quoted formulas". To say that a V-formula is a quoted version of a T-formula, we need to define the MeansQuoted relation (MQ for short). This relation is only well-defined once you first specify the V and T constructors. It is also a dependent type; here we define the return-type of  *)
Definition MQR VC TC := Ind VC -> Ind TC -> Prop.

(* ...and usually, we need to be talking about _constructors_ (MQC) for that relation, because it must be just as extensible as the formula types. Since MQR uses VC and TC in "negative" positions (LHS of an implication), it doesn't naturally embed in subclasses the way Ind does, so we need to have the constructors explicitly allow subclasses: *)
Definition MQCT VC TC :=
  ∀ VC2 (eV : VC2 ⊆ VC) TC2 (eT : TC2 ⊆ TC), MQR VC2 TC2 -> Prop.
Existing Class MQCT.

(* We also define _inductive instances_ of MQ constructors: *)
Definition MQInd [VC TC] (MQC : MQCT VC TC) (qx : Ind VC) (x : Ind TC)
  :=
  ∀ VC2 eV TC2 eT R (_mq : MQC VC2 eV TC2 eT R), R (ind_embed qx) (ind_embed x).


(* ...the main case of which is to add one additional variable to each of V and T, and say that the new V-variable is a quoted version of the new T-variable. *)
Definition OneMoreMQConstructor [VC TC] (qx : Ind VC) (x: Ind TC) (MQC : MQCT VC TC) : MQCT VC TC
  := λ VC2 eV TC2 eT R,
    (MQC _ _ _ _ R) ∧
    (R (ind_embed qx) (ind_embed x)).

Definition MQCEmbed
  [VC TC] (MQC : MQCT VC TC) {VC2 TC2} {eV: VC2 ⊆ VC} {eT: TC2 ⊆ TC}
  : MQCT VC2 TC2
  := λ _ _ _ _ MQ, (MQC _ _ _ _ MQ).

Definition OneMoreQuotvar [VC TC] (MQC : MQCT VC TC)
  : MQCT (OneMoreConstructor VC) (OneMoreConstructor TC)
  :=
  OneMoreMQConstructor omc_new omc_new (MQCEmbed MQC).

Definition MQCSubclass [VC TC] (MQC1 MQC2 : MQCT VC TC)
  := ∀ VC2 eV TC2 eT MQ,
    MQC1 VC2 eV TC2 eT MQ ->
    MQC2 VC2 eV TC2 eT MQ.


(* Propositions represent sets of rules of inference, so we define a ruleset type: *)

Inductive Ruleset TC :=
  | ruleset_implies : Ind TC -> Ind TC -> Ruleset TC
  | ruleset_and : Ruleset TC -> Ruleset TC -> Ruleset TC
  | ruleset_forall : Ruleset (OneMoreConstructor TC) -> Ruleset TC
   .

(* A ruleset is a constraint on what inferences may be valid: for example, the rule (A & B) |- (B & A) says that for all values of B and A, the inference (A & B) |- (B & A) must be valid.

In practice, we don't use the full generality of arbitrary constraints. Our only recursive constraint is transitivity ((A |- B) and (B |- C) imply (A |- C)), and there isn't a proposition that represents it, it's just always true. All propositions represent simple positive constraints, which just say that certain inferences must be valid.

Nevertheless, the simplest way to define Rule is as a predicate on InfSets, which are predicates on inferences. (An InfSet takes two formulas P,C and says whether it holds inference P |- C as valid.)

We must ask what the actual type of Ruleset is. A Ruleset must be agnostic to grammar-extensions, but you may express a rule that assumes particular constructors exist (otherwise, our example rule wouldn't be able to express &). Therefore: *)

Definition InfSet TC := Ind TC -> Ind TC -> Prop.
Existing Class InfSet.
Definition infset_embed [C] (infs : InfSet C) {C2} {_c:C ⊆ C2} : InfSet C2
  := λ p c, infs (ind_embed p) (ind_embed c).

Fixpoint Ruleset_to_Coq [TC] (R : Ruleset TC) (infs : InfSet TC) : Prop :=
  match R with
  | ruleset_implies p c => infs p c
  | ruleset_and A B => Ruleset_to_Coq A _ ∧ Ruleset_to_Coq B _
  | ruleset_forall F => ∀ (x : Ind TC),Ruleset_to_Coq F (infset_embed (_c := (λ _ _, {| omc_new_case := (x _ _) |})) infs)
  end.
  
Fixpoint Ruleset_embed [TC TC2] [eT : TC2 ⊆ TC] (R : Ruleset TC)  : Ruleset TC2 :=
  match R with
  | ruleset_implies p c => ruleset_implies (ind_embed p) (ind_embed c)
  | ruleset_and A B => ruleset_and (Ruleset_embed A) (Ruleset_embed B)
  | ruleset_forall F => ruleset_forall (Ruleset_embed (eT := λ _ _, {| omc_new_case := omc_new_case |}) F)
  end.


Inductive FormulaMeansProp {VC TC} {MQC : MQCT VC TC}
  {_vp:VC ⊆ PropositionConstructors}
  : Ind VC -> Ruleset TC -> Prop :=

  | fmp_implies [qp qc p c]
      :
      MQInd MQC qp p ->
      MQInd MQC qc c ->
      FormulaMeansProp [qp -> qc] (ruleset_implies p c)

  | fmp_unfold [a b B] :
      UnfoldStep a b ->
      FormulaMeansProp b B ->
      FormulaMeansProp a B

  | fmp_and [a b A B] :
      FormulaMeansProp a A ->
      FormulaMeansProp b B ->
      FormulaMeansProp [a & b] (ruleset_and A B)

  | fmp_forall_quoted_formulas
      (f : Ind VC)
      (F : Ruleset (OneMoreConstructor TC))
      :
      FormulaMeansProp (MQC := OneMoreQuotvar MQC)
        [(ind_embed f) omc_new]
        F
      ->
      FormulaMeansProp
        [⋀ f]
        (ruleset_forall (@F))
  .

(****************************************************
       Concrete (quotation?)
****************************************************)

(* In order to make quoted versions of ordinary formulas, we need an extra constructor for quoting stuff: *)

Class FormulaConstructors R := {
      quote_case : R
    ; formula_prop_case :: PropositionConstructors R
  }.

Instance formulac_class_unwrap :
  ∀ [R], Class FormulaConstructors R ->
         FormulaConstructors R := λ _ b, b.
Instance shortcut_formulac_propc :
  ∀ [R], Class FormulaConstructors R ->
         PropositionConstructors R := λ _ _, _.
Instance shortcut_formulac_funcc :
  ∀ [R], Class FormulaConstructors R ->
         FunctionConstructors R := λ _ _, _.
Instance shortcut_formulac_aplc :
  ∀ [R], Class FormulaConstructors R ->
         ApplyConstructor R := λ _ _, _.
Instance subclass_formulac_propc : FormulaConstructors ⊆ PropositionConstructors := λ _, _.
Instance subclass_formulac_funcc : FormulaConstructors ⊆ FunctionConstructors := _.
Instance subclass_formulac_aplc : FormulaConstructors ⊆ ApplyConstructor := _.

Definition f_quote {C} {_ : C ⊆ FormulaConstructors} : Ind C := λ _ _, quote_case.

Inductive IsAtom : Ind FormulaConstructors -> Prop :=
  | atom_const : IsAtom const
  | atom_fuse : IsAtom fuse
  | atom_implies : IsAtom f_implies
  | atom_and : IsAtom f_and
  | atom_forall_quoted_formulas : IsAtom forall_quoted_formulas
  | atom_quote : IsAtom f_quote
  .

Definition FcMQC : MQCT FormulaConstructors FormulaConstructors :=
  λ VC2 eV TC2 eT R,
    (∀ f a, IsAtom a ->
      UnfoldPath f (ind_embed a) -> R [f_quote f] (ind_embed a))
    ∧
    (∀ qa qb b, UnfoldStep qa qb -> R qb b -> R qa b)
    ∧
    (∀ qa a qb b, R qa a -> R qb b ->
      R [f_quote qa qb] [a b])
    .


(****************************************************
            Utilities for axioms of IC
****************************************************)

(* Definition StandardFormula := Ind FormulaConstructors. *)
  

Notation "{ x → y }" := (ruleset_implies x y)
  (at level 0, x at next level, y at next level).
Notation "{ x ∧ y }" := (ruleset_and x y)
  (at level 0, x at next level, y at next level).
Notation "{ ⋀ f }" := (ruleset_forall f)
  (at level 0, f at next level).

Notation "^ x" := (@ind_embed _ x _ omc_subclass) (at level 0).
Notation "'α'" := omc_new (at level 0).
Notation "'β'" := (^α) (at level 0).
Notation "'γ'" := (^β) (at level 0).

Definition ICR := Ruleset FormulaConstructors.
Definition AxiomRepresenting (rule : ICR) := ∃ f, FormulaMeansProp (MQC := FcMQC) f rule.

Definition fmp_unfold_path {VC TC} {MQC : MQCT VC TC}
  {_vp:VC ⊆ PropositionConstructors} [a b B] : UnfoldPath a b ->
      FormulaMeansProp b B ->
      FormulaMeansProp a B.
  intros path _f.
  induction path.
  exact _f.
  exact (fmp_unfold H (IHpath _f)).
Defined.

Definition functionize_prop [VC TC] [_vp : VC ⊆ PropositionConstructors] (P : Ruleset (OneMoreConstructor TC)) (p : Ind (OneMoreConstructor VC)) [MQC] (_pP : FormulaMeansProp (MQC := OneMoreQuotvar MQC) p P) : ∃ f : Ind VC, FormulaMeansProp (MQC := OneMoreQuotvar MQC) [(ind_embed f) omc_new] P.

Create HintDb abstraction_elimination.

Definition bubble_embed_in_const {C} {_c : C ⊆ FunctionConstructors} : @const (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) const := eq_refl.
Definition bubble_embed_in_fuse {C} {_c : C ⊆ FunctionConstructors} : @fuse (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) fuse := eq_refl.
Definition bubble_embed_in_implies {C} {_c : C ⊆ PropositionConstructors} : @f_implies (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) f_implies := eq_refl.
Definition bubble_embed_in_and {C} {_c : C ⊆ PropositionConstructors} : @f_and (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) f_and := eq_refl.
Definition bubble_embed_in_forall {C} {_c : C ⊆ PropositionConstructors} : @forall_quoted_formulas (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) forall_quoted_formulas := eq_refl.
Definition bubble_embed_in_quote {C} {_c : C ⊆ FormulaConstructors} : @f_quote (OneMoreConstructor C) _ = ind_embed (_c := omc_subclass) f_quote := eq_refl.

Hint Rewrite bubble_embed_in_const : abstraction_elimination.
Hint Rewrite bubble_embed_in_fuse : abstraction_elimination.
Hint Rewrite bubble_embed_in_implies : abstraction_elimination.
Hint Rewrite bubble_embed_in_and : abstraction_elimination.
Hint Rewrite bubble_embed_in_forall : abstraction_elimination.
Hint Rewrite bubble_embed_in_quote : abstraction_elimination.

Definition bubble_embed_in_apply {C} {_c : C ⊆ FunctionConstructors} a b : @apply (OneMoreConstructor C) _ (ind_embed a) (ind_embed b) = ind_embed (_c := omc_subclass) (apply a b) := eq_refl.

Hint Rewrite bubble_embed_in_apply : abstraction_elimination.

Lemma UnfoldPath_in_lhs [C] [_cfn : C ⊆ FunctionConstructors] (a b c : Ind C) : UnfoldPath (_cfn := _cfn) a b -> UnfoldPath (_cfn := _cfn) [a c] [b c].
  intro.
  induction H.
  apply unfold_path_refl.
  eapply unfold_path_step_then;[|exact IHUnfoldPath].
  apply unfold_in_lhs.
  assumption.
Qed.

Lemma abstraction_elimination_const {C} {_c : C ⊆ FunctionConstructors} b : UnfoldPath (_cfn := subclass_trans omc_subclass _c) [(ind_embed [const b]) α] (ind_embed b).
  eapply unfold_path_step_then; [|apply unfold_path_refl].
  apply unfold_const.
Qed.

Definition f_id {C} {_c : C ⊆ FunctionConstructors} : Ind C := [fuse const const].

Lemma abstraction_elimination_id {C} {_c : C ⊆ FunctionConstructors} : UnfoldPath (_cfn := subclass_trans omc_subclass _c) [(ind_embed f_id) α] α.
  eapply unfold_path_step_then.
  apply unfold_fuse.
  eapply unfold_path_step_then; [|apply unfold_path_refl].
  apply unfold_const.
Qed.

Lemma abstraction_elimination_fuse {C} {_c : C ⊆ FunctionConstructors} a b q : UnfoldPath (_cfn := subclass_trans omc_subclass _c) [(ind_embed a) α] q ->
UnfoldPath [(ind_embed [fuse a b]) α] [q [b α]].
  intro.
  eapply unfold_path_step_then.
  apply unfold_fuse.
  apply UnfoldPath_in_lhs.
  assumption.
Qed.

Ltac abstraction_elimination := repeat (
  autorewrite with abstraction_elimination;
  match goal with
  | |- UnfoldPath ((ind_embed ?f) α) (ind_embed ?B) => apply abstraction_elimination_const
  | |- UnfoldPath [(ind_embed ?f) α] α => apply abstraction_elimination_id
  | |- UnfoldPath ((ind_embed ?f) α) (apply ?B ?C) => apply abstraction_elimination_fuse
  end).
  
(* Print bubble_embed_in_apply.
  Set Printing Implicit. *)

(* UnfoldPath
  (apply (ind_embed ?f) α)
  (apply (apply f_implies α)
  (apply
  (apply f_quote
  (apply
  (apply f_quote
  (apply f_quote
  f_and))
  α))
  α)) *)

(****************************************************
              Concrete axioms of IC
****************************************************)

Definition rule_dup : ICR := {⋀ {α → [α & α]}}.
Definition rule_drop : ICR := {⋀ {⋀ {[α & β] → α}}}.
Definition rule_and_sym : ICR := {⋀ {⋀ {[α & β] → [β & α]}}}.
Definition rule_and_assoc_left : ICR := {⋀ {⋀ {⋀ {[α & [β & γ]] → [[α & β] & γ]}}}}.
Definition rule_and_assoc_right : ICR := {⋀ {⋀ {⋀ {[[α & β] & γ] → [α & [β & γ]]}}}}.

Lemma dfkjdjf 
VC2 
(eV : VC2
⊆ OneMoreConstructor
  FormulaConstructors) a b : (ind_embed (_c := omc_subclass)
  (apply a b)) = (apply (ind_embed a) (ind_embed b)).
    (* Set Printing Implicit. *)
    reflexivity.
Qed.

Print rule_dup.
Definition ax_dup : AxiomRepresenting rule_dup.
  unfold AxiomRepresenting.
  unfold rule_dup.
  econstructor.
  apply fmp_forall_quoted_formulas.
  eapply fmp_unfold_path.
  2: {
    apply fmp_implies; unfold MQInd; intros;destruct _mq;
    destruct H.
    apply H0.
    destruct H1.
    (* unfold ind_embed. *)
    (* pose (H2 _ _ _ _ H0 H0) as x. *)
    (* unfold ind_embed,apply in x. *)
    (* change ( (ind_embed (_c := eT)
  (apply (apply f_and α) α))) with ( 
  (apply (ind_embed (_c := eT) (apply f_and α)) (ind_embed α))). *)
    instantiate (1 := ((apply (apply f_quote _) _))).
    (* instantiate (3 := f_quote). *)

    (* repeat change ( (ind_embed (_c := eV)
  (apply ?a ?b))) with (
  (apply (ind_embed (_c := eV) a) (ind_embed b))). *)
    (* change ( (ind_embed (_c := eT)
  (apply ?a ?b))) with (
  (apply (ind_embed (_c := eT) a) (ind_embed b))). *)
    (* unfold ind_embed,apply in *. *)
    apply H2.
    instantiate (1 := ((apply (apply f_quote _) _))).
    apply H2.
    instantiate (1 := ((apply f_quote f_and) )).
    change (R [f_quote (ind_embed f_and)] (ind_embed f_and)).
    apply H.
    constructor.
    constructor.
    apply H0.
    apply H0.
    
  }
  abstraction_elimination.
  autorewrite with abstraction_elimination.
  instantiate (1 := [fuse _ _]).
  Print abstraction_elimination_fuse.
  eapply abstraction_elimination_fuse.
  eapply (abstraction_elimination_fuse (C := FormulaConstructors) (_c := subclass_formulac_funcc)).

  
  eapply unfold_path_step_then.
  apply unfold_fuse.
  apply UnfoldPath_in_lhs.
  assumption.
(*   
  autorewrite with abstraction_elimination;
  match goal with
  | |- UnfoldPath ((ind_embed ?f) α) (ind_embed ?B) => apply abstraction_elimination_const
  | |- UnfoldPath [(ind_embed ?f) α] α => apply abstraction_elimination_id
  | |- UnfoldPath ((ind_embed ?f) α) (apply ?B ?C) => apply abstraction_elimination_fuse
  end). *)

Defined.

Definition IC_rules := 
  {
    {rule_dup ∧ rule_drop}
    ∧
    {rule_and_sym ∧ {rule_and_assoc_left ∧ rule_and_assoc_right}}
  }.

(****************************************************
              Definitions of inference
****************************************************)

Definition transitivity [TC] (infs : InfSet TC) : Prop
  := ∀ a b c, infs a b -> infs b c -> infs a c.


Definition infs_stated_by {TC} (rules : Ruleset TC) : InfSet TC
  := λ p c, ∀ infs,
    Ruleset_to_Coq rules infs ->
    infs p c.
Definition infs_provable_from {TC} (rules : Ruleset TC) : InfSet TC
  := λ p c, ∀ infs, 
    transitivity infs ->
    Ruleset_to_Coq rules infs ->
    infs p c.

Definition rules_implies [TC] (premise : Ruleset TC) (conclusion : Ruleset TC) : Prop
  := ∀ TC2 (eT : TC2 ⊆ TC) (infs : InfSet TC2), 
    transitivity infs ->
    Ruleset_to_Coq (Ruleset_embed premise) infs ->
    Ruleset_to_Coq (Ruleset_embed conclusion) infs.

Definition IC_provable_infs := infs_provable_from IC_rules.

(****************************************************
            Definitions of core metatheorems
****************************************************)

(* Principles behind VC/TC relationship here:
V-rules judge V-infs
V-infs are between V-formulas
V-formulas represent T-rules
We need to include, in the judgment, T-rules that are on extensions of the original TC
...so we need to have a matching extention to VC
*)

Definition MQFunctional [VC TC] (MQC : MQCT VC TC) := ∀ qx x (_x : MQInd MQC qx x) y (_y : MQInd MQC qx y), y = x.
Definition MQSurjective [VC TC] (MQC : MQCT VC TC) := ∀ x, ∃ qx, MQInd MQC qx x.
Definition MPFunctional [VC TC] [eV : VC ⊆ PropositionConstructors] (MQC : MQCT VC TC) := ∀ x X Y (_x : FormulaMeansProp x X) (_y : FormulaMeansProp x Y), Y = X.
Definition MPSurjective [VC TC] [eV : VC ⊆ PropositionConstructors] (MQC : MQCT VC TC) := ∀ X, ∃ x, FormulaMeansProp x X.

Definition InferenceIncludes [VC TC] [eV : VC ⊆ PropositionConstructors] (MQC : MQCT VC TC) (rules : Ruleset VC) 
:=
  ∀ VC2 (eV : VC2 ⊆ VC) TC2 (eT : TC2 ⊆ TC) (MQC2 : MQCT VC2 TC2) (_mq : MQCSubclass MQC2 (MQCEmbed MQC))
    (p c : Ind VC2)
    (pc_provable : infs_provable_from (Ruleset_embed rules) p c)
    (P C : Ruleset TC2)
    (_p : FormulaMeansProp (MQC:=MQC2) p P)
    (_c : FormulaMeansProp (MQC:=MQC2) c C)
        ,
        rules_implies P C.


Definition IncludesInference [VC TC] [eV : VC ⊆ PropositionConstructors] (MQC : MQCT VC TC) (rules : Ruleset VC) :=
  ∀ VC2 (eV : VC2 ⊆ VC) TC2 (eT : TC2 ⊆ TC) (MQC2 : MQCT VC2 TC2) (_mq : MQCSubclass MQC2 (MQCEmbed MQC))
    (P C : Ruleset TC2)
    (PC_implied : rules_implies P C)
    (p c : Ind VC2)
    (_p : FormulaMeansProp (MQC:=MQC2) p P)
    (_c : FormulaMeansProp (MQC:=MQC2) c C),
        infs_provable_from (Ruleset_embed rules) p c.


(****************************************************
            Proofs of MQFunctional
****************************************************)

Lemma FcMQCFunctional : MQFunctional FcMQC.
  intros qx x qxx.
  unfold MQInd in *.
  specialize (qxx FormulaConstructors _ FormulaConstructors _). 
  change (ind_embed qx) with (qx) in qxx.
  change (ind_embed x) with (x) in qxx.
  (* unfold ind_embed, subclass_apply, subclass_refl in qxx. cbn in qxx. *)
  (* specialize (qxx (λ qx x, ∀ y, )).  *)
  apply qxx. clear qxx.
  split; [ | split]; intros.
  specialize (_y FormulaConstructors _ FormulaConstructors _).
  change (ind_embed y) with (y) in _y.
  revert a H H0.
  generalize f.
  generalize y.
  apply _y.
Qed.

(****************************************************
            Proofs of MQSurjective
****************************************************)
Print nat_ind.
Lemma FcMQCSurjective : MQSurjective FcMQC.
  intro x.
  refine (x (∀ y, ∃ qx : Ind FormulaConstructors,
  MQInd FcMQC qx y) _).
  generalize x.
  apply x.
  split.
  apply x.
  split.

  apply (x (∀ y, ∃ qx : Ind FormulaConstructors,
  MQInd FcMQC qx y)).
  split.
∃ qx : Ind FormulaConstructors,
  MQInd FcMQC qx x
(****************************************************
            Proofs of InferenceIncludes
****************************************************)

Lemma rules_implies_trans C (X Y Z : Ruleset C) (XY : rules_implies X Y) (YZ : rules_implies Y Z) : rules_implies X Z.
  unfold rules_implies. intros. refine (YZ _ _ _ _ (XY _ _ _ _ _)); assumption.
Qed.

Lemma meaning_unique : 

Ltac iisetup := unfold InferenceIncludes; let pc_stated := fresh "pc_stated" in intros VC2 eV TC2 eT MQC _mq p c pc_provable; unfold infs_provable_from in pc_provable; cbn in pc_provable;
  apply pc_provable; clear pc_provable.
  (* (intros x y z P C _p _c || intros x y P C _p _c || intros x P C _p _c). *)
Definition inference_includes_drop : InferenceIncludes FcMQC rule_drop.
  iisetup.
  intros xy yz X Z _x _z.
  {apply rules_implies_trans.
  admit. }

  (* unfold ind_embed, subclass_apply, shortcut_omc_trans_apply, subclass_apply, omc_subclass. cbn. *)
  intros x y.
  intros P C _p _c.
  (* destruct _p. *)
  dependent destruction _p. 
  {discriminate x. admit. }
  { dependent destruction  H; discriminate x; admit. }
  apply ex_intro with (ruleset_and P P).
  apply ex_intro with (mi_and _p _p).
  unfold rules_implies. intros. cbn. split; assumption.
Qed.