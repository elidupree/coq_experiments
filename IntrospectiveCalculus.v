Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Require Import Ascii String.
Open Scope string_scope.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(****************************************************
              Typeclass practicalities
****************************************************)

(* We often want to view IC formulas as "extensible". That is, we know that the formula type has certain constructors, but don't guarantee that those are the ONLY constructors.

Theoretically, this is "simpler" than Coq's `Inductive` types (constructors come _before_ inductive instances), but in Coq, it's not elementary. So to represent a "set of constructors", we use a typeclass, where the typeclass methods are the constructors. Thus, anytime we have a type F with an instance of FormulaConstructors, we can view F as a legitimate "extension" of the concept of formulas.

Here we must do some bureaucracy about how we'll use typeclasses. *)

(* Sometimes we need to pass a typeclass as a function argument. This is fine because a typeclass is an ordinary value, but Coq's features for using typeclasses _implicitly_ don't have a built-in way to treat a local variable as a typeclass. To work around this, we make a wrapper class "Class", which is technically the identity function but is always treated as a typeclass. So when we want a local variable `C` to be treated as a typeclass, we say `Class C` instead. This is the same thing, but counts as a typeclass for implicits. *)
Definition Class [P] (p:P) := p.
Existing Class Class.
Hint Unfold Class : typeclass_instances.
Definition use_class {T P t} (c:@Class (T -> Type) P t) : P t := c.
(* Definition use_class {P T} (c:Class P T) : P T := c. *)

(* We also often want to extend a typeclass with additional constructors, while still leaving it open to still-further constructors. This gives us a _second typeclass_ that is a subclass of the first. It's useful to represent the subclass relation explicitly: *)
Definition SubclassOf {T} (Superclass Subclass : T -> Type) := ∀ T (_:Class Subclass T), Class Superclass T.
Existing Class SubclassOf.
Notation "R ⊆ S" := (SubclassOf S R) (at level 70).
Instance subclass_refl {T} {A : T -> Type}
  : (A ⊆ A)
  := λ x xA, xA.

(* Once we make an instance for subclass transitivity (A ⊆ B -> B ⊆ C -> A ⊆ C), we risk making instance-search diverge: The subgoal looking for (A ⊆ B) tries looking for some additional transitivity-instance (A ⊆ X) and (X ⊆ B), ad infinitum. So we have to set a limit on typeclass search: *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 3.
Instance subclass_trans {T} {A B C : T -> Type}
  : (A ⊆ B) ->
    (B ⊆ C) ->
    (A ⊆ C)
  := λ ab bc, λ x xA, bc _ (ab _ xA).

Definition test_subclass_trans {T} {A B C : T -> Type}
  : (A ⊆ B) -> (B ⊆ C) -> (A ⊆ C) := _.
Definition test_subclass_trans_2 {T} {A B C D : T -> Type}
  : (A ⊆ B) -> (B ⊆ C) -> (C ⊆ D) -> (A ⊆ D) := λ _ _ _, _.

(* Lemma subclass_trans_refl1 [T] [A B : T -> Type] (s : A ⊆ B) : 
  subclass_trans subclass_refl s = s.
  reflexivity.
Qed.
Lemma subclass_trans_refl2 [T] [A B : T -> Type] (s : A ⊆ B) : 
  subclass_trans s subclass_refl = s.
  reflexivity.
Qed. *)

Instance subclass_apply {T} {A B : T -> Type} {t}
  : (A ⊆ B) -> Class A t -> Class B t
  := λ ab At, ab _ At.

(* The definitions above treat a class as an arbitrary constraint, but *constructor* classes also have a positivity requirement, which we sometimes need to require explicitly: *)
(* Class ConstructorClass (C : Type -> Type) := {
    cc_embed : ∀ {a b} {_:C a}, (a -> b) -> C b
  }. *)

(****************************************************
   Relations between internal and external meaning
****************************************************)

Class ApplyConstructor F := {
    apply : F -> F -> F
  }.

Class FunctionConstructors F := {
    const : F
  ; fuse : F
  ; fc_ac :: ApplyConstructor F
  }.

Class PropositionConstructors F := {
    pc_fc :: FunctionConstructors F
  ; f_implies : F
  ; f_and : F
  ; f_forall_quoted_formulas : F
  }.

(* When we want to use PropositionConstructors methods, but only have our wrapper Class PropositionConstructors, we need to be able to unwrap it: *)
Instance pc_class_unwrap :
  ∀ {F}, Class PropositionConstructors F ->
         PropositionConstructors F := λ _ b, b.
Instance aplc_class_unwrap :
  ∀ {F}, Class ApplyConstructor F ->
         ApplyConstructor F := λ _ b, b.

(* And because we use a low depth limit, we need to provide some "shortcuts": *)
Instance shortcut_cpc_fnc F : Class PropositionConstructors F -> FunctionConstructors F := _.
Instance shortcut_cpc_aplc F : Class PropositionConstructors F -> ApplyConstructor F := λ _, _.

Notation "[ x y .. z ]" := (apply .. (apply x y) .. z)
 (at level 0, x at next level, y at next level).
Notation "[ x -> y ]" := [f_implies x y] (at level 0, x at next level, y at next level).
Notation "[ x & y ]" := [f_and x y]
  (at level 0, x at next level, y at next level).
Notation "[ ⋀ x ]" := [f_forall_quoted_formulas x]
  (at level 0, x at next level).

Inductive UnfoldStep {F} `{FunctionConstructors F} : F -> F -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c].


(* Notation "R ∧1 S" := (λ x, R x ∧ S x) (at level 70). *)
(* Notation "R ×1 S" := (λ x, prod (R x) (S x)) (at level 70). *)
(* Notation "R ∧3 S" := (λ x y z, R x y z ∧ S x y z) (at level 70). *)
(* Notation "R ∧4 S" := (λ x y z w, R x y z w ∧ S x y z w) (at level 70). *)
(* Notation "R ⊆ S" := (∀ x, R x -> S x) (at level 70). *)
(* Definition Construction Constructors := ∀ {T} `{Constructors T}, T. *)

Class OneMoreConstructor Constrs F := {
    omc_embed : Class Constrs F
  ; omc_new : F
  }.

Instance onemore_class_unwrap :
  ∀ {Constrs F}, Class (OneMoreConstructor Constrs) F ->
         OneMoreConstructor Constrs F := λ _ _ c, c.
         
Instance OneMoreConstructor_subclass {C}
  : OneMoreConstructor C ⊆ C
  := λ _ _, omc_embed.
  
Instance shortcut_omc_trans A B
  : (A ⊆ B) -> (OneMoreConstructor A ⊆ B)
  := _.
  
Instance shortcut_omc_trans_apply A B T
  : (A ⊆ B) -> (Class (OneMoreConstructor A) T) -> Class B T
  := λ _ _, _.

(* Propositions are formulas that say things about other formulas, but there's no intrinsic reason those formulas have to use the _same grammar_. So we will often be passing around _two_ formula-constructor-classes, which I call the "viewing type" (conventionally named V, with constructors named VC) and the "target type" (conventionally named T, with constructors named TC).

The gotcha: We don't want one of them to be accidentally passed where the other is expected (especially implicitly!)... but they are the same type!

So, we make the types different _in name_, which means Coq will implicitly pass them only in the correct role. *)
Definition VConsClass := Type -> Type.
Definition TConsClass := Type -> Type.
Implicit Type VC : VConsClass.
Implicit Type TC : TConsClass.
Existing Class VConsClass.
Existing Class TConsClass.
(* ...but when a Type -> Type is needed in a context that can disambiguate which one, we do want Coq to know that a VConsClass or TConsClass will suffice: *)
Hint Unfold VConsClass : typeclass_instances.
Hint Unfold TConsClass : typeclass_instances.


(* Set Typeclasses Debug Verbosity 2. *)
Definition test_subclass_apply_with_VConsClass
  {VC VC2:VConsClass} {V} (v:Class VC2 V) `{VC2 ⊆ VC}
  : Class VC V := _.
  
Definition test_subclass_apply_with_VConsClass_2
  {C : Type -> Type} {VC2 : VConsClass} {V:Type} (v:@Class VConsClass VC2 V) `{VC2 ⊆ C}
  : @Class (Type -> Type) C V := _.

Definition test_OneMoreConstructor_apply_and_unwrap_with_VConsClass
  {VC oVC2:VConsClass} `{oVC2 ⊆ OneMoreConstructor VC}
  {V} (_v:Class oVC2 V)
  : OneMoreConstructor VC V := _.


(* Given any constructor-class, we may also be interested in the inductive type with those constructors. We will be using this a lot, so it gets a short name.

Unfortunately, we can't express the statement `C (Ind C)`, because it results in universe inconsistency. This would work fine in the Prop universe; I think I could theoretically rewrite most of the code here to use Prop instead of Type, and have it work. But Coq generally expects you to be working in the predicative hierarchy instead, and can't abstract over Prop vs Type in the way we'd need. But, I think it turns out to be unnecessary to express `C (Ind C)` anyway (we can just convert to other forms). *)
Definition Ind C := ∀ T (_:Class C T), T.

Definition ind_on_stricter_constructors C C2
  : (C2 ⊆ C) -> Ind C -> Ind C2
  := λ _c x T eT, x T _.


(* We also deal with "quoted formulas". To say that a V-formula is a quoted version of a T-formula, we need to define the MeansQuoted relation (MQ for short). This relation is only well-defined once you first specify the V and T constructors: *)
Definition MQT V TC := V -> Ind TC -> Prop.

Definition mqt_on_looser_constructors [V TC TC2] [eT : (TC ⊆ TC2)]
  : MQT V TC -> MQT V TC2
  := λ MQ v t, MQ v (ind_on_stricter_constructors eT t).

(* ...and usually, we need to be talking about _constructors_ (MQC) for that relation, because it must be just as extensible as the formula types: *)
Definition MQCT VC TC :=
  ∀ V (_v:Class VC V) (TC2 : TConsClass) (eT : TC2 ⊆ TC), MQT V TC2 -> Prop.
Existing Class MQCT.

(* We also define how an MQCT relates _inductive instances_ of VC and TC - which is the same thing as saying an inductive instance of those MQ constructors: *)
(* We also need to be able to say an inductive instance of those MQ constructors ("this concrete qx is forced by the constructors to mean a quoted version of this concrete x, no matter what embedding we're in..."); "any MQ that obeys MQC (bearing in mind that MQC can judge any MQ on any extension of TC) must hold (MQ qx x)" *)
Definition MQInd {VC TC V} {_v:Class VC V} (qx : V) (x : Ind TC) {MQC : MQCT VC TC}
  :=
  ∀ TC2 eT MQ (_mq : MQC _ _ _ _ MQ), MQ qx (ind_on_stricter_constructors eT x).
Print MQInd.

(* ...and to say that a particular Ind VC always construct something that quotes an Ind TC: *)
Definition VInd_MQInd {VC TC V} {_v:Class VC V} (qx : Ind VC) (x : Ind TC) {MQC : MQCT VC TC}
  := ∀ V _v, MQInd (qx V _v) x.

(* Definition MQInd {VC TC} (qx : Ind VC) (x : Ind TC) {MQC : MQCT}
  :=
  ∀ V (_v:Class VC V) T (_t:Class TC T) (MQ : MQT),
    MQC _ _ _ _ MQ ->
    MQ _ _ _ _ (qx _ _) (x _ _). *)

(* ...the main case of which is to add one additional variable to each of V and T, and say that the new V-variable is a quoted version of the new T-variable. *)

Definition OneMoreMQConstructor [VC TC] (qx : Ind VC) (x: Ind TC) (MQC : MQCT VC TC) : MQCT VC TC
  := λ V _v TC2 eT MQ,
    (MQC _ _ _ _ MQ) ∧
    (∀ T (_t:Class (OneMoreConstructor TC) T), (MQ (qx _ _) (λ _ _, x _ _))).

Definition MQCOnStricterFormulaTypes
  {VC TC VC2 TC2} {eV: VC2 ⊆ VC} {eT: TC2 ⊆ TC}
  (MQC : MQCT VC TC) : MQCT VC2 TC2
  := λ _ _ _ _ MQ, (MQC _ _ _ _ MQ).

Print MQCOnStricterFormulaTypes.

Definition MQCSubclassOf [VC TC] (MQC1 MQC2 : MQCT VC TC)
  := ∀ V _v TC2 eT MQ, MQC1 V _v TC2 eT MQ -> MQC2 V _v TC2 eT MQ.

Lemma MQCSubclassOf_refl [VC TC] (MQC : MQCT VC TC) : MQCSubclassOf MQC MQC.
  unfold MQCSubclassOf. trivial.
Defined.

Lemma OneMoreMQConstructor_embed
  {VC TC} (qx : Ind VC) (x: Ind TC) (MQC : MQCT VC TC)
  : MQCSubclassOf (OneMoreMQConstructor qx x MQC) MQC.
  unfold MQCSubclassOf, OneMoreMQConstructor.
  intros.
  destruct H; assumption.
Qed.

Lemma MQC_embed_under_stricter
  {VC TC VC2 TC2} {eV: VC2 ⊆ VC} {eT: TC2 ⊆ TC}
  (MQC1 MQC2 : MQCT VC TC)
  : MQCSubclassOf MQC1 MQC2 ->
    MQCSubclassOf (MQCOnStricterFormulaTypes MQC1) (MQCOnStricterFormulaTypes MQC2).
  
  unfold MQCSubclassOf, MQCOnStricterFormulaTypes.
  intros.
  exact (H _ _ _ _ _ H0).
Qed.

(* Lemma MQC_unembed_under_stricter
  {VC TC VC2 TC2} {eV: VC2 ⊆ VC} {eT: TC2 ⊆ TC}
  V (_v : Class VC2 V) (MQ : MQT V TC2)
  (MQC1 MQC2 : MQCT VC TC)
  :
    MQCSubclassOf (MQCOnStricterFormulaTypes MQC1) (MQCOnStricterFormulaTypes MQC2) ->
    MQCSubclassOf MQC1 MQC2.
  
  unfold MQCSubclassOf, MQCOnStricterFormulaTypes.
  intros.
  unfold subclass_apply, mqt_on_looser_constructors, ind_on_stricter_constructors, subclass_apply in H.
  specialize (H V _ MQ).
  exact (H _ _ _ H0).
Qed. *)

Lemma MQC_stricter_trans
  {VC TC VC2 TC2 VC3 TC3}
  {eV12: VC2 ⊆ VC} {eT12: TC2 ⊆ TC}
  {eV23: VC3 ⊆ VC2} {eT23: TC3 ⊆ TC2}
  (MQC : MQCT VC TC)
  : MQCSubclassOf
    (@MQCOnStricterFormulaTypes VC2 TC2 VC3 TC3 _ _ (MQCOnStricterFormulaTypes MQC))
    (@MQCOnStricterFormulaTypes VC TC VC3 TC3 _ _ MQC).
  
  unfold MQCSubclassOf, MQCOnStricterFormulaTypes.
  intros.
  assumption.
Qed.

Lemma MQC_stricter_unwrap
  {VC TC} (MQC : MQCT VC TC)
  V _v TC2 eT MQ
  : @MQCOnStricterFormulaTypes VC TC VC TC _ _ MQC V _v TC2 eT MQ
   -> MQC V _v TC2 eT MQ.
  
  unfold MQCOnStricterFormulaTypes.
  intros.
  assumption.
Qed.

(* Lemma MQInd_erjekr {VC TC V} {_v:Class VC V} (qx : V) (x : Ind TC) {MQC : MQCT VC TC} TC2 (eT : TC2 ⊆ TC) :
  MQInd qx x -> @MQInd VC TC2 _ _ qx (ind_on_stricter_constructors eT x) (MQCOnStricterFormulaTypes _).
  intro _mqi. unfold MQInd in *. intros.
  apply _mqi.
  unfold MQCOnStricterFormulaTypes in H.
  exact H. *)

Definition OneMoreQuotvar {VC TC} (MQC : MQCT VC TC)
  : MQCT (OneMoreConstructor VC) (OneMoreConstructor TC)
  :=
  OneMoreMQConstructor
    (@omc_new _) (@omc_new _)
    (MQCOnStricterFormulaTypes MQC).
  (* λ oVC2 oTC2 _v _t MQ,
    (MQC _ _ _ _ MQ) ∧
    (∀ V (_v:Class oVC2 V) T (_t:Class oTC2 T),
      MQ _ _ _ _ omc_new omc_new). *)

Print OneMoreQuotvar.
Eval compute in OneMoreQuotvar.

(* Propositions represent rules of inference. A Rule is a constraint on what inferences may be valid: for example, the rule (A & B) |- (B & A) says that for all values of B and A, the inference (A & B) |- (B & A) must be valid.

In practice, we don't use the full generality of arbitrary constraints. Our only recursive rule is transitivity ((A |- B) and (B |- C) imply (A |- C)), and there isn't a proposition that represents it, it's just always true. All propositions represent simple positive constraints, which just say that certain inferences must be valid.

Nevertheless, the simplest way to define Rule is as a predicate on InfSets, which are predicates on inferences. (An InfSet takes two formulas P,C and says whether it holds inference P |- C as valid.)

We must ask what the actual type of Rule is. A Rule must be agnostic to grammar-extensions, but you may express a rule that assumes particular constructors exist (otherwise, our example rule wouldn't be able to express &). Therefore: *)

Definition InfSet T := T -> T -> Prop.
Existing Class InfSet.
(* Definition _proves {T} {infs:InfSet T} p c := infs p c.
Notation "p ⊢ c" := (_proves p c) (at level 70). *)

Definition Rule {TC} := ∀ T (_:Class TC T), InfSet T -> Prop.

(* We can now make the big definition of what propositions mean. *)

(* definition specific to T, although we will often be dealing in values of type (∀ T (_t:Class TC T), Ruleset) *)
Inductive Ruleset {TC} :=
  | ruleset_implies : Ind TC -> Ind TC -> Ruleset
  | ruleset_and : Ruleset -> Ruleset -> Ruleset
  | ruleset_forall : @Ruleset (OneMoreConstructor TC) -> Ruleset
   .

Definition specialize_ind {TC} (f : Ind (OneMoreConstructor TC)) (x : Ind TC) : Ind TC :=
  λ T _t, f T {| omc_new := (x _ _) |}.
  

(* wrong variable order:
Fixpoint specialize_ruleset {TC} (R : @Ruleset (OneMoreConstructor TC)) (x : Ind TC) : @Ruleset TC :=
  match R return Ruleset with
  | ruleset_implies p c => ruleset_implies (specialize_ind p x) (specialize_ind c x)
  | ruleset_and A B => ruleset_and (specialize_ruleset A x) (specialize_ruleset B x)
  | ruleset_forall F => ruleset_forall (specialize_ruleset F (ind_on_stricter_constructors _ x))
    end. *)
    

Fixpoint Ruleset_to_Coq [TC] (R : Ruleset) {T} {_t: Class TC T} (infs : InfSet T) : Prop :=
  match R with
  | ruleset_implies p c => infs (p _ _) (c _ _)
  | ruleset_and A B => Ruleset_to_Coq A _ ∧ Ruleset_to_Coq B _
  | ruleset_forall F => ∀ x, @Ruleset_to_Coq _ F _ {| omc_new := x |} _
  end.
    
(* Set Printing Implicit. *)
(* Set Typeclasses Debug Verbosity 2. *)
(* Set Typeclasses Depth 4. *)
Inductive FormulaMeans {VC TC} {MQC : MQCT VC TC}
  {_vp:VC ⊆ PropositionConstructors}
  {V} {_v: Class VC V}
  (* {T} {_t: Class TC T}
  {MQ : ∀ {V} {_v:Class VC V} {T} {_t:Class TC T}, V -> T -> Prop}
  {_mq : MQC _ _ _ _ (@MQ)} *)
  : V -> Ruleset -> Prop :=

  | mi_implies [qp qc p c]
      :
      MQInd qp p ->
      MQInd qc c ->
      FormulaMeans [qp -> qc] (ruleset_implies p c)

  | mi_unfold [a b B] :
      UnfoldStep a b ->
      FormulaMeans b B ->
      FormulaMeans a B

  | mi_and [a b A B] :
      FormulaMeans a A ->
      FormulaMeans b B ->
      FormulaMeans [a & b] (ruleset_and A B)

  | mi_forall_quoted_formulas
      (f : Ind VC)
      (F : (@Ruleset (OneMoreConstructor TC)))
      :
      (∀ V _v,
        @FormulaMeans _ _ (OneMoreQuotvar MQC) _ V _v
          [(f _ _) omc_new]
          F)
      ->
      FormulaMeans
        [⋀ (f _ _)]
        (ruleset_forall (@F))
  .

(****************************************************
       Definitions of concrete formula types
****************************************************)

(* The above has been very abstract. We now proceed to the concrete formulas of IC. These belong to the Set universe, for convenience of programming.

All formulas of IC are apply-trees where the leaves are standard atoms... *)

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_implies
  | atom_and
  | atom_forall_quoted_formulas
  | atom_quote
  .

(* ...but our metatheorems may also extend the formula type with additional constructors, which represent metavariables. Each such variable is essentially an additional constructor, so our formula type is parameterized with the extension type. *)

Inductive Formula Ext :=
  | f_atm : Atom -> Formula Ext
  | f_ext : Ext -> Formula Ext
  | fo_apl : Formula Ext -> Formula Ext -> Formula Ext.
Arguments f_atm [Ext] _.

Inductive OneMoreExt OldExt :=
  | ome_embed : OldExt -> OneMoreExt OldExt
  | ome_new : OneMoreExt OldExt.
Arguments ome_embed {OldExt} _.
Arguments ome_new {OldExt}.

(* We'll also need to "be able to talk to" the abstract definitions above, so we make an equivalent definition out of typeclasses. *)

Class FormulaConstructors F := {
      fc_atm : Atom -> F
    ; fc_apl :: ApplyConstructor F
  }.
  
  (* Set Printing Implicit.
Set Typeclasses Debug Verbosity 2.
Definition test_subclass_apply_with_VConsClass_FormulaConstructors
  {VC2 : (Type -> Type)} {TC2:(Type -> Type)} {V:Type} (v:@Class (Type -> Type) VC2 V) {_:VC2 ⊆ FormulaConstructors} {_:TC2 ⊆ FormulaConstructors}
  : @Class (Type -> Type) FormulaConstructors V.
  (* clear X0. *)
  typeclasses eauto.
  eauto with typeclass_instances. *)
  
(* Definition test_subclass_apply_with_VConsClass_FormulaConstructors
  {VC2 : VConsClass} {TC2:TConsClass} {V:Type} (v:@Class VConsClass VC2 V) {_:VC2 ⊆ FormulaConstructors} {_:TC2 ⊆ FormulaConstructors}
  : @Class (Type -> Type) FormulaConstructors V := _.

Definition test_subclass_apply_with_VConsClass_FormulaConstructors_2 :∀ (VC2:VConsClass) (TC2:TConsClass),
    (VC2 ⊆ FormulaConstructors) -> (TC2 ⊆ FormulaConstructors) ->
        Prop :=
  λ VC2 TC2 eV eT,
    ∀ V (_v:Class VC2 V)
     (* T (_t:Class TC2 T) *)
     ,
      let _ : Class FormulaConstructors V := _ in
      (* let _ : Class FormulaConstructors T := _ in
      let MQ := MQ V _ T _ in *)
      False. *)

Instance f_unwrap :
  ∀ {F}, Class FormulaConstructors F ->
         FormulaConstructors F := λ _ b, b.

(* Instance fc_cc : ConstructorClass (Class FormulaConstructors) := {
    cc_embed := λ a b FCa ab, {|
        fc_atm := λ a, ab (fc_atm a)
      ; fc_apl := λ a b, ab (fc_apl a b)
    |}
  }. *)

Instance f_apli {Ext} : Class ApplyConstructor (Formula Ext) := {|
    apply := @fo_apl Ext
  |}.
Instance f_fc {Ext} : Class FormulaConstructors (Formula Ext) := {|
      fc_atm := @f_atm Ext
  |}.

Instance fc_func F : FormulaConstructors F ->
  FunctionConstructors F := {
    const := fc_atm atom_const
  ; fuse := fc_atm atom_fuse
  }.

Instance fc_prop F : FormulaConstructors F ->
  PropositionConstructors F := {
    f_implies := (fc_atm atom_implies)
  ; f_and := (fc_atm atom_and)
  ; f_forall_quoted_formulas := (fc_atm atom_forall_quoted_formulas)
  }.

Instance fc_subset_prop
  : FormulaConstructors ⊆ PropositionConstructors
  := fc_prop.

(* Definition OneMoreConstructor_fc_trans_apply {C} {_vp : C ⊆ FormulaConstructors} {V} {_v : Class (OneMoreConstructor C) V}
  : Class FormulaConstructors V := let _ : Class C V := _ in _.
Hint Immediate OneMoreConstructor_fc_trans_apply : typeclass_instances. *)

Instance shortcut_cfc_pc F : Class FormulaConstructors F -> PropositionConstructors F := _.
Instance shortcut_cfc_func F : Class FormulaConstructors F -> FunctionConstructors F := _.
Instance shortcut_cfc_aplc F : Class FormulaConstructors F -> ApplyConstructor F := _.


(* Definition ind_to_sf (i : Ind FormulaConstructors)
  : StandardFormula := i _ _. *)

Definition ome_to_ind {Ext} {Constrs}
  (embed : Ext -> Ind Constrs)
  (e : @OneMoreExt Ext)
  : Ind (OneMoreConstructor Constrs)
  := λ _ _, match e with
      | ome_embed e => (embed e _ _)
      | ome_new => omc_new
      end.



Fixpoint NMoreConstructors n Constrs :=
  match n with 
    | 0 => Constrs
    | S pred => OneMoreConstructor (NMoreConstructors pred Constrs)
    end.
Fixpoint NMoreConstructorsL n Constrs :=
  match n with 
    | 0 => Constrs
    | S pred => (NMoreConstructorsL pred (OneMoreConstructor Constrs))
    end.

Fixpoint NMoreExt n Ext :=
  match n with
    | 0 => Ext
    | S pred => @OneMoreExt (NMoreExt pred Ext)
    end.

Fixpoint NMoreQuotvars n {VC} {TC} (MQC : MQCT VC TC) : MQCT (NMoreConstructors n VC) (NMoreConstructors n TC) :=
  match n with
    | 0 => MQC
    | S p => OneMoreQuotvar (NMoreQuotvars p MQC)
    end.

Fixpoint NMoreQuotvars_without_new_MQCs n {VC} {TC} (MQC : MQCT VC TC) : MQCT (NMoreConstructors n VC) (NMoreConstructors n TC) :=
  match n with
    | 0 => MQC
    | S p => MQCOnStricterFormulaTypes (NMoreQuotvars_without_new_MQCs p MQC)
    end.

Definition FormulaWithNVars n : Type := Formula (NMoreExt n False).
Definition FCWithNVars n : Type -> Type := NMoreConstructors n FormulaConstructors.

(* we could write (Formula False) instead, but this makes inference easier *)
Definition StandardFormula := FormulaWithNVars 0.
Fixpoint sf_to_ind (f : StandardFormula)
  : Ind FormulaConstructors
  := λ _ _, match f with
    | f_atm a => fc_atm a
    | f_ext a => match a with end
    | fo_apl a b => [(sf_to_ind a _) (sf_to_ind b _)]
    end.



(* Instance fplus_fcplus {Ext} : Class (OneMoreConstructor FormulaConstructors) (Formula (@OneMoreExt Ext)) :=
  {|
      omc_embed := _
    ; omc_new := f_ext ome_new
  |}.

Instance fplus2_fcplus2 {Ext} : Class (OneMoreConstructor (OneMoreConstructor FormulaConstructors)) (Formula (@OneMoreExt (@OneMoreExt Ext))) :=
  {|
      omc_embed := _
    ; omc_new := f_ext (ome_embed ome_new)
  |}.

Print fplus2_fcplus2.
Definition test1 : Formula (@OneMoreExt (@OneMoreExt False))
  := @omc_new (OneMoreConstructor FormulaConstructors) _ _.
Definition test2 : Formula (@OneMoreExt (@OneMoreExt False))
  := @omc_new (FormulaConstructors) _ _.
Eval compute in (test1, test2). *)

(* Set Printing Implicit. *)
Fixpoint nth_new_ext {Ext} n : (@NMoreExt (S n) Ext) := 
  match n with
    | 0 => ome_new
    | S pred => ome_embed (nth_new_ext pred)
    end.

(* Instance fplus__eq_add_S {n m Ext} :
  Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt (n + S m) Ext))
  ->
  Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt (S n + m) Ext)).
  intro.
  change (S n + m) with (S (n + m)).
  rewrite (plus_n_Sm n m).
  assumption.
Defined. *)

(* Fixpoint fplusnm_fcplusn n m : 
  Class (FCWithNVars n)
        (Formula (@NMoreExt n (@NMoreExt m False))) := match n return Class (FCWithNVars n)
        (Formula (@NMoreExt n (@NMoreExt m False))) with
    | 0 => f_fc
    | S pred => 
      {|
          omc_embed := 
            (* we can technically get away with writing just `_` for this, but that's too magical *)
            fplusnm_fcplusn ()
        ; omc_new := f_ext ome_new
      |}
    end. *)

(* Instance fplusnm_fcplusn n m : 
  Class (FCWithNVars n)
        (Formula (@NMoreExt n (@NMoreExt m False))).
  induction n. exact _.
  (* Set Printing Implicit. *)
  cbn.
  refine 
      {|
          omc_embed := 
            _
        ; omc_new := f_ext ome_new
      |}.
  
  
        
         :=
  match n return Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt (n + m) Ext)) with
    | 0 => f_fc
    | S pred => 
      {|
          omc_embed := 
            (* we can technically get away with writing just `_` for this, but that's too magical *)
            fplus__eq_add_S (fplusnm_fcplusn pred (S m))
        ; omc_new := f_ext (nth_new_ext (pred + m))
      |}
    end.
Existing Instance fplusnm_fcplusn.
Print fplusnm_fcplusn.

Print fplus__eq_add_S. *)
(* Instance fplus__plus_n_0 n {Ext} :
  Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt (n + 0) Ext))
  ->
  Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt n Ext)).
  intro.
  refine (eq_rect_r (λ m, Class (NMoreConstructors n FormulaConstructors)
        (Formula (@NMoreExt m Ext))) X _).
  apply plus_n_O.
Defined.
Print fplus__plus_n_0. *)

Fixpoint NMoreConstructors_subclass n C
  : NMoreConstructors n C ⊆ C
  := match n with
    | 0 => subclass_refl
    | S p => subclass_trans OneMoreConstructor_subclass (NMoreConstructors_subclass p C)
    end.
Existing Instance NMoreConstructors_subclass.
(* Lemma NMoreConstructors_flop n C : NMoreConstructors (S n) C = NMoreConstructors n (OneMoreConstructor C).
  induction n; [trivial|].
  cbn in *.
  rewrite <- IHn.
  reflexivity.
Qed. *)

(* Set Printing Implicit. *)
Instance nmore_fc n Constrs T : (Constrs ⊆ FormulaConstructors) -> Class (NMoreConstructors n Constrs) T -> Class FormulaConstructors T := λ _ _, _.



(* Definition fwn_to_ind n
  : FormulaWithNVars n -> Ind (FCWithNVars n)
  :=
  nmf_to_ind n (False_rect _). *)


Instance fcn_sub_fc n
  : FCWithNVars n ⊆ FormulaConstructors
  := NMoreConstructors_subclass n _.

Instance fcn_pc n : FCWithNVars n ⊆ PropositionConstructors
  := _.

Fixpoint embed_formula
  Ext1 Ext2 (embed : Ext1 -> Ext2)
  (f : (Formula Ext1)) : (Formula Ext2)
  := match f with
    | f_atm a => f_atm a
    | f_ext a => f_ext (embed a)
    | fo_apl a b => [(embed_formula embed a) (embed_formula embed b)]
    end.

(* Fixpoint FCn_embed
  n Ext1 Ext2 (embed : Ext1 -> Ext2)
  : Class (FCWithNVars n) (Formula Ext1) ->
    Class (FCWithNVars n) (Formula Ext2)
  := λ _f, match n return Class (FCWithNVars n) (Formula Ext1) -> Class (FCWithNVars n) (Formula Ext2) with
    | 0 => λ _, f_fc
    | S n => λ _, {|
        omc_embed := FCn_embed ( OneMoreConstructor_subclass _) ;
        omc_new := embed_formula embed omc_new
      |}
    end _f. *)

Definition FCn_embed n Ext1 Ext2 (embed : Ext1 -> Ext2) :
  Class (FCWithNVars n) (Formula Ext1) ->
  Class (FCWithNVars n) (Formula Ext2).
  intro.
  induction n.
  exact f_fc.
  exact {|
    omc_embed := IHn (OneMoreConstructor_subclass X) ;
    omc_new := embed_formula embed omc_new
  |}.
Defined.



Definition FCn_embed2 [n m] :
  Class (FCWithNVars n) (FormulaWithNVars m) ->
  Class (FCWithNVars n) (FormulaWithNVars (S m)).
  intro.
  induction n.
  exact f_fc.
  exact {|
    omc_embed := IHn (OneMoreConstructor_subclass X) ;
    omc_new := embed_formula ome_embed omc_new
  |}.
Defined.

(* Inductive ReifiedFCWithNVarsInM : nat -> nat -> Type :=
  | rfcn_0 m : ReifiedFCWithNVarsInM 0 m
  | rfcn_S n m : ReifiedFCWithNVarsInM n m -> ReifiedFCWithNVarsInM (S n) (S m)
  .
  Locate "≤".
  Print le.
  Print le_ind.
Print le_rect.
Fixpoint FCn_embed22 n m (_c : Class (FCWithNVars n) (FormulaWithNVars m)) : 
  Class (FCWithNVars n) (FormulaWithNVars (S m)) :=
    match n with
      | 0 => f_fc
      | (S pred) => FCn_embed22 pred m 
      end.

  intro.
  induction n.
  exact f_fc.
  exact {|
    omc_embed := IHn (OneMoreConstructor_subclass X) ;
    omc_new := embed_formula ome_embed omc_new
  |}.
Defined. *)


Fixpoint ome_new_embed3 {Ext} n R :
  (@NMoreExt (S n) Ext -> R) -> R :=
  match n with
    | 0 => λ embed, embed ome_new
    | S pred => λ embed, (@ome_new_embed3 _ pred R (λ e, embed (ome_embed e)))
    end.
Print ome_new_embed3.

Definition next_new_var_in {Ext} m 
  (prev_var : (NMoreExt m Ext))
  : (NMoreExt (S m) Ext)
  := ome_embed prev_var.

Fixpoint nth_new_var_in_wrong {Ext} n m
  : (NMoreExt n (NMoreExt (S m) Ext))
  := match n with
    | 0 => ome_new
    | S pred => next_new_var_in pred (nth_new_var_in_wrong pred m)
    end.
(* Fixpoint nth_new_var_in {Ext} n m
  : (NMoreExt (S m) (NMoreExt n Ext))
  := match n with
    | 0 => ome_new
    | S pred => next_new_var_in pred (nth_new_var_in pred m)
    end. *)
    
(* Definition FCn_embed3_impl n m :
  Class (FCWithNVars (S n)) (FormulaWithNVars m) ->
  Class (FCWithNVars (S n)) (FormulaWithNVars (S m)).
  intro.

  (* induction n.
  exact f_fc. *)
  notypeclasses refine {|
    omc_embed := _ ;
    omc_new := f_ext (nth_new_var_in n m)
  |}.
  change (Class (FCWithNVars n) (FormulaWithNVars (S m))).

  IHn (OneMoreConstructor_subclass X)
Defined. *)

(* Require Import Vector.

Fixpoint nth_var_in n m (vars : Vector.t (NMoreExt (S m) False) n) : (NMoreExt (S m) False).
  destruct vars.
  exact ome_new.
  exact (nth_var_in n m vars).
Defined.

Definition embed_vars n m (vars : Vector.t (NMoreExt m False) n) : Vector.t (NMoreExt (S m) False) n
  := map ome_embed vars. *)
(* 
Definition vars_to_ n (vars : Vector.t (NMoreExt n False) n) :
  (FCWithNVars n)
  (FormulaWithNVars n).
  induction n.
  exact f_fc.
  destruct vars.
  exact {|
    omc_embed := IHvars ;
    omc_new := f_ext ome_new
  |}. *)

(* Fixpoint vars_to_ n m (vars : Vector.t (NMoreExt m False) n) :
  (FCWithNVars n)
  (FormulaWithNVars m) :=
  match vars with 
    | nil => f_fc
    | cons h pred t => {|
        omc_embed := vars_to_ m t ;
        omc_new := f_ext h
      |}
  end.

Fixpoint right_vars n : Vector.t (NMoreExt n False) n :=
  match n with
    | 0 => Vector.nil _
    | S pred => Vector.cons _ ome_new _ (map ome_embed (right_vars pred))
    end. *)


(* Instance fn_fcn n : Class
  (FCWithNVars n)
  (FormulaWithNVars n)
  := vars_to_ n (right_vars n). *)
  
Inductive ler (n : nat) : nat -> Type :=
  | ler_nn : ler n n
  | ler_Sm m : ler n m → ler n (S m).

Definition ltr n m := ler (S n) m.

Inductive upto : nat -> nat -> Type :=
  | upto_0m m : upto 0 m
  | upto_Sn n m : ltr n m -> upto n m -> upto (S n) m.

Inductive leroute : nat -> nat -> Type :=
  | leroute_00 : leroute 0 0
  | leroute_Sm n m : leroute n m -> leroute n (S m)
  | leroute_Sn n m : ltr n m -> leroute n m -> leroute (S n) m.

Fixpoint ler_0m m : ler 0 m :=
  match m with
    | 0 => ler_nn 0
    | S pred => ler_Sm (ler_0m pred)
    end.

Search le.
Lemma ler_SnSm n m (l : ler n m) : ler (S n) (S m).
  induction l; constructor.
  assumption.
Defined.

Fixpoint ler_Pn [n m] (l : ler (S n) m) : ler n m :=
  match l with
    | ler_nn => ler_Sm (ler_nn _)
    | ler_Sm m l => ler_Sm (ler_Pn l)
    end.
(* Set Printing Implicit.
Print ler_Pn. *)
(* Fixpoint ler_pboth n m (l : ler (S n) (S m)) : ler n m :=
  match l in ler _ m0 return (m0 = (S m)) -> ler n m with
    | ler_nn => λ eq, match eq with eq_refl => ler_nn n end
    | ler_Sm m l => λ eq, _
    end eq_refl.

    
  dependent induction l.
  constructor.
  
  assumption.
Defined. *)

Lemma ler_pboth n m (l : ler (S n) (S m)) : ler n m.
  dependent induction l.
  constructor.
  induction m.
  dependent destruction l.

  apply ler_Sm.
  apply IHl.
  reflexivity.
Qed.

Lemma S_not_ler n : ler (S n) n -> False.
  intro l. induction n.
  dependent destruction l.
  exact (IHn (ler_pboth l) ).
Qed.

Lemma ler_unique n m (l0 l1 : ler n m) : l0 = l1.
  induction l0.
  dependent destruction l1.
  reflexivity.

  contradict l1; apply S_not_ler.
  dependent destruction l1.
  clear IHl0; contradict l0; apply S_not_ler.
  rewrite (IHl0 l1); reflexivity.
Qed.

Fixpoint upto_Sm n m (u : upto n m) : upto n (S m) :=
  match u with 
    | upto_0m _ => upto_0m _
    | upto_Sn _ _ l u => upto_Sn (ler_Sm l) (upto_Sm u)
    end.

Fixpoint upto_nn n : upto n n :=
  match n with
    | 0 => upto_0m _
    | S pred => upto_Sn (ler_nn _) (upto_Sm (upto_nn pred))
    end.

Fixpoint ler_upto n m (l : ler n m) : upto n m :=
  match l with
    | ler_nn => upto_nn n
    | ler_Sm m l => upto_Sm (ler_upto l)
    end.

Definition upto_ler n m (u : upto n m) : ler n m :=
  match u with
    | upto_0m m => ler_0m m
    | upto_Sn _ _ l u => l
    end.

Fixpoint leroute_ler n m (r : leroute n m) : ler n m :=
  match r with
    | leroute_00 => ler_nn _
    | leroute_Sm _ _ r => ler_Sm (leroute_ler r)
    | leroute_Sn _ _ l r => l
    end.

Lemma upto_unique n m (u0 u1 : upto n m) : u0 = u1.
  induction u0.
  dependent destruction u1.
  reflexivity.
  dependent destruction u1.
  rewrite (ler_unique l0 l).
  rewrite (IHu0 u1); reflexivity.
Qed.

(* Lemma upto_SnSm n m (u : upto n m) : upto (S n) (S m).
  induction u; constructor.
  apply ler_SnSm; apply ler_0m.

  assumption.
Defined. *)

Fixpoint leroute_0m m : leroute 0 m :=
  match m with
    | 0 => leroute_00
    | S pred => leroute_Sm (leroute_0m pred)
    end.

Fixpoint upto_route n m (u : upto n m) : leroute n m :=
  match u with 
    | upto_0m _ => leroute_0m _
    | upto_Sn _ _ l u => leroute_Sn l (upto_route u)
    end.

Fixpoint leroute_n_alternating n : leroute n n :=
  match n with
    | 0 => leroute_00
    | S pred => leroute_Sn (ler_nn _) (leroute_Sm (leroute_n_alternating pred))
    end.
  

Fixpoint embedded_var_ext i m (embedding : ltr i m) : (NMoreExt m False):=
  match embedding with
    | ler_nn => ome_new
    | ler_Sm m embedding => ome_embed (embedded_var_ext embedding)
    end.

Fixpoint embedded_var_ind i m (embedding : ltr i m) : Ind (FCWithNVars m) :=
  match embedding with
    | ler_nn => λ _ _, omc_new
    | ler_Sm m embedding => λ _ _, (embedded_var_ind embedding) _ _
    end.



Fixpoint fcn_instance_route n m (r : leroute n m) : Class
  (FCWithNVars n)
  (FormulaWithNVars m)
  :=
  match r in leroute n m return Class (FCWithNVars n)
  (FormulaWithNVars m) with 
    | leroute_00 => f_fc
    | leroute_Sm _ _ r => FCn_embed2 (fcn_instance_route r)
    | leroute_Sn _ _ l r => {|
        omc_embed := fcn_instance_route r ;
        omc_new := f_ext (embedded_var_ext l)
      |}
    end.
Fixpoint embeddings_to_fcn_instance n m (u : upto n m) : Class
  (FCWithNVars n)
  (FormulaWithNVars m)
  :=
  match u with 
    | upto_0m _ => f_fc
    | upto_Sn _ _ e u => {|
        omc_embed := embeddings_to_fcn_instance u ;
        omc_new := f_ext (embedded_var_ext e)
      |}
    end.


Fixpoint ler_fcn_subclass [n m] (l : ler n m) : 
  (FCWithNVars m) ⊆ (FCWithNVars n)
  :=
  match l 
  (* in ler n m return (FCWithNVars m) ⊆ (FCWithNVars n)  *)
  with 
    | ler_nn => subclass_refl
    | ler_Sm m l => subclass_trans OneMoreConstructor_subclass (ler_fcn_subclass l)
    end.
Existing Instance ler_fcn_subclass.

Instance ler_fcn_subclass_apply [n m] (l : ler n m) V 
   : Class (FCWithNVars m) V -> Class (FCWithNVars n) V := subclass_apply (ler_fcn_subclass l).
Instance ltr_fcn_subclass_apply [n m] (l : ltr n m) V 
   : Class (FCWithNVars m) V -> Class (FCWithNVars n) V := subclass_apply (ler_fcn_subclass (ler_Pn l)).

Instance fn_fcn n : Class
  (FCWithNVars n)
  (FormulaWithNVars n)
  := embeddings_to_fcn_instance (upto_nn n).
  

Fixpoint ewnm_to_ind [n m] (embeddings : upto n m) : NMoreExt n False -> Ind (FCWithNVars m)
  := 
  match embeddings with 
    | upto_0m _ => False_rect _
    | upto_Sn n m new_embedding u => λ e, match e with
      | ome_embed e => λ _ _, ewnm_to_ind u e _ _
      | ome_new => embedded_var_ind new_embedding
      end
    end.

Definition ewn_to_ind [n] (e : NMoreExt n False ) : Ind (FCWithNVars n) :=
  ewnm_to_ind (upto_nn n) e.

(* Set Typeclasses Debug Verbosity 2. *)
Fixpoint fwn_to_ind n (f : FormulaWithNVars n) : Ind (FCWithNVars n)
  := λ _ _, match f with
    | f_atm a => fc_atm a
    | f_ext e => ewn_to_ind e _ _
    | fo_apl a b => [
      (fwn_to_ind a _ _)
      (fwn_to_ind b _ _)
    ]
    end.

Lemma unfold_rewrap [n] (f g : FormulaWithNVars n) :
  UnfoldStep f g ->
  ∀ V _v, UnfoldStep (fwn_to_ind f V _v) (fwn_to_ind g V _v).
  intros.
  (* Set Printing Implicit. *)
  induction H; [constructor|constructor|].
  exact (unfold_in_lhs (fwn_to_ind c V _v) IHUnfoldStep).
Qed.

(* Set Printing Implicit.
Fixpoint nme_to_ind {Ext} {Constrs} [n]
  (embed : Ext -> Ind Constrs)
  : NMoreExt n Ext -> Ind (NMoreConstructors n Constrs)
  := match n return NMoreExt n Ext -> Ind (NMoreConstructors n Constrs) with
    | 0 => embed
    | S pred => λ e _ _, ome_to_ind (nme_to_ind embed) e _
    end.

Fixpoint ewn_to_ind [n m] (e : ltr n m) : NMoreExt n False -> Ind (FCWithNVars m)
  (* := nme_to_ind (False_rect _). *)
  := match e with
    | ler_nn _ => omc_new 
    | ler_Sm n m e => λ e _ _, ome_to_ind (ewn_to_ind e ) e _
    end. *)

(* note the similarity to `lt` *)
(* Inductive VarsEmbedding : nat -> nat -> Type :=
  | no_unaccounted_vars n : VarsEmbedding n n
  | s_unaccounted_vars n m : VarsEmbedding n m -> VarsEmbedding n (S m).

Fixpoint embedded_var_ext i m (embedding : VarsEmbedding i m) : (NMoreExt (S m) False):=
  match embedding with
    | no_unaccounted_vars _ => ome_new
    | s_unaccounted_vars i m embedding => ome_embed (embedded_var_ext embedding)
    end.

Fixpoint ve_0_m m :=
  match m with
    | 0 => no_unaccounted_vars 0
    | S pred => s_unaccounted_vars (ve_0_m pred)
    end.

Fixpoint ve_Sn n m
  (embedding : VarsEmbedding n m)
  :  :=
  match m with
    | 0 => no_unaccounted_vars 0
    | S pred => s_unaccounted_vars (ve_0_m pred)
    end.

Inductive VarsEmbeddingSN n m : nat -> nat -> Type :=
  | no_unaccounted_vars n : VarsEmbedding n n
  | s_unaccounted_vars n m : VarsEmbedding n m -> VarsEmbedding n (S m).

Fixpoint ve_rect_n
  (P : ∀ n m (embedding : VarsEmbedding n m), Type)
  (case_0 : ∀ m, P 0 m)
  (case_S : ∀ m n (embedding : VarsEmbedding (S n) m), P )
  : 
 

Fixpoint f_fcvar n m (embedding : VarsEmbedding n m) : Class
  (FCWithNVars n)
  (FormulaWithNVars m)
  := match n return   (FCWithNVars n)
  (FormulaWithNVars m) with
    | 0 => f_fc
    | S pred => {|
        omc_embed := f_fcvar (ler_Sm pred m) ;
        omc_new := f_ext (embedded_var_ext embedding)
      |}
    end.

Fixpoint fn_fcn n : Class
  (FCWithNVars n)
  (FormulaWithNVars n)
  := match n as i return FCWithNVars i (FormulaWithNVars n) with
    | 0 => f_fc
    | S pred => {|
        omc_embed := _ ;
        omc_new := f_ext (embedded_var_ext pred n)
      |}
    end.
Print fn_fcn. *)

  

(* Definition FCn_embed3 n m :
  Class (FCWithNVars n) (FormulaWithNVars m) ->
  Class (FCWithNVars n) (FormulaWithNVars (S m)).
  intro.
  induction n.
  exact f_fc.
  notypeclasses refine {|
    omc_embed := _ ;
    omc_new := f_ext (nth_new_var_in n m)
  |}.
  change (Class (FCWithNVars n) (FormulaWithNVars (S m))).

  apply IHn.

  IHn (OneMoreConstructor_subclass X)
Defined. *)

(* Instance fplusn_fcplusn n {Ext} : 
  Class (FCWithNVars n)
        (Formula (NMoreExt n Ext)).
  induction n.
  exact _.
  cbn.
  exact {|
    omc_embed := FCn_embed n ome_embed IHn ;
    omc_new := f_ext ome_new
  |}.
Defined. *)

(* Instance fn_fcn n : Class
  (FCWithNVars n)
  (FormulaWithNVars n)
  .
  induction n.
  exact _.
  cbn.
  exact {|
    omc_embed := FCn_embed3 n _ IHn ;
    omc_new := f_ext ome_new
  |}.
Defined.
Print fn_fcn. *)

(* Set Printing Implicit. *)
(* Definition ome_extend_constrs Constrs Ext :
  ConstructorClass (Class Constrs) ->
  Class Constrs (Formula Ext) ->
  Class Constrs (Formula (@OneMoreExt Ext))
  := λ _ _, cc_embed (embed_formula ome_embed). *)


Lemma ewnm_to_ind_swap_succ n m (u : upto n m) e T _t : 
  ewnm_to_ind (upto_Sm u) e T _t =
ewnm_to_ind u e T
  (OneMoreConstructor_subclass _t).
  induction u; [contradiction|].
  destruct e; [apply IHu|reflexivity].
Qed.

Lemma embed_formula_rewrap n f T H : 
  (fwn_to_ind
    (embed_formula (Ext2 := NMoreExt (S n) _) (λ a : NMoreExt n _, ome_embed a) f)
    T
    H)
  = (fwn_to_ind
    f
    T
    (OneMoreConstructor_subclass H)).
  
  induction f; destruct n; cbn in *; contradiction || trivial.
  {
    destruct e; [apply ewnm_to_ind_swap_succ|reflexivity].
  }
  {
    rewrite IHf1, IHf2; reflexivity.
  }
  {
    rewrite IHf1, IHf2; reflexivity.
  }
Qed.

(* Lemma apply_rewrap n (f : FormulaWithNVars n) x V _v : fwn_to_ind [f x] V _v = [(fwn_to_ind f V _v) (fwn_to_ind x V _v)].
  reflexivity.
Qed. *)


Definition f_quote {F} `{FormulaConstructors F} := fc_atm atom_quote.
Definition f_qaply {Ext F} `{FormulaConstructors F} f x : Formula Ext := [f_quote f x].

Inductive UnfoldsToKind F `{FormulaConstructors F} [T]
    (kind : F -> T -> Prop) :
    F -> T -> Prop :=
  | utk_done f t : kind f t -> UnfoldsToKind kind f t
  | utk_step a b t :
      UnfoldStep a b ->
      UnfoldsToKind kind b t ->
      UnfoldsToKind kind a t.

Inductive IsAtom F `{FormulaConstructors F}
    : F -> Atom -> Prop :=
  | is_atom a : IsAtom (fc_atm a) a.

Lemma IsAtom_rewrap [n] (f : FormulaWithNVars n) a :
  IsAtom f a ->
  ∀ V _v, IsAtom (fwn_to_ind f V _v) a.
  intro. destruct H. constructor.
Qed.

Lemma utk_rewrap [n] (f : FormulaWithNVars n) a :
  UnfoldsToKind (@IsAtom _ _) f a ->
  ∀ V _v, UnfoldsToKind (@IsAtom _ _) (fwn_to_ind f V _v) a.
  intros.
  induction H.
  { constructor. apply IsAtom_rewrap. assumption. }  
  exact (utk_step (unfold_rewrap H _ _) IHUnfoldsToKind).
Qed.

(* Inductive FcMeansQuoted {F} `{FormulaConstructors F}
    (* (Ext -> StandardFormula -> Prop) *)
    : F -> StandardFormula -> Prop :=
  | quoted_atom f a :
    @UnfoldsToKind F _ _ (@IsAtom F _) f a ->
    FcMeansQuoted [f_quote f] (f_atm a)
  | quoted_apply qa a qb b :
    UnfoldsToKind FcMeansQuoted qa a ->
    UnfoldsToKind FcMeansQuoted qb b ->
    FcMeansQuoted [f_quote qa qb] [a b]. *)

(* Set Printing Implicit. *)
Definition FcMQC : MQCT FormulaConstructors FormulaConstructors :=
  λ V _v TC2 eT MQ,
    (∀ f a,
      @UnfoldsToKind V _ _ (@IsAtom V _) f a ->
      MQ [f_quote f] (λ _ _, fc_atm a))
    ∧
    (∀ qa qb b, UnfoldStep qa qb -> MQ qb b -> MQ qa b)
    ∧
    (∀ qa a qb b, MQ qa a -> MQ qb b ->
      MQ [f_quote qa qb] (λ _ _, [(a _ _) (b _ _)]))
    .

(*
(* Same as MQInd, but delivers UnfoldsToKind MQ instead of just MQ. *)
Definition UTKInd {VC TC} (qx : Ind VC) (x : Ind TC) {MQC : MQCT}
  {_:VC ⊆ FormulaConstructors}
  :=
  ∀ V (_v:Class VC V) T (_t:Class TC T) (MQ : MQT),
    MQC _ _ _ _ MQ ->
    @UnfoldsToKind V _ _ (MQ V _v T _t) (qx _ _) (x _ _). *)

(* Definition FcMQC_ind_apply (qa a qb b : Ind FormulaConstructors) :
  let _ := FcMQC in
  UTKInd qa a -> UTKInd qb b ->
  @MQInd _ _ (λ _ _, [f_quote (qa _ _) (qb _ _)]) (λ _ _, [(a _ _) (b _ _)]) FcMQC. *)

Fixpoint FcMQCWithRoute [n m] (r : leroute n m) : MQCT (FCWithNVars n) (FCWithNVars m) :=
  match r in leroute n m return MQCT (FCWithNVars n) (FCWithNVars m) with 
    | leroute_00 => FcMQC
    | leroute_Sm _ _ r => MQCOnStricterFormulaTypes (FcMQCWithRoute r)
    | leroute_Sn _ _ l r => OneMoreMQConstructor (@ omc_new _) (embedded_var_ind l) (MQCOnStricterFormulaTypes (FcMQCWithRoute r))
    end.

Fixpoint FcMQCWithEmbeddings [n m] (u : upto n m) : MQCT (FCWithNVars n) (FCWithNVars m) :=
  match u in upto n m return MQCT (FCWithNVars n) (FCWithNVars m) with 
    | upto_0m _ => MQCOnStricterFormulaTypes FcMQC
    | upto_Sn n m e u => OneMoreMQConstructor (@ omc_new _) (embedded_var_ind e) (MQCOnStricterFormulaTypes (FcMQCWithEmbeddings u))
    end.

Definition FcMQCWithNVars n : MQCT (FCWithNVars n) (FCWithNVars n) := NMoreQuotvars n FcMQC.
Print FcMQCWithNVars.

Definition FcMQCWithEmbedNVars n := FcMQCWithEmbeddings (upto_nn n).

Lemma FcMQCWithEmbeddings_deeper n m (u : upto n m) : 
  (* this proof is messy , maybe clean it up later *) 
  MQCSubclassOf (MQCOnStricterFormulaTypes (FcMQCWithEmbeddings u)) (FcMQCWithEmbeddings (upto_Sm u)).
  unfold MQCSubclassOf; intros V _v TC2 eT MQ _f.
  induction u; [trivial|].
  cbn in *.
  destruct _v as (embed, new).
  destruct _f as (_fembed, _fnew).
  specialize (IHu embed eT _fembed).
  split; cbn.
  {
    exact IHu.
  }
  {
    intros.
    exact (_fnew T _).
  }
Qed.

Lemma FcMQCWithEmbeddings_shallower n m (u : upto n m) : 
  (* this proof is messy , maybe clean it up later *) 
  MQCSubclassOf (FcMQCWithEmbeddings (upto_Sm u)) (MQCOnStricterFormulaTypes (FcMQCWithEmbeddings u)).

  unfold MQCSubclassOf; intros V _v TC2 eT MQ _f.
  induction u; [trivial|].
  cbn in *.
  destruct _v as (embed, new).
  destruct _f as (_fembed, _fnew).
  specialize (IHu embed eT _fembed).
  split; cbn.
  {
    exact IHu.
  }
  {
    unfold mqt_on_looser_constructors .
    intros.
    cbn in *.
  (* destruct _t as (_tembed, _tnew). *)
    exact (_fnew T {|omc_new := fc_atm atom_const|}).
  }
Qed.

  
Lemma FcMQCn_embed n : MQCSubclassOf (FcMQCWithNVars n) (FcMQCWithEmbedNVars n).
  unfold MQCSubclassOf. intros V _v TC2 eT MQ _f.
  induction n; [assumption|].
  cbn in *.
  destruct _v as (embed, new).
  destruct _f as (_fembed, _fnew).
  specialize (IHn embed _ _fembed).
  split.
  {
    unfold MQCOnStricterFormulaTypes.
    cbn.
    apply FcMQCWithEmbeddings_deeper.
    exact IHn.
  }
  {
    intros.
    exact (_fnew T _).
  }
Qed.

(* Lemma FcMQCembed_n n m (u : upto n m) V (_v : Class _ V) MQ : FcMQCWithEmbeddings u _v MQ -> FcMQCWithNVars n _v (mqt_on_looser_constructors MQ). *)

Lemma FcMQCembed_n n  : MQCSubclassOf (FcMQCWithEmbedNVars n) (FcMQCWithNVars n).
  unfold MQCSubclassOf. intros V _v TC2 eT MQ _f.
  induction n; [assumption|].

  (* apply MQC_embed_under_stricter. *)
  cbn in *.
  destruct _v as (embed, new).
  destruct _f as (_fembed, _fnew).
  specialize (IHn embed _).
  split.
  {
    unfold MQCOnStricterFormulaTypes in *.
    cbn in *.
    exact (IHn (FcMQCWithEmbeddings_shallower _ _ _ _ _fembed)).
  }
  {
    intros.
    exact (_fnew T _).
  }
Qed.

(* Lemma FcMQC_routes_equivalent n m (r0 r1 : leroute n m) : MQCSubclassOf (FcMQCWithRoute r0) (FcMQCWithRoute r1).
  induction r0.
  (* 00 case: *)
  dependent destruction r1; apply MQCSubclassOf_refl.
  (* Sm case: *)
  {
    dependent destruction r1.
    apply MQC_embed_under_stricter.
    exact (IHr0 r1).
    (* cbn. *)
    unfold MQCSubclassOf; intros.
    cbn in H.
    cbn.
    split.
    generalize V _v MQ H.
    (* Set Printing Implicit. *)
    change (MQCSubclassOf (@MQCOnStricterFormulaTypes _ _ _ _ subclass_refl OneMoreConstructor_subclass (FcMQCWithRoute r0)) (MQCOnStricterFormulaTypes (FcMQCWithRoute r1))).
    apply MQC_embed_under_stricter.
    destruct H.
  } *)


Lemma FcMQC_route_diamond1
  n m (r : leroute n m) (l : ltr n m)
  : MQCSubclassOf
    (FcMQCWithRoute (leroute_Sm (leroute_Sn l r)))
    (FcMQCWithRoute (leroute_Sn (ler_Sm l) (leroute_Sm r))).
  
  unfold MQCSubclassOf. intros. cbn in *.
  destruct H; split; trivial.

  intros. exact (H0 _ _).
Qed.
Lemma FcMQC_route_diamond2
  n m (r : leroute n m) (l : ltr n m)
  : MQCSubclassOf
    (FcMQCWithRoute (leroute_Sn (ler_Sm l) (leroute_Sm r)))
    (FcMQCWithRoute (leroute_Sm (leroute_Sn l r))).
  
  unfold MQCSubclassOf. intros. cbn in *.
  destruct H; split; trivial.

  (* unfold shortcut_omc_trans_apply, subclass_apply, subclass_refl in H0.
  unfold mqt_on_looser_constructors, ind_on_stricter_constructors, subclass_apply. *)
  (* Set Printing Implicit. *)
  (* super hacky but I guess it's proved???? *)
  intros. exact (H0 _ {| omc_new := fc_atm atom_const |}).
Qed.

Lemma FcMQC_route_diamond3
  n m (r0 r1 : leroute n m) (l : ltr n m)
  (_ms : MQCSubclassOf
    (FcMQCWithRoute r0)
    (FcMQCWithRoute r1))
  : MQCSubclassOf
    (FcMQCWithRoute (leroute_Sm (leroute_Sn l r0)))
    (FcMQCWithRoute (leroute_Sn (ler_Sm l) (leroute_Sm r1))).
  
  unfold MQCSubclassOf. intros. cbn in *.
  destruct H; split.

  apply _ms; exact H.
  intros; exact (H0 _ _).
Qed.

Lemma FcMQC_route_diamond4
  n m (r0 r1 : leroute n m) (l : ltr n m)
  (_ms : MQCSubclassOf
    (FcMQCWithRoute r0)
    (FcMQCWithRoute r1))
  : MQCSubclassOf
    (FcMQCWithRoute (leroute_Sn (ler_Sm l) (leroute_Sm r0)))
    (FcMQCWithRoute (leroute_Sm (leroute_Sn l r1))).
  
  unfold MQCSubclassOf. intros. cbn in *.
  destruct H; split.

  apply _ms; exact H.
  intros; exact (H0 _ {| omc_new := fc_atm atom_const |}).
Qed.



(* Lemma FcMQC_routes_equivalent n m p (r0 r1 : leroute n m) (l : ler m p) : MQCSubclassOf (@MQCOnStricterFormulaTypes _ _ _ _ subclass_refl (ler_fcn_subclass l) (FcMQCWithRoute r0)) (@MQCOnStricterFormulaTypes _ _ _ _ subclass_refl (ler_fcn_subclass l) (FcMQCWithRoute r1)).
  induction r0.
  (* 00 case: *)
  dependent destruction r1; apply MQCSubclassOf_refl.
  (* Sm case: *)
  {
    dependent destruction r1.
    {
    (* refine (
      match l in ler _ ml return (p = ) with
        ler_nn => _
        end
    ).
    destruct l.
    specialize (IHr0 r1 (ler_Sm (ler_nn _))).
    apply MQC_embed_under_stricter.
    exact IHr0.
    
    (* Show Proof. *)
    specialize (IHr0 r1 (ler_Sm (ler_Pn l))).
    specialize (IHl IHr0).
    refine (IHl _).
    apply MQC_embed_under_stricter.
    (* cbn in *. *)
    exact IHr0.
    
    (* apply MQC_embed_under_stricter. fold FcMQCWithRoute. *)
    exact IHr0.
    (* unfold mqt_on_looser_constructors in *. *)
    cbn in *.
    (* Set Printing Implicit. *)
    unfold MQCOnStricterFormulaTypes in *.
    unfold MQCOnStricterFormulaTypes, subclass_apply, subclass_refl in *.
    unfold mqt_on_looser_constructors, ind_on_stricter_constructors, subclass_apply in *. cbn in *.

    induction l.
    exact (IHr0 _f).
    cbn in *. exact (IHr0 _f).

    change (mqt_on_looser_constructors
  (mqt_on_looser_constructors MQ)) with (@mqt_on_looser_constructors V _ (FCWithNVars m) (ler_fcn_subclass (ler_Pn l)) MQ) in _f.
    cbn in *. *)
    }
    {
      apply FcMQC_route_diamond3.
    }
  } *)


(* Lemma FcMQC_routes_equivalent n m p (r0 r1 : leroute n m) (l : ler m p) : FcMQCWithRoute r0 _v (@mqt_on_looser_constructors _ _ _ (ler_fcn_subclass l) MQ) -> FcMQCWithRoute r1 _v (@mqt_on_looser_constructors _ _ _ (ler_fcn_subclass l) MQ).
  intro _f.
  induction r0.
  (* 00 case: *)
  dependent destruction r1; exact _f.
  (* Sm case: *)
  {
    dependent destruction r1.
    specialize (IHr0 r1 (ler_Pn l) _v).
    (* unfold mqt_on_looser_constructors in *. *)
    cbn in *.
    unfold MQCOnStricterFormulaTypes, subclass_apply, subclass_refl in *.
    (* Set Printing Implicit. *)
    unfold mqt_on_looser_constructors, ind_on_stricter_constructors, subclass_apply in *. cbn in *.

    induction l.
    exact (IHr0 _f).
    cbn in *. exact (IHr0 _f).

    change (mqt_on_looser_constructors
  (mqt_on_looser_constructors MQ)) with (@mqt_on_looser_constructors V _ (FCWithNVars m) (ler_fcn_subclass (ler_Pn l)) MQ) in _f.
    cbn in *.
  }
  (* Sn case: *)
  {

  } *)



(* Lemma fcn_routes_equivalent n m (r0 r1 : leroute n m) V (_v : Class _ V) MQ : fcn_instance_route r0 _v MQ -> fcn_instance_route r1 _v MQ.  *)
  

(* Lemma just_uhh1 VC TC MQC MQ : 
  OneMoreQuotvar MQC subclass_refl subclass_refl MQ ->
  MQC _ _ (subclass_trans _ subclass_refl) (subclass_trans _ subclass_refl) MQ.
  (* cbn. *)
  intro.
  (* rewrite subclass_trans_refl2. *)
  (* rewrite subclass_trans_refl2. *)
  destruct H.
  (* unfold MQCOnStricterFormulaTypes in H. *)
  (* rewrite subclass_trans_refl1 in H. *)
  (* rewrite subclass_trans_refl1 in H. *)
  assumption.
Qed.
Lemma just_uhh3 VC TC MQC MQ : 
  NMoreQuotvars 3 MQC subclass_refl subclass_refl MQ ->
  MQC _ _ _ _ MQ.
  (* cbn. *)
  intro.
  (* rewrite subclass_trans_refl2. *)
  (* rewrite subclass_trans_refl2. *)
  destruct H.
  destruct H.
  destruct H.
  (* unfold MQCOnStricterFormulaTypes in H. *)
  (* rewrite subclass_trans_refl1 in H. *)
  (* rewrite subclass_trans_refl1 in H. *)
  (* unfold NMoreQuotvars, NMoreConstructors, NMoreConstructors_subclass in *. *)
  (* rewrite subclass_trans_refl2. *)
  (* rewrite subclass_trans_refl2. *)
  assumption.
Qed. *)

(* Lemma quotvar_unzip_succ VC TC (MQC1 MQC2 : MQCT) :
  MQCSubclassOf MQC1 MQC2 ->
  MQCSubclassOf (OneMoreQuotvar MQC1) (MQCOnStricterFormulaTypes MQC2).
  unfold MQCSubclassOf; intros.
  destruct H0.
  exact (H _ _ _ _ _ H0).
Defined.
Print quotvar_unzip_succ.

Lemma quotvar_unzip_n n VC TC (MQC1 MQC2 : MQCT) :
  MQCSubclassOf MQC1 MQC2 ->
  MQCSubclassOf
    (NMoreQuotvars n MQC1)
    (NMoreQuotvars_without_new_MQCs n MQC2).
  induction n; [trivial | ].
  cbn. intro.
  exact (quotvar_unzip_succ (IHn H)).
Defined.

Lemma stricter_unpack_succ VC TC MQC V _v TC2 eT MQ :
  (@MQCOnStricterFormulaTypes
    VC TC (OneMoreConstructor VC) (OneMoreConstructor TC)
    _ _
    MQC) V _v TC2 eT MQ ->
  MQC _ _ _ _ MQ.
  trivial.
Qed.
Print stricter_unpack_succ.

Lemma stricter_unpack_n n VC TC (MQC : MQCT VC TC) V _v TC2 eT MQ : 
    (NMoreQuotvars_without_new_MQCs n MQC)
      V _v TC2 eT MQ ->
    MQC V _ TC2 _ MQ.
  induction n; [trivial | ].
  intro.
  exact (IHn _ _ H).
Qed. *)
  

Lemma embeddings_to_fcn_instance_ends_at_f_fc n m (u : upto n m) :
  (subclass_apply (fcn_sub_fc n) (embeddings_to_fcn_instance u)) = (@f_fc (NMoreExt m False)).
  
  induction u; [reflexivity|assumption].
Qed.
Lemma fcn_sub_fc_ends_at_f_fc n :
  (subclass_apply (fcn_sub_fc n) (fn_fcn n)) = (@f_fc (NMoreExt n False)).
  
  exact (embeddings_to_fcn_instance_ends_at_f_fc _).
Qed.



(* Lemma FcMQC_subset_n n :
  MQCSubclassOf (FcMQCWithNVars n) (NMoreQuotvars_without_new_MQCs n FcMQC).
  apply quotvar_unzip_n. apply MQCSubclassOf_refl.
Defined. *)

(* Lemma FcMQCn_FcMQC [n V _v TC2 eT MQ] :
  @FcMQCWithNVars n V _v TC2 eT MQ ->
  @FcMQC            V _ TC2 _ MQ.
  intros.
  apply stricter_unpack_n.
  apply FcMQC_subset_n; assumption.
Qed. *)

Lemma FcMQCWithEmbeddings_FcMQC [n m] [u : upto n m] :
  MQCSubclassOf (FcMQCWithEmbeddings u) (MQCOnStricterFormulaTypes FcMQC).
  induction u.
  unfold MQCSubclassOf; intros; assumption.
  {
    unfold MQCSubclassOf. intros. 
    destruct H.
    apply IHu.
    exact H.
  }
Qed.

Lemma FcMQCn_FcMQC [n] :
  MQCSubclassOf (FcMQCWithNVars n) (MQCOnStricterFormulaTypes FcMQC).

  unfold MQCSubclassOf; intros V _v TC2 eT MQ _f.
  apply FcMQCn_embed in _f.
  generalize V _v TC2 eT MQ _f.
  change (MQCSubclassOf (FcMQCWithEmbedNVars n) (MQCOnStricterFormulaTypes FcMQC)).
  apply FcMQCWithEmbeddings_FcMQC.  
Qed.
Arguments FcMQCn_FcMQC [n]%nat_scope [V _v TC2 eT MQ] _.

(* Lemma FcMQC_fold [n] [qf qg : FormulaWithNVars n] TC2 eT [MQ] (_mq : (FcMQCWithNVars n) (FormulaWithNVars n) _ TC2 eT MQ) [f : Ind (FCWithNVars n)] :
  UnfoldStep qf qg ->
  MQ qg f ->
  MQ qf f.

  intros u qg_means_f.

  (* "we don't need the variable constructors for this, discard them and take the FcMQC constructors" *)
  destruct (FcMQCn_FcMQC _mq) as (atmc, (unfc, aplc)).

  (* use the unfold constructor *)
  refine (unfc qf qg (ind_on_stricter_constructors (fcn_sub_fc n) f) _ qg_means_f).

  rewrite fcn_sub_fc_ends_at_f_fc.
  exact u.
Qed. *)

Lemma FcMQC_fold_ind [n] [qf qg : FormulaWithNVars n] [V _v TC2 eT MQ] (_mq : (FcMQCWithNVars n) V _v TC2 eT MQ) [f : Ind TC2] :
  UnfoldStep (fwn_to_ind qf V _v) (fwn_to_ind qg V _v) ->
  MQ (fwn_to_ind qg V _v) f ->
  MQ (fwn_to_ind qf V _v) f.

  intros u qg_means_f.

  (* "we don't need the variable constructors for this, discard them and take the FcMQC constructors" *)
  destruct (FcMQCn_FcMQC _mq) as (atmc, (unfc, aplc)).

  (* use the unfold constructor *)
  refine (unfc _ _ _ _ qg_means_f).

  (* rewrite fcn_sub_fc_ends_at_f_fc. *)
  exact u.
Qed.

(* Lemma FcMQC_Ind_fold n qf qg f :
  UnfoldStep qf qg ->
  MQInd (MQC := FcMQCWithNVars n) qg f ->
  MQInd (MQC := FcMQCWithNVars n) qf f.
  (* Set Printing Implicit. *)
  unfold MQInd. intros u qg_means_f MQ _mq.
  specialize (qg_means_f MQ _mq).
  exact (FcMQC_fold _mq u qg_means_f).
Qed. *)


(****************************************************
      Search for meanings of reified formulas
****************************************************)

Inductive GetResult t :=
  | success : t -> GetResult t
  | timed_out : GetResult t
  | error T : T -> GetResult t.

Notation "? x <- m1 ; m2" :=
  (match m1 with
    | success x => m2
    | timed_out => timed_out _
    | error T s => error _ s
    end) (right associativity, at level 70, x pattern).


Fixpoint unfold_step [Ext] a : option (Formula Ext) :=
  match a with
    (* Atoms never unfold *)
    | f_atm _ => None
    | f_ext _ => None
    (* Unfold in the LHS until you're done... *)
    | fo_apl f x => match unfold_step f with
      | Some g => Some [g x]
      (* Then if you're done with the LHS, check its form... *)
      | None => match f with
        | fo_apl (f_atm atom_const) a =>
            Some a
        | fo_apl (fo_apl (f_atm atom_fuse) a) b =>
            Some [[a x] [b x]]
        | _ => None
        end
      end
    end.
(* Fixpoint unfold_step [Ext] f : option {g : (Formula Ext) | UnfoldStep f g} :=
  match f with
    (* Atoms never unfold *)
    | f_atm _ => None
    | f_ext _ => None
    (* Unfold in the LHS until you're done... *)
    | fo_apl f x => match unfold_step f with
      | Some (exist g u) => Some (exist _ [g x] (unfold_in_lhs x u)) 
      (* Then if you're done with the LHS, check its form... *)
      | None => match f with
        | fo_apl (f_atm atom_const) a =>
            Some (exist _ a (unfold_const a x))
        | fo_apl (fo_apl (f_atm atom_fuse) a) b =>
            Some (exist _ [[a x] [b x]] (unfold_fuse a b x))
        | _ => None
        end
      end
    end. *)

Lemma unfold_step_correct [Ext] (a b : Formula Ext) :
  unfold_step a = Some b -> UnfoldStep a b.
  (* intro e. *)

  refine ((fix r a b := match a as a0 return (a = a0 -> _) with
    (* Atoms never unfold *)
    | f_atm _ => _
    | f_ext _ => _
    (* Unfold in the LHS until you're done... *)
    | fo_apl f x => _
    end eq_refl) a b); clear a0 b0; intros e fe; [discriminate | discriminate | ].

  refine (match unfold_step f as og return (unfold_step f = og -> _) with
      | Some g => _
      (* Then if you're done with the LHS, check its form... *)
      | None => _
      end eq_refl); intro fog; [refine ?[unfold_in_lhs]|refine ?[lhs_done]].
 
  [unfold_in_lhs]: {
    cbn in fe. rewrite fog in fe. injection fe as <-.
    apply (unfold_in_lhs x (r f g fog)).
  }
  [lhs_done] : {
    clear r.
    cbn in fe. rewrite fog in fe.
    refine (match f as f0 return (f = f0) -> _ with
          | fo_apl (f_atm atom_const) a => _
          | fo_apl (fo_apl (f_atm atom_fuse) a) b => _
          | _ => _
          end eq_refl); intro ff; rewrite ff in fe; discriminate || idtac; [refine ?[const_case] | refine ?[fuse_case]].
    
    [const_case]: {
      injection fe as <-.
      exact (unfold_const a x).
    }
    [fuse_case]: {
      injection fe as <-.
      exact (unfold_fuse a b x).
    }
  }
Qed.


Definition unreify_vars [Ext]
  (vars : Ext -> bool)
  : Ext -> Prop :=
  λ e, true = (vars e).

Fixpoint get_folded_atom [Ext] steps (f : Formula Ext) :=
  match steps with 0 => timed_out _ | S pred =>
    match unfold_step f with
      | Some g => get_folded_atom pred g
      | None => match f with
        | f_atm a => success a
        | _ => error _ ("not a folded atom:")
        end
      end
    end.   

Lemma get_folded_atom_correct [Ext] steps (f : Formula Ext) a :
  get_folded_atom steps f = success a -> UnfoldsToKind (@IsAtom _ _) f a.

  refine ((fix r steps f :=
    match steps as n0 return (steps = n0) -> _ with 0 => _ | S pred => _ end eq_refl) steps f)
    ; intros ne e; [discriminate|].
  
   refine (match unfold_step f as og return (unfold_step f = og -> _) with
      | Some g => _
      (* Then if you're done with the LHS, check its form... *)
      | None => _
      end eq_refl); intro fog; cbn in e; rewrite fog in e; [refine ?[unfold]|refine ?[flat]].
 
  [unfold]: {
    exact (utk_step (unfold_step_correct _ fog) (r pred g e)).
  }
  [flat]: {
    clear r fog.
    refine (match f as f0 return (f = f0) -> _ with
      | f_atm a => _
      | _ => _
      end eq_refl); intros ->; discriminate || idtac.
    
    injection e as <-. apply utk_done. apply is_atom.
  }
Qed.

Definition QfResult n := Ind (FCWithNVars n).

Fixpoint get_quoted_formula steps [n] (qf : FormulaWithNVars n)
  : GetResult (QfResult n) :=
  match steps with 0 => timed_out _ | S pred =>
    match unfold_step qf with
      | Some qg => get_quoted_formula pred qg
      | None => match qf with
          | fo_apl (f_atm atom_quote) a =>
            ? a <- get_folded_atom pred a ; 
            success (λ _ _, (fc_atm a))
          | fo_apl (fo_apl (f_atm atom_quote) qa) qb =>
            ? a <- get_quoted_formula pred qa ; 
            ? b <- get_quoted_formula pred qb ;
            success (λ _ _, [(a _ _) (b _ _)])
          | f_ext e => success (ewn_to_ind e)
          | _ => error _ ("not a quoted formula:", qf)
          end
      end
  end.

Lemma ext_new_quotvar_rewrap_impl [n m] (embedding : ltr n m)
  : VInd_MQInd (MQC := FcMQCWithNVars m) (embedded_var_ind embedding) (embedded_var_ind embedding).
  induction embedding; unfold VInd_MQInd, MQInd; intros; destruct _mq as (embed, new).
  {
    exact (new _ {| omc_new := fc_atm atom_const |}).
  }
  {
    exact (IHembedding _ _ _ _ _ embed).
  }
Qed.


Lemma ext_quotvar_rewrap_impl [n m] (embeddings : upto n m) (e : NMoreExt n False)
  : VInd_MQInd (MQC := FcMQCWithNVars m) (ewnm_to_ind embeddings e) (ewnm_to_ind embeddings e).
  induction embeddings; [contradiction|].
  destruct e; [apply IHembeddings|apply ext_new_quotvar_rewrap_impl].
Qed.

Lemma ext_quotvar_rewrap [n] (e : NMoreExt n False)
  : VInd_MQInd (MQC := FcMQCWithNVars n) (ewn_to_ind e) (ind_on_stricter_constructors _ (ewn_to_ind e)).
  (* unfold subclass_apply. *)

  induction n; [contradiction|].
  destruct e; [refine ?[embed]|refine ?[new]].

  [new]: {
    unfold VInd_MQInd, MQInd; intros.
    destruct _mq as (embed, new).
    exact (new _ {| omc_new := fc_atm atom_const |}).
  }
  [embed]: {
    apply ext_quotvar_rewrap_impl.
  }
Qed.


Lemma get_quoted_formula_correct
  steps [n] (qf : FormulaWithNVars n) f :
  get_quoted_formula steps qf = success f ->
    VInd_MQInd (MQC := FcMQCWithNVars n) (fwn_to_ind qf) f.
  
  refine ((fix r steps n (qf : FormulaWithNVars n) f :=
    match steps as n0 return (steps = n0) -> _ with 0 => _ | S pred => _ end eq_refl) steps n qf f)
    ; intros ne e; [discriminate|].
  
  refine (match unfold_step qf as oqg return (unfold_step qf = oqg -> _) with
      | Some qg => _
      | None => _
      end eq_refl); intro fog; cbn in e; rewrite fog in e; [refine ?[unfold]|refine ?[flat]].
  
  [unfold]: {
    unfold VInd_MQInd, MQInd; intros.
    pose (unfold_step_correct _ fog) as u.
    specialize (r pred n qg f e _ _ _ _ _ _mq).
    exact (FcMQC_fold_ind _mq (unfold_rewrap u _ _) r).
  }
  [flat]: {
    clear fog.
    
    unfold VInd_MQInd, MQInd; intros.
    destruct (FcMQCn_FcMQC _mq) as (atmc, (unfc, aplc)).

    refine (match qf as qf0 return (qf = qf0) -> _ with
      | fo_apl (f_atm atom_quote) a => _
      | fo_apl (fo_apl (f_atm atom_quote) qa) qb => _
      | f_ext e => _
      | _ => _
      end eq_refl); intros ->; discriminate || idtac;
      [refine ?[ext] | refine ?[qatm] | refine ?[qaply]].
    
    [qatm]: {
      (* TODO reduce duplicate code ID 3894038493 *)
      refine (match (get_folded_atom pred a) as a0 return (get_folded_atom pred a = a0) -> _ with
        | success atm => _
        | _ => _
        end eq_refl); intro eq; rewrite eq in e; discriminate || idtac.

        injection e as <-.

        pose (get_folded_atom_correct pred _ eq) as atc.
        apply atmc.
        exact (utk_rewrap atc _ _).
    }
    [qaply]: {
      (* TODO reduce duplicate code ID 3894038493 *)
      refine (match (get_quoted_formula pred qa) as qa0 return (get_quoted_formula pred qa = qa0) -> _ with
        | success a => _
        | _ => _
        end eq_refl); intro eqa; rewrite eqa in e; discriminate || idtac.
      refine (match (get_quoted_formula pred qb) as qb0 return (get_quoted_formula pred qb = qb0) -> _ with
        | success b => _
        | _ => _
        end eq_refl); intro eqb; rewrite eqb in e; discriminate || idtac.

        injection e as <-.

        pose (r pred _ _ _ eqa) as ar.
        pose (r pred _ _ _ eqb) as br.
        apply aplc.
        exact (ar _ _ _ _ _ _mq).
        exact (br _ _ _ _ _ _mq).
    }
    [ext]: {
      (* clear atmc unfc aplc. *)
      injection e0 as <-.
      exact (ext_quotvar_rewrap _ _ _ _ _mq).
    }
  }
Qed.


Definition MiSearchResult n : Type :=
    @Ruleset (FCWithNVars n).

(* Fixpoint specialize_prop_meaning TC T (P : @Ruleset (OneMoreConstructor TC) T) (tx : Ind TC): @Ruleset TC T := 
  match P with
  | ruleset_implies p c => ruleset_implies p c
  | ruleset_and A B => ruleset_and (specialize_prop_meaning A tx) (specialize_prop_meaning B tx)
  | ruleset_forall F => ruleset_forall (λ T2 _t2 tx2, specialize_prop_meaning (F T2 {| omc_new := tx _ _ |} tx2))
  end. *)

Fixpoint get_prop_meaning steps [n] (f : FormulaWithNVars n)
  : GetResult (MiSearchResult n) :=
  match steps with 0 => timed_out _ | S pred =>
    match unfold_step f with
      | Some g => get_prop_meaning pred g
      | None => match f with
        (* [qp -> qc] *)
        | fo_apl (fo_apl (f_atm atom_implies) qp) qc =>
          ? p <- (get_quoted_formula pred qp) ;
          ? c <- (get_quoted_formula pred qc) ;
          success (ruleset_implies p c)
        
        (* [a & b] *)
        | fo_apl (fo_apl (f_atm atom_and) a) b =>
          ? A <- (get_prop_meaning pred a) ;
          ? B <- (get_prop_meaning pred b) ;
          (* success (A ∧4 B) *)
          success (ruleset_and A B)

        (* [forall_quoted_formulas f] *)
        | fo_apl (f_atm atom_forall_quoted_formulas) f =>
          ? Fx <- (get_prop_meaning pred (n := S n)
              [(embed_formula (λ a, ome_embed a) f)
                  (f_ext ome_new)]) ; 
                  (* TODO: be able to strip off the extra variable BEFORE putting under binding: *)
            success (ruleset_forall Fx)
        | _ => error _ ("not a proposition:", f)
      end
    end
  end.


(* Lemma unfold_fx_embed [n] (f : FormulaWithNVars n)
(Fx : (MiSearchResult (n := S n) [(embed_formula (λ a, ome_embed a) f)
                  (f_ext ome_new)]))
                  
  T (_t : Class (OneMoreConstructor (NMoreConstructors n FormulaConstructors)) T)
  : (λ H : InfSet T,
  Fx T
  {| omc_embed := OneMoreConstructor_subclass _t; omc_new := omc_new |} H)
= Fx T _t.
  induction n; cbn.
  reflexivity. *)

  

  

Lemma get_prop_meaning_correct
  steps [n] (f : FormulaWithNVars n) rule :
  get_prop_meaning steps f = success rule ->
    ∀ V _v,
    FormulaMeans (MQC := FcMQCWithNVars n) (fwn_to_ind f V _v) rule.
  
  refine ((fix r steps n (f : FormulaWithNVars n) rule :=
    match steps as n0 return (steps = n0) -> _ with 0 => _ | S pred => _ end eq_refl) steps n f rule)
    ; intros ne e; [discriminate|].
  
  (* unfold MQInd; intros. *)
  refine (match unfold_step f as oqg return (unfold_step f = oqg -> _) with
      | Some g => _
      | None => _
      end eq_refl); intro fog; cbn in e; rewrite fog in e; [refine ?[unfold]|refine ?[flat]].
  Print mi_unfold.
  [unfold]: {
    pose (unfold_step_correct _ fog) as u.
    intros.
    specialize (r pred n g rule e V _v).
    exact (mi_unfold (VC := FCWithNVars n) (a := (fwn_to_ind f V _v)) (b := (fwn_to_ind g V _v)) (unfold_rewrap u V _v) r).
  }
  [flat]: {
    clear fog.

    refine (match f as f0 return (f = f0) -> _ with
        (* [qp -> qc] *)
        | fo_apl (fo_apl (f_atm atom_implies) qp) qc => _
        
        (* [a & b] *)
        | fo_apl (fo_apl (f_atm atom_and) a) b => _

        (* [forall_quoted_formulas f] *)
        | fo_apl (f_atm atom_forall_quoted_formulas) f => _
        | _ => _
      end eq_refl); intros ->; discriminate || idtac;
      [refine ?[forall_case] | refine ?[implies_case] | refine ?[and_case]].
    
    [implies_case]: {
      (* TODO reduce duplicate code ID 3894038493 *)
      refine (match (get_quoted_formula pred qp) as qp0 return (get_quoted_formula pred qp = qp0) -> _ with
        | success p => _
        | _ => _
        end eq_refl); intro eqp; rewrite eqp in e; discriminate || idtac.
      refine (match (get_quoted_formula pred qc) as qc0 return (get_quoted_formula pred qc = qc0) -> _ with
        | success c => _
        | _ => _
        end eq_refl); intro eqc; rewrite eqc in e; discriminate || idtac.

        injection e as <-.
        apply get_quoted_formula_correct in eqp.
        apply get_quoted_formula_correct in eqc.
        intros.
        exact (mi_implies (eqp _ _) (eqc _ _)).
    }
    [and_case]: {
      (* TODO reduce duplicate code ID 3894038493 *)
      refine (match (get_prop_meaning pred a) as a0 return (get_prop_meaning pred a = a0) -> _ with
        | success a => _
        | _ => _
        end eq_refl); intro eqa; rewrite eqa in e; discriminate || idtac.
      refine (match (get_prop_meaning pred b) as b0 return (get_prop_meaning pred b = b0) -> _ with
        | success b => _
        | _ => _
        end eq_refl); intro eqb; rewrite eqb in e; discriminate || idtac.

        injection e as <-.

        intros.
        (* apply r in eqa.
        apply r in eqb. *)
        exact (mi_and
          (r _ _ _ _ eqa _ _) (r _ _ _ _ eqb _ _)).
    }
    [forall_case]: {
      refine (match (get_prop_meaning pred (n := S n)
              [(embed_formula (λ a, ome_embed a) f)
                  (f_ext ome_new)]) as fx2 return ((get_prop_meaning pred (n := S n)
              [(embed_formula (λ a, ome_embed a) f)
                  (f_ext ome_new)]) = fx2) -> _ with
        | success Fx => _
        | _ => _
        end eq_refl); intro eq; cbn in eq; rewrite eq in e; discriminate || idtac.

      injection e as <-.

(* Print mi_forall_quoted_formulas. *)
      intros.
      refine (mi_forall_quoted_formulas (fwn_to_ind f) _).
      intros.
      (* cbn. *)
      unfold shortcut_omc_trans_apply , subclass_refl, subclass_apply.
      pose (embed_formula_rewrap f _v0) as rewrap.
      change (@fwn_to_ind n f V0 _) with (@fwn_to_ind n f V0 (@OneMoreConstructor_subclass (FCWithNVars n) V0 _v0)) in rewrap.
      rewrite <- rewrap.
  
      exact (r _ _ _ _ eq _ _).
    }
  }
Qed.

(****************************************************
   Practicalities of concrete formula construction
****************************************************)

Definition f_id {F} `{FunctionConstructors F} : F := [fuse const const].

Definition f_with_variable [Ext]
  (fgen : Formula (OneMoreExt Ext) ->
          Formula (OneMoreExt Ext)) : Formula (OneMoreExt Ext) :=
  (fgen (f_ext ome_new)).

Fixpoint eliminate_abstraction
  [Ext]
  (f : Formula (@OneMoreExt Ext))
  : Formula Ext :=
  match f with
    | f_atm a => [const (f_atm a)]
    | f_ext e => match e with
      | ome_new => f_id
      | ome_embed e => [const (f_ext e)]
      end
    | fo_apl a b => [fuse (eliminate_abstraction a) (eliminate_abstraction b)]
    end.

Fixpoint quote_f [Ext] f : Formula Ext :=
  match f with
    | f_atm _ => [f_quote f]
    (* assume this is a variable that represents a quoted formula: *)
    | f_ext _ => f
    | fo_apl a b => [f_quote (quote_f a) (quote_f b)]
    end.

Inductive ParensState := ps_default | ps_apply_chain | ps_fuse_chain.
Fixpoint display_f_impl ps [Ext] (f : Formula Ext) : string :=
  match f with
    | f_ext _ => "@"
    | fo_apl (fo_apl (f_atm atom_fuse)
      (f_atm atom_const))
      (f_atm atom_const) => "id"
    | fo_apl (fo_apl (f_atm atom_fuse) a) b => 
      let 
        b := display_f_impl ps_default b in
      let items := match a with
        | fo_apl (f_atm atom_const) (f_atm atom_implies) => b ++ " ->" 
         | _ =>
         display_f_impl ps_fuse_chain a ++ " " ++ b
         end in
      match ps with
        | ps_fuse_chain => items
        | _ => "[" ++ items ++ "]"
        end
    | fo_apl a b => 
      let 
        b := display_f_impl ps_default b in
      let items := match a with
        | f_atm atom_implies => b ++ " ->" 
        | _ =>
         display_f_impl ps_fuse_chain a ++ " " ++ b
         end in
      match ps with
        | ps_apply_chain => items
        | _ => "(" ++ items ++ ")"
        end
    | f_atm a => match a with
      | atom_const => "c"
      | atom_fuse => "fuse"
      | atom_implies => "implies"
      | atom_and => "and"
      | atom_forall_quoted_formulas => "⋀"
      | atom_quote => "“"
      end
    end.
  
Definition display_f := display_f_impl ps_default.

Notation "[ x => y ]" :=
  (eliminate_abstraction (f_with_variable (λ x, y)))
  (at level 0, x at next level, y at next level).
  
Notation "[ ∀ x , y ]" :=
  [⋀ [x => y]]
  (at level 0, x at next level, y at next level).

(* Definition foo : StandardFormula := [x => [x & x]].
Print foo.
Eval lazy in foo.
Eval cbv beta iota delta -[f_id const fuse] in foo. *)

(* Definition no_vars (e:False) := false.
Definition no_meanings R
 : revar_meanings no_vars R.
  unfold revar_meanings, unreify_vars.
  intros. dependent destruction H.
Defined. *)

(* Definition no_meanings R (e:False) : (true = false) -> R.
  intro. dependent destruction H.
Defined. *)

(* Definition with_no_meanings
  f
  (g : GetResult (MiSearchResult no_vars f)) :
  GetResult (∀ F `(FormulaConstructors F), InfSet F -> Prop) :=
  ? g <- g ;
  success (λ F _ infs, g F _
        (no_meanings _) infs). *)

(* Definition get_prop_meaning n f :=
  (with_no_meanings (get_prop_meaning n f no_vars)). *)

Parameter Infs : InfSet StandardFormula.
Definition simplify_meaning
  (meaning : MiSearchResult 0)
  := Ruleset_to_Coq (meaning) Infs.
Definition get_prop_meaning_simplified n f :=
  ? g <- get_prop_meaning n f ;
  success (simplify_meaning g).

Definition test0 : StandardFormula :=
  [[f_quote const] -> [f_quote const]].
Eval compute in (get_prop_meaning_simplified 90 test0).

(* Set Typeclasses Debug Verbosity 2. *)
Definition test05 : StandardFormula := [∀ a, [a -> a]].
Eval compute in (get_prop_meaning_simplified 90 test05).


Fixpoint embed_nmore n [Ext] (f : Formula Ext)
  : (Formula (NMoreExt n Ext)) :=
  match n return Formula (NMoreExt n Ext) with
    | 0 => f
    | S pred => embed_formula ome_embed (embed_nmore pred f)
    end.
Notation "f @ n" := (embed_nmore n f) (at level 0).


(****************************************************
              Concrete axioms of IC
****************************************************)

Definition ax_refl : StandardFormula :=
  [∀a, [a -> a]].
(* Definition ax_trans : StandardFormula :=
  [∀a, [a -> a]]. *)

Definition dup : StandardFormula :=
  [∀a,
    [a -> (quote_f [a & a])]
  ].
Eval compute in display_f dup.
Eval compute in (get_prop_meaning_simplified 90 dup).

Definition drop : StandardFormula :=
  [∀a, [∀ctx,
    [(quote_f [ctx & (a@1)]) -> ctx]
  ]].

Definition and_sym : StandardFormula :=
  [∀a, [∀b,
    [(quote_f [(a@1) & b])
    -> (quote_f [b & (a@1)])]
  ]].
Eval compute in display_f and_sym.
(* Eval cbv beta iota delta in and_sym. *)
Eval compute in (get_prop_meaning_simplified 90 and_sym).

Definition and_assoc_left : StandardFormula :=
  [∀a, [∀b, [∀c,
    [(quote_f [(a@2) & [(b@1) & c]])
    -> (quote_f [[(a@2) & (b@1)] & c])]
  ]]].
Eval compute in (get_prop_meaning_simplified 1890 and_assoc_left).

Definition and_assoc_right : StandardFormula :=
  [∀a, [∀b, [∀c,
    [(quote_f [[(a@2) & (b@1)] & c])
    -> (quote_f [(a@2) & [(b@1) & c]])]
  ]]].

(****************************************************
              Definitions of inference
****************************************************)

Definition f_default {Ext} : Formula Ext := const.
Definition sf_default : StandardFormula := f_default.
Definition default_ruleset : Ruleset := ruleset_implies (fwn_to_ind sf_default) (fwn_to_ind sf_default).
Definition reflexivity {TC} : Rule
  := λ _ _ infs, ∀ a, infs a a.
Definition transitivity {TC} : Rule
  := λ _ _ infs, ∀ a b c, infs a b -> infs b c -> infs a c.
Arguments reflexivity {TC} {T} {_t} _.
Arguments transitivity {TC} {T} {_t} _.

Definition infs_provable_from {TC:TConsClass} (rules : Ruleset) :
  ∀ T {_t:Class TC T}, InfSet T
  := λ _ _ p c, ∀ infs,
    reflexivity infs ->
    transitivity infs ->
    Ruleset_to_Coq rules infs ->
    infs p c.
Arguments infs_provable_from {TC} rules [T]%type_scope {_t} p c.

Definition rules_implies {TC:TConsClass} (premise : Ruleset) (conclusion : Ruleset) : Prop
  := ∀ T (_t:Class TC T) (infs : InfSet T), reflexivity infs -> transitivity infs -> Ruleset_to_Coq premise infs -> Ruleset_to_Coq conclusion infs.

(****************************************************
          Putting together the axioms of IC
****************************************************)

(* Fixpoint to_construction (f : StandardFormula) {F} `{FormulaConstructors F}
  : F
  := match f with
    | f_atm a => fc_atm a
    | f_ext e => match e with end
    | fo_apl a b => [(to_construction a) (to_construction b)]
    end. *)

Definition IC_axioms : StandardFormula := 
  [
    [ax_refl & [dup & drop]]
    & [and_sym & [and_assoc_left & and_assoc_right]]].

Definition IC_external_rules : Ruleset :=
  match get_prop_meaning 900 IC_axioms with
  | success r => r
  | _ => default_ruleset
  end.
Eval compute in (simplify_meaning IC_external_rules).


Definition IC_provable_infs := infs_provable_from IC_external_rules.
Arguments IC_provable_infs {T _}.
Definition IC_provable_props := IC_provable_infs IC_axioms.

Definition IC_implements_inference_for
  n axioms Axioms p P
  (_a : FormulaMeans (MQC := FcMQCWithNVars n) axioms Axioms)
  (_p : FormulaMeans (MQC := FcMQCWithNVars n) p P)
  := (rules_implies Axioms P) -> (IC_provable_infs axioms p).
Print IC_implements_inference_for.


Definition IC_can_preserve_left_context_when_using [n]
  (r : @Ruleset (FCWithNVars n)) := ∀ ctx p c, (infs_provable_from r p c) -> (IC_provable_infs [ctx & p] [ctx & c]).
Print IC_can_preserve_left_context_when_using.

Lemma rules_positive {TC} T (_t : Class TC T) R (infs0 infs1 : InfSet T) :
  (∀ p c, infs0 p c -> infs1 p c) -> Ruleset_to_Coq R infs0 -> Ruleset_to_Coq R infs1.
  induction R; cbn.
  intros; apply H; assumption.
  {
    intros. destruct H0.
    split.
    apply IHR1; assumption.
    apply IHR2; assumption.
  }
  {
    intros.
    apply IHR.
    assumption.
    apply H0.
  }
Qed.
Print rules_positive.

Lemma and_proves_more_left {TC} T (_t : Class TC T)
  (R S : @Ruleset TC) p c : infs_provable_from R (T:=T) p c -> infs_provable_from (ruleset_and R S) p c.
  unfold infs_provable_from. intros.
  destruct H2.
  apply H; assumption.
Qed.

Lemma and_proves_more_right {TC} T (_t : Class TC T)
  (R S : @Ruleset TC) p c : infs_provable_from S (T:=T) p c -> infs_provable_from (ruleset_and R S) p c.
  unfold infs_provable_from. intros.
  destruct H2.
  apply H; assumption.
Qed.

Lemma forall_proves_more {TC}
  (R : @Ruleset (OneMoreConstructor TC)) : ∀ T (_t : Class TC T) (x : T) p c, infs_provable_from R (_t := {| omc_new := x |}) p c -> infs_provable_from (ruleset_forall R) p c.
  intros.
  unfold infs_provable_from. intros.
  (* apply H; solve [unfold infs_provable_from; intros; assumption] || idtac.
  unfold reflexivity. intros.  *)
  
  apply H; [assumption | assumption | apply H2].
  (* change (λ p0 c0 : T, infs p0 c0) with infs. *)
  (* Set Printing Implicit. *)
  (* cbn in H2. *)
  (* exact (H2 x). *)
Qed.

Lemma provable_obey_rules {TC} T (_t : Class TC T) (R : @Ruleset TC) : Ruleset_to_Coq R (infs_provable_from R (T:=T)).
  induction R; cbn.
  { unfold infs_provable_from. intros. apply H1. }
  {
    split.
    eapply rules_positive; [|apply IHR1].
    apply and_proves_more_left.
    eapply rules_positive; [|apply IHR2].
    apply and_proves_more_right.
  }
  {
    intro.
    eapply rules_positive; [|apply IHR].
    apply forall_proves_more.
  }
Qed.
  

Lemma rules_implies_and_intro {TC} A B C : rules_implies A B -> rules_implies A C -> rules_implies A (ruleset_and B C).
  intros _B _C.
  unfold rules_implies in *. intros T _t infs refl trans rp.
  split.
  apply _B; assumption.
  apply _C; assumption.
Qed.

Lemma IC_can_preserve_left_context_when_using__and n a b :
  IC_can_preserve_left_context_when_using a ->
  IC_can_preserve_left_context_when_using b ->
  @IC_can_preserve_left_context_when_using n (ruleset_and a b).
  
  intros _a _b.
  unfold IC_can_preserve_left_context_when_using; intros.
  (* unfold IC_provable_infs, infs_provable_from; intros infs refl trans icp. *)

  unfold infs_provable_from in H.

  apply H.

  { intros f infs refl trans icp. apply refl. }

  { intros x y z xy yz infs refl trans icp. exact (trans _ _ _ (xy _ refl trans icp) (yz _ refl trans icp)). }

  cbn.
  split.
  { 
    refine (rules_positive _ a _ _ _ _).
    apply _a.
    apply provable_obey_rules.
  }
  { 
    refine (rules_positive _ b _ _ _ _).
    apply _b.
    apply provable_obey_rules.
  }
Qed.
  


Lemma IC_implements_inference_case__and
  n axioms Axioms p P q Q
  (_a : FormulaMeans (MQC := FcMQCWithNVars n) axioms Axioms)
  (_p : FormulaMeans (MQC := FcMQCWithNVars n) p P)
  (_q : FormulaMeans (MQC := FcMQCWithNVars n) q Q)
  (IHp : IC_implements_inference_for _a _p)
  (IHq : IC_implements_inference_for _a _q)
  : IC_implements_inference_for _a (mi_and _p _q).
  unfold IC_implements_inference_for, rules_implies in *.
  intros.
  cbn in H.
  (* apply proj1 in H. *)
  assert (IC_provable_infs axioms p). { apply IHp. intros. destruct (H _ _ _ H0 H1 H2). assumption. }
  assert (IC_provable_infs axioms q). { apply IHq. intros. destruct (H _ _ _ H1 H2 H3). assumption. }
  clear IHp IHq H.
  
  intros infs refl trans icp.
  (* specialize (H0 infs refl trans icp).
  specialize (H1 infs refl trans icp). *)

















(* Definition tejhst : 
  ∀ (Axioms : ∀ {T} {_:Class FormulaConstructors T}, InfSet T -> Prop)
    (P : ∀ {T} {_:Class FormulaConstructors T}, InfSet T -> Prop),

      P (infs_provable_from (@Axioms) _). *)


(* Lemma FormulaMeans_induction_with_meaning_only
  (IH : ∀ {TC}, Ruleset → Prop)
  (implies_case :
    (∀ TC (p c : Ind TC), IH (ruleset_implies p c)))
  (and_case : ∀ TC A B, IH A -> IH B ->
    IH (ruleset_and A B))
  (forall_case : ∀ TC (F : ∀ T, Class TC T → T → InfSet T → Prop),
    @IH (OneMoreConstructor TC) (λ _ _ _,  F _ _ omc_new _) →
    IH (λ _ _ _, ∀ x, F _ _ x _))
  :
  ∀ VC TC (MQC : MQCT) (_vp : VC ⊆ PropositionConstructors) i r,
    FormulaMeans i r → IH r.
  
  intros.
  induction H; [
    refine ?[implies_case] |
    refine ?[unfold_case] |
    refine ?[and_case] |
    refine ?[forall_case]].
  
  [implies_case]: { apply implies_case. }
  [unfold_case]: { assumption. }
  [and_case]: { apply and_case; assumption. }
  [forall_case]: { apply forall_case; assumption. }
Qed. *)


(* Lemma fwn_ind_roundtrip n (x : Ind (FCWithNVars n)) T _t : 
(fwn_to_ind (x (FormulaWithNVars n) _) T _t). *)

(* Set Printing Implicit. *)
Lemma mq_fwn_ind_roundtrip n :
    let VC : VConsClass := FCWithNVars n in
    let TC : TConsClass := FCWithNVars n in
    let MQC : MQCT VC TC := FcMQCWithNVars n in
    ∀ qx x,
      MQInd qx x ->
      MQInd qx
        (fwn_to_ind
        (x (FormulaWithNVars n) _)).
  admit.
  unfold MQInd.
  intros.
  (* induction n. *)
  (* cbn in *. *)
  (* unfold FcMQCWithNVars in *. *)

  specialize (H V _).
  specialize (H (FormulaWithNVars n) _).
  (* Set Printing Implicit. *)
  unfold MQT in H.

  pose (λ V _v T2 _t2 qxVv xFn,
      ∀ eq : ((FormulaWithNVars n) = T2),
        match eq in _ = Fn return (Class (FCWithNVars n)
  Fn -> Fn -> Prop) with
        | eq_refl => λ _t2_fixed xFn_fixed, ∀ _eq : (_t2_fixed = (fn_fcn n)), match _eq with
          | eq_refl => MQ V _v T _t qxVv (fwn_to_ind xFn_fixed T _t)
          end
        end _t2 xFn) as MQ2.
  specialize (H MQ2).
  assert (FcMQCWithNVars _ _ _ MQ2); [refine ?[prove_MQ2_cases] | refine ?[use_MQ2]].
  [use_MQ2]: {
    specialize (H H1).
    unfold MQ2 in H1.
    apply H2.
    admit.
  }
  [prove_MQ2_cases]: {
    clear H.
    unfold MQ2. clear MQ2.
    induction n.
    cbn in *.
    unfold FcMQC. intuition cbn.
    substitute <- eq.

    unfold FcMQCWithNVars, FCWithNVars, FormulaWithNVars in *.
  }

  cbn in H.

  pose ((λ V _v T _t qx x, MQ V _v T _t (qx V _v)
  (fwn_to_ind
  (x (FormulaWithNVars n)
  (fn_fcn n))
  T
  _t)) : MQT) as MQ2.

  unfold FcMQC in *.
  specialize (H V _v T _t MQ H0).

  apply H.
  induction H.
Qed.

(* Set Printing Implicit. *)
(* Fixpoint fn_fcn n i : Class
  (FCWithNVars i)
  (FormulaWithNVars
  n) := match i return Class
  (FCWithNVars i)
  (FormulaWithNVars
  n) with
    | 0 => f_fc
    | S p => {|
        omc_embed := fn_fcn n p ;
        omc_new := 
        cheat
        (* f_ext (@ome_new (NMore n False)) *)
         |}
    end.
Existing Instance fn_fcn. *)

Section IC_implements_inference.

Variable axioms : ∀ {V} {_:Class FormulaConstructors V},
  V.
Variable Axioms : ∀ {T} {_:Class FormulaConstructors T},
  InfSet T -> Prop.
Variable aA : FormulaMeans (MQC := FcMQC) (@axioms) (@Axioms).

Section IC_implements_inference_cases.

Variable n : nat.
(* Local Instance VC : VConsClass := FCWithNVars n.
Local Instance TC : TConsClass := FCWithNVars n.
Local Instance MQC : MQCT := FcMQCWithNVars n. *)

(* Implicit Type VC : VConsClass.
Implicit Type TC : TConsClass.
Implicit Type MQC : MQCT VC TC. *)

(* Variable VC : VConsClass.
Variable TC : TConsClass.
Existing Instance VC.
Existing Instance TC.
Variable MQC : MQCT.
Variable vcf : VC ⊆ FormulaConstructors.
Variable tcf : TC ⊆ FormulaConstructors.
Existing Instance MQC.
Existing Instance vcf.
Existing Instance tcf. *)
(* Variable mqcf :
  ∀ VC2 TC2 (_ : VC2 ⊆ VC) (_ : TC2 ⊆ TC) MQ,
    MQC _ _ MQ -> FcMQC _ _ MQ. *)

(* Local Instance vcp : VC ⊆ PropositionConstructors := consume _. *)

Variable p : ∀ {V} {_:Class (FCWithNVars n) V}, V.
Variable P : ∀ {T} {_:Class (FCWithNVars n) T}, InfSet T -> Prop.
Variable pP : FormulaMeans (MQC := FcMQCWithNVars n) (@p) (@P).

Definition p_proven := ∀ T (_t:Class (FCWithNVars n) T) (infs : InfSet T),
        let _ : TConsClass := FCWithNVars n in
        reflexivity _ infs ->
        transitivity _ infs ->
        Axioms infs -> P infs.

Definition IH := p_proven -> ∀ V (_v:Class (FCWithNVars n) V),
        IC_provable_infs axioms p.

End IC_implements_inference_cases.

Print IH.

(* Set Typeclasses Debug Verbosity 2. *)
Definition implies_case_AxIH [n] {V} {_v: Class (FCWithNVars n) V}
  (infs : InfSet V)
  (p c : ∀ {T} {_:Class (FCWithNVars n) T}, T)  := 
      (* let _ : VConsClass := FCWithNVars n in *)
      (* let _ : TConsClass := FCWithNVars n in *)
      let _ : MQCT := FcMQCWithNVars n in
      (* let _ : Class FormulaConstructors V := consume _ in *)
      (* let _ : Class PropositionConstructors V := consume _ in *)
      (* cheat. *)
  ∀ (qp qc : ∀ V, Class (FCWithNVars n) V → V),
        MQInd qp (@p) -> MQInd qc (@c) ->
        infs axioms (f_implies (qp V _v) (qc V _v)).

(* Definition testfcn n : Class
  (FCWithNVars n)
  (FormulaWithNVars
  n) := _. *)

(* Print VC. *)
Lemma implies_case {n}
      (qp qc : ∀ {V} {_:Class (FCWithNVars n) V}, V)
      (p c : ∀ {T} {_:Class (FCWithNVars n) T}, T)
      :
      let VC : VConsClass := FCWithNVars n in
      let TC : TConsClass := FCWithNVars n in
      let MQC : MQCT VC TC := FcMQCWithNVars n in
      (MQInd (@qp) (@p)) ->
      (MQInd (@qc) (@c)) ->
      IH n
        (λ V _,
          [qp -> qc])
        (λ _ _ infs, infs p c).
  intros.
  unfold IH, IC_provable_infs, infs_provable_from.
  intros. destruct H2 as (refl, (trans, ic)).
  cbv in refl. cbv in trans.
  unfold p_proven, reflexivity, transitivity in H1.
  
  specialize (H1 (FormulaWithNVars n)).
  specialize (H1 _).
  specialize (H1 (λ p c, (implies_case_AxIH infs) (fwn_to_ind p) (fwn_to_ind c))).

  cbn in H1.
  (* Set Printing Implicit. *)
  unfold FormulaWithNVars in *.

  assert (implies_case_AxIH infs
    (fwn_to_ind
    (p Formula
    (fn_fcn n)))
    (fwn_to_ind
    (c Formula
    (fn_fcn n)))); [refine ?[axih_cases]|refine ?[use_proven_axih]].

  [use_proven_axih]: {
    unfold implies_case_AxIH in H2.
    specialize (H2 qp qc).
    specialize (H2 (mq_fwn_ind_roundtrip n H)).
    specialize (H2 (mq_fwn_ind_roundtrip n H0)).
    exact H2.
    admit.
  }

  [axih_cases]: {
    apply H1; clear H1;
      [refine ?[refl_case]|refine ?[trans_case]|refine ?[rules_case]].

    [refl_case]: {
      unfold implies_case_AxIH. intros.
      (* TODO: axiom fetching tactic *)
      compute in ic. destruct ic.
    }

    [rules_case]: { 
        unfold implies_case_AxIH.
      refine (
        match aA in (FormulaMeans a A) return (A _ _
  (λ p0 c0 : Formula,
  ∀ qp0
 qc0 : ∀ V0 : Type,
  Class (FCWithNVars n)
  V0
→ V0,
  MQInd qp0
  (fwn_to_ind p0)
→ MQInd qc0
  (fwn_to_ind c0)
→ infs (a _ _)
  (f_implies
  (qp0 Formula
  (fn_fcn n))
  (qc0 Formula
  (fn_fcn n))))) with 
          | mi_implies qp qc p c x y => _
          | mi_unfold a b B unf bB => _
          | mi_and a A b B aA bB => _
          | mi_forall_quoted_formulas f F fxFX => _
          end
      ); clear axioms Axioms aA; [
        refine ?[implies_case]
        |refine ?[unfold_case]
        |refine ?[and_case]
        |refine ?[forall_case]].

      [implies_case]: {
        clear qp0 qc0 H H0.
        clear f f0 f1.
        clear V _v.
        unfold _proves.
        intros.

        (* qp0/qc0 and qp/qc are quoted versions of the same thing (p/c)
           within FcMQC, where that implies qp0=qp and qc0=qc
           so this is just reflexivity *)
        admit.
      }
      [unfold_case]: {
        unfold implies_case_AxIH; intros.
      }
      [and_case]: {

      }
      [forall_case]: {
        clear qp qc H H0.
        clear f2 f0 f1.
        clear V _v.
        
      }
    }
  }



  (* cbv in H1. *)

  (* specialize H1 with (infs :=
    λ p c,
      ∀ (qp qc : ∀ V, Class (FCWithNVars n) V → V),
        MQInd qp p -> MQInd qc c ->
        infs axioms (f_implies (qp V _v) (qc V _v))).
        
          : IH [qp -> qc] (λ _ _ infs, infs p c). *)
Qed.

End IC_implements_inference.

Lemma IC_implements_inference_universal :
  ∀ (axioms : ∀ {V} {_:Class FormulaConstructors V}, V)
    (Axioms : ∀ {T} {_:Class FormulaConstructors T}, InfSet T -> Prop),
    FormulaMeans
      (MQC := FcMQC)
      (@axioms)
      (@Axioms) -> 
    ∀ (p : ∀ {V} {_:Class FormulaConstructors V}, V)
      (P : ∀ {T} {_:Class FormulaConstructors T}, InfSet T -> Prop),
      FormulaMeans
        (MQC := FcMQC)
        (@p)
        (@P) ->

      (∀ {T} {_t:Class FormulaConstructors T} (infs : InfSet T),
        Axioms infs -> P infs)
        ->
        (* <-> *)
      ∀ {T} {_t:Class FormulaConstructors T},
        IC_provable_infs _ axioms p
        (* cheat *)
        .
  intros.
  
  refine ((fix recurse 
    
    Ext (assumed1 : @Meanings Ext) assumed2 a1_a2 f F mf
      {struct mf}
      : FormulaMeans (MQC:=MQC) f F
    := match mf
        in FormulaMeans _ f F
        return FormulaMeans assumed2 f F
        with
    | mi_assumed a A aAassumed => _
    | mi_implies qp p qc c x y => _
    | mi_unfold a b B unf bBimp => _
    | mi_and a A b B aAimp bBimp => _
    | mi_forall_valid_propositions f F fxFXimp => _
    | mi_forall_quoted_formulas f F fxFXimp => _
    end) Ext assumed1 assumed2 a1_a2 f F mf);
      [refine ?[assumed] | refine ?[implies] |
        refine ?[unfold] | refine ?[and] |
        refine ?[forall_prop] | refine ?[forall_quote]];
      clear assumed3 assumed4 f0 F0 a1_a3 mf0.
  refine
  induction H0. ; [admit | admit | admit | admit | admit |].

  unfold IC_provable_infs, infs_provable_from. intros.
  5: {
  }
Qed.

(****************************************************











                  Obsolete code











****************************************************)

Notation "[ x y .. z ]" := (apply .. (apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const {Ext} := @f_atm Ext atom_const.
Definition fuse {Ext} := @f_atm Ext atom_fuse.
Definition f_implies {Ext} := @f_atm Ext atom_implies.
Definition f_and {Ext} := @f_atm Ext atom_and.
Definition f_forall_valid_propositions {Ext} := @f_atm Ext atom_forall_valid_propositions.
Definition f_forall_quoted_formulas {Ext} := @f_atm Ext atom_forall_quoted_formulas.
Definition f_quote {Ext} := @f_atm Ext atom_quote.
Definition f_id {Ext} : Formula Ext := [fuse const const].
(* Definition f_extra e := f_atm (atom_extra e). *)
Definition f_pair [Ext] a b : Formula Ext := [fuse [fuse f_id [const a]] [const b]].
Definition fp_fst {Ext} : Formula Ext := [fuse f_id [const const]].
Definition fp_snd {Ext} : Formula Ext := [fuse f_id [const f_id]].
Definition f_default {Ext} : Formula Ext := const.

Notation "[ x & y ]" := [f_and x y]
  (at level 0, x at next level, y at next level).
(* Notation "[ x &* y ]" := [fuse [fuse [const [f_quote [f_quote f_and]]] x] y] (at level 0, x at next level, y at next level). *)
Notation "[ x -> y ]" := [f_implies x y] (at level 0, x at next level, y at next level).

(* Notation "[ x & y & .. & z ]" :=
  (apply (apply f_and x) .. (apply (apply f_and y) z) ..)
  (at level 0, x at next level, y at next level).
Definition foo := [f_const & f_const & f_const]. *)

(* subset notation is used for InfSets (which are 2-way relations) *)
Notation "R ⊆ S" := (∀ x, R x -> S x) (at level 70).
Notation "R ⊆2 S" := (∀ x y, R x y -> S x y) (at level 70).
Notation "R ⊇ S" := (∀ x, S x -> R x) (at level 70).
Notation "R ⊇2 S" := (∀ x y, S x y -> R x y) (at level 70).
Notation "R <->2 S" := (∀ x y, S x y <-> R x y) (at level 70).
Notation "R ∧1 S" := (λ x, R x ∧ S x) (at level 70).
Notation "R ∧3 S" := (λ x y z, R x y z ∧ S x y z) (at level 70).
Notation "R ∪ S" := (λ x, R x \/ S x) (at level 70).
Notation "R ∪2 S" := (λ x y, R x y \/ S x y) (at level 70).
(* Notation "⋃ S" := (λ x, ∃ T, S T /\ T x) (at level 70).
Notation "⋂ S" := (λ x, ∀ T, S T -> T x) (at level 70).
Notation "⋃2 S" := (λ x y, ∃ T, S T /\ T x y) (at level 70).
Notation "⋂2 S" := (λ x y, ∀ T, S T -> T x y) (at level 70). *)
(* Notation "⋀ S" := (λ x, ∀ T, (S T) x) (at level 70). *)
Notation "∅" := (λ x, False) (at level 70).
Notation "∅2" := (λ x y, False) (at level 70).
Definition Singleton A (a:A) := λ x, x = a.
Definition Singleton2 A B (a:A) (b:B) := λ x y, x = a /\ y = b.
(* Inductive Singleton2 A B (a:A) (b:B) : A -> B -> Prop :=
  | singleton2_cons x y : Singleton2 a b x y. *)

Definition StandardFormula := Formula False.

Definition InfSet F := F -> F -> Prop.

Definition Rule F := ∀ G, (F -> G) -> InfSet G -> Prop.

Definition Meanings {EExt} J :=
  (Formula EExt) -> Rule J -> Prop.

Inductive UnfoldStep [Ext] : (Formula Ext) -> (Formula Ext) -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c].
(* 
Definition QuotedJudgment qf := StandardFormula -> Prop *)


Fixpoint embed_formula
  Ext1 Ext2 (embed : Ext1 -> Ext2)
  (f : (Formula Ext1)) : (Formula Ext2)
  := match f with
    | f_atm a => f_atm a
    | f_ext a => f_ext (embed a)
    | apply a b => [(embed_formula embed a) (embed_formula embed b)]
    end.

Inductive FormulaMeans [EExt] [J]
  (MeansQuoted : (Formula EExt) -> J -> Prop)
  : @Meanings EExt J :=
  | mi_implies qp p qc c :
      MeansQuoted qp p -> MeansQuoted qc c -> 
      FormulaMeans MeansQuoted [qp -> qc] (λ J2 e infs,
        infs (e p) (e c))
  | mi_unfold a b B :
      UnfoldStep a b ->
      FormulaMeans MeansQuoted b B ->
      FormulaMeans MeansQuoted a B
  | mi_and a A b B :
      FormulaMeans MeansQuoted a A ->
      FormulaMeans MeansQuoted b B ->
      FormulaMeans MeansQuoted [a & b] (A ∧3 B)
  (* | mi_forall_quoted_formulas f 
    (F : ∀ J2, (J -> J2) -> J2 -> Rule J2) :
    (∀ EExt2 J2 qx x e_embed j_embed
        (MQ : (Formula EExt2) -> J2 -> Prop),
      (∀ e i, MeansQuoted e i -> MQ (e_embed e) (j_embed i)) ->
      MQ qx x -> 
      FormulaMeans MQ [(e_embed f) qx] (F J2 j_embed x)
    ) -> 
    FormulaMeans
      MeansQuoted
      [f_forall_quoted_formulas f]
      (λ J2 e infs,
        ∀ J3
          (e13 : (J -> J3))
          (e32 : (J3 -> J2))
          (compat : ∀ j, e32 (e13 j) = e j)
          x,
          (F J3 e13 x)
          J2 e32 (λ p c, infs p c)). *)
  | mi_forall_quoted_formulas f 
    (F : ∀ J2, (J -> J2) -> J2 -> InfSet J2 -> Prop) :
    (∀ EExt2 J2 qx x e_embed j_embed
        (MQ : (Formula EExt2) -> J2 -> Prop),
      (∀ e i, MeansQuoted e i -> MQ (e_embed e) (j_embed i)) ->
      MQ qx x -> 
      FormulaMeans MQ [(e_embed f) qx] (λ J3 e infs,
        (F J3 (λ v, e (j_embed v)) (e x) infs))
    ) -> 
    FormulaMeans
      MeansQuoted
      [f_forall_quoted_formulas f]
      (λ J2 e infs,
        ∀ x, F J2 e x infs).


(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
Definition MetaInferences
  J
  (KnownRules : Rule J)
  (p c : StandardFormula) : Prop :=
  ∀ P, FormulaMeans (∅2) p P -> 
    ∃ C, FormulaMeans (∅2) c C ∧
      ∀ J2 (e : J -> J2) infs,
        KnownRules J2 e infs -> P J2 e infs -> C J2 e infs.

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
Fixpoint KnownInferences n : InfSet StandardFormula :=
  match n with
    | 0 => ∅2
    | S pred => MetaInferences
      (λ J2 e infs, ∀ p c, KnownInferences pred p c -> infs (e p) (e c))
    end.






  





(* Fixpoint unfold_until (t : Type) n
  (body : (Formula -> GetResult t) -> Formula -> GetResult t)
  : (Formula -> GetResult t) :=
  match n with
    | 0 => timed_out _
    | S pred => body (unfold_until pred body) f
    end.
Notation "'unfold_or' body" :=
  (match n with
    | 0 => timed_out _ | S pred => body end) (at level 40). *)


Print FormulaMeans.
(* Definition Meaning : Meanings := FormulaMeans (∅2). *)

Inductive OneMoreExt {OldExt} :=
  | ome_embed : OldExt -> OneMoreExt
  | ome_new : OneMoreExt.

Fixpoint embed_onemore OldExt
  (f : Formula OldExt)
  : Formula (@OneMoreExt OldExt) :=
  match f with
    | fo_apl a b => [(embed_onemore a) (embed_onemore b)] 
    | f_atm a => f_atm a
    | f_ext a => f_ext (ome_embed a)
    end.


Fixpoint specialize_onemore OldExt
  (f : Formula (@OneMoreExt OldExt))
  (x : Formula OldExt)
  : Formula OldExt :=
  match f with
    | fo_apl a b => [(specialize_onemore a x) (specialize_onemore b x)] 
    | f_atm a => f_atm a
    | f_ext a => match a with
        | ome_embed a => f_ext a
        | ome_new => x
      end
    end.

Lemma specialize_embed [OldExt] (f: Formula OldExt) x :
  specialize_onemore (embed_onemore f) x = f.
  induction f; cbn; [| |rewrite IHf1; rewrite IHf2]; reflexivity.
Qed.

(* Inductive UnreifiedAssumed [Ext]
  (propvars : Ext -> Prop)
  (pv_meanings : ∀ e, propvars e -> Rule)
  : Meanings :=
  | unreified_assumed e (ae : propvars e) :
  UnreifiedAssumed propvars pv_meanings
    (f_ext e) (pv_meanings e ae). *)
        
(* Definition MiSearchSuccess [Ext]
    (quotvars : Ext -> Prop)
    (propvars : Ext -> Prop)
    (f : Formula Ext) : Type :=
    ∀ (qv_meanings : ∀ e, quotvars e -> StandardFormula)
      (pv_meanings : ∀ e, propvars e -> Rule),
    {F | FormulaMeans
      (UnreifiedAssumed propvars pv_meanings)
      f F}. *)

(* Definition embed_assumed 
    [OldExt]
    (assumed_meanings : @Meanings OldExt)
    : @Meanings (@OneMoreExt OldExt) :=
  λ f F, (∃ fp, f = embed_onemore fp /\ assumed_meanings fp F). *)

(* Definition assume_one_more
    [OldExt]
    (assumed_meanings : @Meanings OldExt)
    (new_meaning : Rule)
    : @Meanings (@OneMoreExt OldExt) :=
  (embed_assumed assumed_meanings) ∪2 (Singleton2 (f_ext (ome_new)) new_meaning). *)

(* Definition one_more_var
    [OldExt]
    (vars : OldExt -> Prop)
    : (@OneMoreExt OldExt) -> Prop :=
  λ a, match a with
    | ome_embed a => vars a
    | ome_new => True 
    end.
Definition embed_vars
    [OldExt]
    (vars : OldExt -> Prop)
    : (@OneMoreExt OldExt) -> Prop :=
  λ a, match a with
    | ome_embed a => vars a
    | ome_new => False
    end.
Definition embed_revars
    [OldExt]
    (vars : OldExt -> bool)
    : (@OneMoreExt OldExt) -> bool :=
  λ a, match a with
    | ome_embed a => vars a
    | ome_new => false
    end.

Definition one_more_var_meaning
    [OldExt]
    [VarType]
    (vars : OldExt -> Prop)
    (meanings : ∀ e, vars e -> VarType)
    (new_meaning : VarType)
    : (∀ e, (one_more_var vars) e -> VarType) :=
  λ e, match e return (one_more_var vars) e -> VarType with
    | ome_embed a => meanings a
    | ome_new => λ _, new_meaning
    end.
Definition embed_var_meanings
    [OldExt]
    [VarType]
    (vars : OldExt -> Prop)
    (meanings : ∀ e, vars e -> VarType)
    : (∀ e, (embed_vars vars) e -> VarType) :=
  λ e, match e return (embed_vars vars) e -> VarType with
    | ome_embed a => meanings a
    | ome_new => λ f, match f with end
    end. *)



(* Lemma mi_monotonic [Ext]
  (assumed1 : @Meanings Ext)
  (assumed2 : @Meanings Ext)
  : (assumed1 ⊆2 assumed2) ->
  (FormulaMeans assumed1 ⊆2 FormulaMeans assumed2).
  intros a1_a2 f F mf.

  refine ((fix recurse 
    Ext (assumed1 : @Meanings Ext) assumed2 a1_a2 f F mf
      {struct mf}
      : FormulaMeans assumed2 f F
    := match mf
        in FormulaMeans _ f F
        return FormulaMeans assumed2 f F
        with
    | mi_assumed a A aAassumed => _
    | mi_implies qp p qc c x y => _
    | mi_unfold a b B unf bBimp => _
    | mi_and a A b B aAimp bBimp => _
    | mi_forall_valid_propositions f F fxFXimp => _
    | mi_forall_quoted_formulas f F fxFXimp => _
    end) Ext assumed1 assumed2 a1_a2 f F mf);
      [refine ?[assumed] | refine ?[implies] |
        refine ?[unfold] | refine ?[and] |
        refine ?[forall_prop] | refine ?[forall_quote]];
      clear assumed3 assumed4 f0 F0 a1_a3 mf0.

  [assumed]: { apply mi_assumed. apply a1_a2; assumption. }
  [implies]: { apply mi_implies; assumption. }
  [unfold]: {
    apply mi_unfold with b.
    assumption. apply recurse with assumed1; assumption.
  }
  [and]: {
    apply mi_and; apply recurse with assumed1; assumption.
  }
  [forall_prop]: {
    apply mi_forall_valid_propositions.
    intros.
    specialize (fxFXimp x X).
    apply recurse with (assumed1 ∪2 Singleton2 x X).
    intuition. assumption.
  }
  [forall_quote]: {
    apply mi_forall_quoted_formulas.
    intros.
    specialize (fxFXimp x qx H).
    apply recurse with assumed1; assumption.
  }
Qed. *)
    
  

(* Lemma specialize_FormulaMeans [OldExt] 
    (assumed_meanings : @Meanings OldExt) f F x X :
  FormulaMeans (assume_one_more assumed_meanings X) f F ->
  FormulaMeans assumed_meanings x X ->
  FormulaMeans assumed_meanings (specialize_onemore f x) F.

  intros.

  refine ((fix recurse 
    OldExt (assumed_meanings : @Meanings OldExt) f F x X mf mx
      : FormulaMeans assumed_meanings
        (specialize_onemore f x) F
    := match mf
        in FormulaMeans _ f F
        return FormulaMeans assumed_meanings
    (specialize_onemore f x) F
        with
    | mi_assumed a A aAassumed => _
    | mi_implies qp p qc c x y => _
    | mi_unfold a b B unf bBimp => _
    | mi_and a A b B aAimp bBimp => _
    | mi_forall_valid_propositions f F fxFXimp => _
    | mi_forall_quoted_formulas f F fxFXimp => _
    end) OldExt assumed_meanings f F x X H H0);
      [refine ?[assumed] | refine ?[implies] |
        refine ?[unfold] | refine ?[and] |
        refine ?[forall_prop] | refine ?[forall_quote]];
      clear OldExt0 assumed_meanings0 f0 F0 x0 X0 H H0 mf.

  [assumed] : {
    dependent destruction aAassumed. destruct H.
    
    destruct H. rewrite H.
    rewrite (specialize_embed x0 x).
    apply mi_assumed; assumption.
    
    destruct H. rewrite H. rewrite H0. cbn. assumption.
  }

  [implies] : {
    (* TODO: "quoted formulas should still work because they can't have f_ext in them?" *)
    admit.
  }

  [unfold] : {
    apply mi_unfold with (specialize_onemore b x).

    (* TODO: unfold-specialize lemma *)
    admit.

    apply recurse with X; assumption.
  }

  [and] : {
    apply mi_and; apply recurse with X; assumption.
  }

  [forall_prop] : {
    apply mi_forall_valid_propositions.
    intros y Y.
    specialize (fxFXimp (embed_onemore y) Y).
    specialize (recurse
      OldExt
      (assumed_meanings ∪2 Singleton2 y Y)
      ([f (embed_onemore y)])
      (F Y)
      x
      X
   ).
  assert ([(specialize_onemore f x) y] =
    (specialize_onemore [f (embed_onemore y)] x)).
    cbn.
    rewrite (specialize_embed y x). reflexivity.
    rewrite <- H in recurse.
    apply recurse.
    apply mi_monotonic with  (assume_one_more assumed_meanings X
∪2 Singleton2 (embed_onemore
  y)
  Y); [|assumption].
  intuition idtac; unfold assume_one_more, embed_assumed in *; cbn in *;intuition idtac.
  apply or_introl. destruct H0. apply ex_intro with x1; intuition idtac.
  destruct H1. rewrite H0. rewrite H1.
  apply or_introl. apply ex_intro with y. intuition idtac. apply or_intror. unfold Singleton2. intuition idtac.
  apply mi_monotonic with assumed_meanings; [| assumption].
  intuition idtac.
  }

  [forall_quote] : {
    apply mi_forall_quoted_formulas.
    intros y qy qqy.
    destruct (qf_convert (Ext2:=(@OneMoreExt OldExt)) qqy) as [qy_ qqy_].
    specialize (fxFXimp y qy_ qqy_).
    specialize (recurse
      OldExt
      assumed_meanings
      ([f qy_])
      (F y)
      x
      X
   ).
  assert ([(specialize_onemore f x) qy] =
    (specialize_onemore [f qy_] x)).
    cbn.
    (* TODO: quoted version of the same formula are basically the same *)
    admit.
    rewrite <- H in recurse.
    apply recurse; assumption.
  }
Qed. *)
  

(* Definition specialize_MiSearchSuccess_prop
    [OldExt] f
    (quotvars : OldExt -> Prop)
    (propvars : OldExt -> Prop)
    (x : Formula OldExt)
    (X : Rule)
    (xXimp : ∀ pv_meanings, FormulaMeans (UnreifiedAssumed
  propvars pv_meanings) x X)
    (missss : MiSearchSuccess
      (embed_vars quotvars) (one_more_var propvars)
      f)
    :
    (MiSearchSuccess quotvars propvars
      (specialize_onemore f x)).
  refine (
    λ qv_meanings pv_meanings,
       match (missss
         (embed_var_meanings quotvars qv_meanings)
         (one_more_var_meaning propvars pv_meanings X)
         ) with
       exist F p => 
        exist _ F _ end).
  
  apply specialize_FormulaMeans with X.
  apply mi_monotonic with (UnreifiedAssumed
  (one_more_var propvars)
  (one_more_var_meaning propvars
  pv_meanings X)).
  intros.
  destruct H.
  unfold assume_one_more, embed_assumed.
  destruct e.
  apply or_introl. apply ex_intro with (f_ext o). constructor.
  reflexivity.
  constructor. apply or_intror. constructor; trivial.
  assumption.
  apply xXimp.
Qed. *)



Definition one_more_revar
    [OldExt]
    (vars : OldExt -> bool)
    : (@OneMoreExt OldExt) -> bool :=
  λ a, match a with
    | ome_embed a => vars a
    | ome_new => true 
    end.

(* Definition embed_revar_meanings
    [OldExt]
    [VarType]
    (vars : OldExt -> bool)
    (meanings : ∀ e, (unreify_vars vars e) -> VarType)
    : (∀ e, (unreify_vars (embed_revars vars)) e -> VarType) :=
  λ e, match e with
    | ome_embed a => meanings a
    | ome_new => λ f, match f with end
    end. *)

Definition revar_meanings [Ext] (vars : Ext -> bool) J :=
  ∀ J2 v, (J -> J2) -> (unreify_vars vars v) -> Rule J2.

Definition embed_revar_meanings [Ext] J J2 (vars : Ext -> bool)
    (e12 : (J -> J2))
    (meanings : revar_meanings vars J)
    : revar_meanings vars J2 :=
   λ J3 v e23,
     meanings J3 v (λ x, (e23 (e12 x))).

Definition embed_rule J J2 (e12 : J -> J2) (rule : Rule J) : Rule J2 :=
  λ J3 e23 infs,
    rule J3 (λ x, (e23 (e12 x))) infs.

Definition one_more_revar_meaning
    [OldExt] J
    (vars : OldExt -> bool)
    (meanings : revar_meanings vars J)
    (new_meaning : Rule J)
    : revar_meanings (one_more_revar vars) J :=
  λ J2 v e, match v return
      (unreify_vars (one_more_revar vars) v)
        -> Rule J2 with
    | ome_embed a => λ ve, meanings J2 a e ve
    | ome_new => λ _, embed_rule e new_meaning
    end.

Definition revar_meanings2 [OldExt] (vars : OldExt -> bool) J :=
  ∀ v, (unreify_vars vars v) -> J.
Definition one_more_revar_meaning2
    [OldExt] J
    (vars : OldExt -> bool)
    (meanings : revar_meanings2 vars J)
    (new_meaning : J)
    : revar_meanings2 (one_more_revar vars) J :=
  λ v, match v return
      (unreify_vars (one_more_revar vars) v)
        -> J with
    | ome_embed a => λ ve, meanings a ve
    | ome_new => λ _, new_meaning
    end.



(* Fixpoint get_MeansQuoted [Ext] n qf
  : GetResult {f : StandardFormula | MeansQuoted qf f} :=
  match n with 0 => timed_out _ | S pred =>
    match unfold_step qf with
      | Some (exist qg u) =>
          ? (exist g gp) <- get_MeansQuoted pred qg ;
          success (exist _ g (quoted_unfold u gp))
      | None => match qf with
          | apply (f_atm atom_quote) (f_atm a) =>
              success (exist _ (f_atm a) (quoted_atom a))
          | apply (apply (f_atm atom_quote) qa) qb =>
            ? (exist a ap) <- get_MeansQuoted pred qa ; 
            ? (exist b bp) <- get_MeansQuoted pred qb ;
            success (exist _ [a b] (quoted_apply (Ext:=Ext) ap bp))
          | _ => error _
          end
      end
  end. *)

Inductive MPSearchResult [Ext]
    (vars : Ext -> bool)
    : Formula Ext -> Type :=
  | msr_implies qp p qc c :
      MeansQuoted qp p -> MeansQuoted qc c -> 
      MPSearchResult vars [qp -> qc]
  | msr_and a b :
      MPSearchResult vars a ->
      MPSearchResult vars b ->
      MPSearchResult vars [a & b]
  | msr_forall_quoted_formulas f :
    MPSearchResult (one_more_revar vars)
      [(embed_formula ome_embed f) (f_ext ome_new)] ->
    MPSearchResult vars [f_forall_quoted_formulas f].

Fixpoint msr_specialize [Ext]
  (vars : Ext -> bool)
  p
  (r : MPSearchResult (one_more_revar vars) p)
  J e x
  : MPSearchResult vars (specialize_onemore p x) :=
  match r
      in MPSearchResult _ p0
      return MPSearchResult vars (specialize_onemore p0 x) with
  | msr_implies qp p qc c qpp qcc => _
  | msr_and a b ra rb => msr_and
      (msr_specialize ra J e x)
      (msr_specialize rb J e x)
  | msr_forall_quoted_formulas f rfx =>
      msr_forall_quoted_formulas
        f
        (msr_specialize rfx J e (embed_onemore x))
    end.


Fixpoint msr_finish (r : MPSearchResult vars) : Rule.


  



(* Definition get_FormulaMeans (n:nat) [Ext]
  (f : Formula Ext)
  (quotvars : Ext -> bool)
  (propvars : Ext -> bool)
  : GetResult (MiSearchSuccess
    (unreify_vars quotvars) (unreify_vars propvars) f).
  refine ((fix get_FormulaMeans Ext
    n f quotvars propvars :=
    match n with 0 => timed_out _ | S pred => _ end) Ext n f quotvars propvars)
    ; clear Ext0 n0 f0 quotvars0 propvars0.
  specialize get_FormulaMeans with (n := pred).
  
  (* pose (λ pv_meanings, (UnreifiedAssumed (unreify_vars propvars) pv_meanings)) as assumed_meanings. *)

  destruct (unfold_step f) as [(g, unf)|].
  {
    refine (? GS <- get_FormulaMeans Ext g quotvars propvars ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct (GS qv_meanings pv_meanings) as (G, Gp).
    apply (exist _ G (mi_unfold unf Gp)).
  }

  refine (match f with
          | f_ext a => _
          | apply (f_atm atom_forall_valid_propositions) f => _
          | apply (f_atm atom_forall_quoted_formulas) f => _
          | apply (apply (f_atm atom_implies) qp) qc => _
          | apply (apply (f_atm atom_and) a) b => _
          | _ => error _
          end);
      [refine ?[assumed] |
        refine ?[forall_prop] | refine ?[forall_quote] |
        refine ?[implies] | refine ?[and]].
  
  [assumed]: {
    refine (match propvars a with
              | true => success (λ qv_meanings pv_meanings, _)
              | false => error _
              end).

    (* TODO: sigh, Coq forgot that we're
       in the (propvars a)=true case *)
    assert (unreify_vars propvars a) as pa; [admit|].

    apply exist with (pv_meanings a pa).
    apply mi_assumed.
    apply unreified_assumed.
  }

  [forall_prop]: {
    refine (? FXS <- (get_FormulaMeans (@OneMoreExt Ext)
      [(embed_formula (λ a, ome_embed a) f) (f_ext ome_new)]
      (embed_revars quotvars)
      (one_more_revar propvars)) ; _).
    apply success; intros qv_meanings pv_meanings.
    refine (exist _ (λ p c, ∃ X : Rule, (_ X) p c) _).
    Unshelve. 2: {
      (* TODO reduce duplicate code ID 23489305 *)
      pose (unreify_embed2 (embed_var_meanings
        (unreify_vars quotvars) qv_meanings)) as qv_meanings1.
      pose (unreify_onemore2 (one_more_var_meaning
        (unreify_vars propvars) pv_meanings X)) as pv_meanings1.
      destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
      (* End duplicate code *)
      exact (λ _, FX).
    }

    apply mi_forall_valid_propositions.
    intros.

    (* TODO reduce duplicate code ID 23489305 *)
    pose (unreify_embed2 (embed_var_meanings
      (unreify_vars quotvars) qv_meanings)) as qv_meanings1.
    pose (unreify_onemore2 (one_more_var_meaning
      (unreify_vars propvars) pv_meanings X)) as pv_meanings1.
    destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
    (* End duplicate code *)
    admit.
    (* pose (@specialize_FormulaMeans
      Ext
      (assumed_meanings pv_meanings)
      [(embed_formula ome_embed f) (f_ext ome_new)]
      FX
      x
      X
      ) as m.
    apply mi_monotonic with (assumed2 := assume_one_more
  (assumed_meanings
  pv_meanings)
  X) in FXp. 2: {
      clear m.
      intros. destruct H. unfold assume_one_more. cbn.
      dependent destruction e.
      apply or_introl. unfold unreify_vars in ae.
      cbn.
      apply ex_intro with (f_ext e).
      constructor; [reflexivity|].
      (* unfold meanings1  .  *)
      admit.
      apply or_intror.
      admit.
    }
    specialize (m FXp). *)
  }

  [forall_quote]: {
    refine (? FXS <- (get_FormulaMeans (@OneMoreExt Ext)
      [(embed_formula (λ a, ome_embed a) f) (f_ext ome_new)]
      (one_more_revar quotvars)
      (embed_revars propvars)) ; _).
    apply success; intros qv_meanings pv_meanings.
    refine (exist _ (λ p c, ∃ x : StandardFormula, (_ x) p c) _).

    Unshelve. 2: {
      (* TODO reduce duplicate code ID 23489305 *)
      pose (unreify_embed2 (embed_var_meanings
        (unreify_vars propvars) pv_meanings)) as pv_meanings1.
      pose (unreify_onemore2 (one_more_var_meaning
        (unreify_vars quotvars) qv_meanings x)) as qv_meanings1.
      destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
      (* End duplicate code *)
      exact (λ _, FX).
    }

    admit.
  }

  [implies]: {
    refine (? PQ <- (get_MeansQuoted pred qp) ; _).
    refine (? CQ <- (get_MeansQuoted pred qc) ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct PQ as (p, qqp).
    destruct CQ as (c, qqc).
    apply exist with (Singleton2 p c).
    apply mi_implies; assumption.
  }

  [and]: {
    refine (? AS <- (get_FormulaMeans Ext a quotvars propvars) ; _).
    refine (? BS <- (get_FormulaMeans Ext b quotvars propvars) ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct (AS qv_meanings pv_meanings) as (A, Ap).
    destruct (BS qv_meanings pv_meanings) as (B, Bp).
    apply exist with (A ∪2 B).
    apply mi_and; assumption.
  }
Defined. *)

(* Eval lazy in 2 + 2.
Eval lazy in get_FormulaMeans (Ext := False) 0 [[f_quote f_quote] -> [f_quote f_quote]] 
  (λ _, false) (λ _, false)
  .
Lemma uhh : False.
  pose (get_FormulaMeans (Ext := False) 0 [[f_quote f_quote] -> [f_quote f_quote]] 
  (λ _, false) (λ _, false)) as x.
  cbn in x.
  unfold get_FormulaMeans in x.
Qed. *)

Fixpoint NMoreAtoms [Ext] n :=
  match n with
    | 0 => Ext
    | S n => @OneMoreExt (@NMoreAtoms Ext n)
    end.

Fixpoint last_more_atom [Ext] n : (@NMoreAtoms Ext (S n)) :=
  match n with
    | 0 => ome_new
    | S n => ome_embed (@last_more_atom Ext n)
    end.
  





Lemma uhh2 :
  success (λ p c, ∃ X : Rule, X p c)
  =
  (with_no_meanings (get_prop_meaning 90 test05 no_vars no_vars)).
  cbn.
  assert (∀ X : Rule, X = unreify_onemore2
  (one_more_var_meaning
  (unreify_vars no_vars)
  (no_meanings Rule) X)
  eq_refl).
  cbv.
Qed.


(* Definition test1 : StandardFormula :=
  (eliminate_abstraction (f_with_variable (λ a, [a -> a]))). *)
Definition test1 : StandardFormula :=
  [∀a, [a -> a]].
Eval compute in display_f test1.
Eval compute in (get_prop_meaning_simplified 90 test1).

Definition test2 : StandardFormula :=
  [∀a, [∀b, [(a@1) -> b]]].
Eval compute in display_f test2.
Eval lazy in (get_prop_meaning_simplified 90 test2).
Definition test3 : StandardFormula :=
  [∀a, [(quote_f [a const]) -> a]].
Eval compute in display_f test3.
Eval lazy in (get_prop_meaning_simplified 90 test3).

(* 
  (λ (_ : False → true = false → Formula)
     (_ : False → true = false → Rule)
     (p c : Formula),
     ∃ x : Formula, p = x ∧ c = x)
 *)



Definition f_false : StandardFormula := [∀p, p].


(* Definition IC_introspective :=
  ∀ p c, IC_provable_infs p c -> IC_provable_props [p -> c]. *)

Lemma IC_implements_inference_universal :
  ∀ axioms Axioms, FormulaMeans (∅2) axioms Axioms ->
    ∀ p P, FormulaMeans (∅2) p P ->
      P (infs_provable_from (Axioms ∧1 transitivity))
      -> (* <-> *)
      IC_provable_infs axioms p.
  intros.
  induction H0; [admit | admit | admit | admit | admit |].

  unfold IC_provable_infs, infs_provable_from. intros.
  5: {
  }
Qed.

Definition IC_implements_inference :=
  ∀ axioms Axioms, FormulaMeans (∅2) axioms Axioms ->
    ∀ qp p qc c, MeansQuoted qp p -> MeansQuoted qc c ->
      infs_provable_from (Axioms ∧1 transitivity) p c
      <->
      IC_provable_infs axioms [qp -> qc].

Definition IC_self_describing :=
  ∀ p, IC_provable_props p ->
    ∃ P, FormulaMeans (∅2) p P ∧ P IC_provable_infs.

Definition IC_introspective :=
  ∀ p P, FormulaMeans (∅2) p P ∧ P IC_provable_infs    
    -> IC_provable_props p.

Definition IC_consistent :=
  ¬ IC_provable_props f_false.

(* [(forall_n) p] should mean
  "put a stream of n qfs into p and it'll be true" *)
Fixpoint forall_n n :=
  match n with
    | 0 => f_id
    | S pred => [p => [(forall_n pred) [l => [∀x, [p (f_pair x l)]]]]]
    end.

Definition and_sym : StandardFormula :=
  [(forall_n 2) [[@0 & @1] -> [@1 & @0]]].

Eval lazy in (get_prop_meaning_simplified 90 and_sym).

(* Definition TrueOf2 Infs f : Prop :=
  InfsAssertedBy f ⊆2 Infs.

Definition FormulasTrueAbout Infs f : Prop :=
  InfsAssertedBy f ⊆2 Infs. *)

(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
Definition RequiredMetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  (* ∀ p c,
    InfsAssertedBy b p c ->
    (InfsAssertedBy a p c \/ KnownJudgedInferences p c). *)
  ∃ A B,
    InfsAssertedBy a A /\ InfsAssertedBy b B /\
    B ⊆2 (A ∪2 KnownJudgedInferences).

Definition PermittedMetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  ∀ A B,
    InfsAssertedBy a A -> InfsAssertedBy b B ->
    B ⊆2 (A ∪2 KnownJudgedInferences).

(* (want to prove: True -> required -> IC -> permitted -/> False.
    by induction: (permitted -/> False)
    somehow: "all statements that describe IC are provable in IC"
    by induction using that: (required -> IC)
    by proofs for individual rules: (IC -> permitted)
    which yields "all provable IC statements describe IC" I think) *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
Fixpoint KnownRequiredInferences n : InfSet :=
  match n with
    | 0 => ∅2
    | S pred => RequiredMetaInferences (KnownRequiredInferences pred)
    end.

Fixpoint KnownPermittedInferences n : InfSet :=
  match n with
    | 0 => ∅2
    | S pred => PermittedMetaInferences (KnownPermittedInferences pred)
    end.

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
(* Fixpoint KnownInferences n : InfSet :=
  match n with
    | 0 => eq (* same as MetaInferences (λ _, False) *)
    | S pred => MetaInferences (KnownInferences pred)
    end. *)

Inductive FType :=
  | t_proposition : FType
  | t_quoted_formula : FType
  | t_function : FType -> FType -> FType.

(* Inductive FMember (t : FType) f : Prop :=
  | tm_proposition p : (InfsAssertedBy f <->2 p) -> FMember t f
  | tm_quoted_formula : True -> FMember t f
  | tm_function a b : (∀x, FMember a x -> FMember b [f x]) -> FMember t f.
  
 
Fixpoint FMember t f : Prop := match t with
  | t_proposition => ∃ p, (InfsAssertedBy f <->2 p) -> FMember t f
  | t_quoted_formula => True
  | t_function a b => ∀x, FMember a x -> FMember b [f x]
  end. *)

Parameter FMember : FType -> Formula -> Prop.

Inductive interpret_result t f :=
  | is_member : FMember t f -> interpret_result t f
  | timed_out : interpret_result t f
  | error : string -> interpret_result t f.

Notation "x <- m1 ; m2" :=
  (match m1 with
    | is_member x => m2
    | timed_out => timed_out
    | error s => error s
    end) (right associativity, at level 70).
(* Notation "x :? t ; m2" :=
  (x <- recurse t x ; m2) (right associativity, at level 70). *)

Definition interpret_as_prop recurse f :=
  match f with
    | apply (apply f_implies p) c => 
      p <- recurse t_quoted_formula p ;
      c <- recurse t_quoted_formula c ;
      is_member t_proposition (λ x y, (x = p) /\ (y = c))
    | apply (apply f_and a) b => 
      a <- recurse t_proposition a ;
      b <- recurse t_proposition b ;
      is_member t_proposition (a ∪2 b)
    | apply (f_all) a =>
      a <- recurse (t_function t_quoted_formula t_proposition) a ;
      is_member t_proposition (∀x, a x)
    | _ => error
  end. 
Definition interpret_as_fn recurse f :=
  match f with
  
  | _ => error
  end. 
  
    (* | _ => match
        unfold_step b
        with
      | Some b => CleanExternalMeaning pred b
      | _ => None
      end
    end *)
  

Fixpoint interpret_as n t f :=
  match n with 0 => timed_out | S pred =>
    end.


Fixpoint CleanExternalMeaning n f quoted_args : option InfSet :=
  match n with
    | 0 => None
    | S pred => match f with
      | apply (apply f_implies p) c => match (
          unquote_formula p,
          unquote_formula c
          ) with
        | (Some p, Some c) => λ x y, x = p /\ y = c
        | _ => None
      end
      | apply (apply f_and a) b => match (
          CleanExternalMeaning pred a,
          CleanExternalMeaning pred b
          ) with
        | (Some a, Some b) => Some (a ∪2 b)
        | _ => None
      end
      | apply (f_all) a => match
          CleanExternalMeaning pred a
          with
        | Some a => Some (∀x, a ∪2 b)
        | _ => None
      end
      | _ => match
          unfold_step b
          with
        | Some b => CleanExternalMeaning pred b
        | _ => None
        end
      end
    end.


Inductive RulesProveInference Rules : Formula -> Formula -> Prop :=
  | proof_by_rule a b : Rules a b -> RulesProveInference Rules a b
  | proof_by_transitivity a b c :
    RulesProveInference Rules a b ->
    RulesProveInference Rules b c ->
    RulesProveInference Rules a c.
Definition InferencesProvenBy Rules : InfSet := RulesProveInference Rules.

(* Definition FormulaMeaning
    (Rules : InfSet)
    (UnknownMeanings : Formula -> Prop)
  : Formula -> Prop
  :=
    fix FormulaMeaning (f : Formula) :=
      match f with
        (* [and a b] *)
        | apply (apply (f_atm atom_and) a) b
          => FormulaMeaning a /\ FormulaMeaning b
        (* [pred_imp a b] *)
        | apply (apply (f_atm atom_pred_imp) a) b
          => (∀ x,
            IsMeansQuotedStream x -> ∃ ap bp,
              UnfoldsToMeansQuoted [a x] ap /\
              UnfoldsToMeansQuoted [b x] bp /\
              RulesProveInference Rules ap bp)
        | _ => UnknownMeanings f
        end. *)

(* Definition InfSetObeysInference Rules a b : Prop :=
  ∀UnknownMeanings,
    (FormulaMeaning Rules UnknownMeanings a) ->
    (FormulaMeaning Rules UnknownMeanings b).

Definition AllInfSetsObeyInference a b : Prop :=
  ∀Rules, InfSetObeysInference Rules a b. *)

(* Definition AllInfSetsObeyAllOf Rules : Prop :=
  ∀a b, Rules a b -> AllInfSetsObeyInference a b. *)

(* Definition InferencesTheseInfSetsObey These a b : Prop :=
  ∀Rules, These Rules -> InfSetObeysInference Rules a b. *)

(* Definition AllTheseInfSetsObeyAllOf These Rules : Prop :=
  ∀a b, Rules a b -> InferencesTheseInfSetsObey These a b. *)

(* Definition NoRules : InfSet := λ _ _, False. *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that are possible
  in all InfSets that include the last *)
(* Fixpoint KnownRequiredInferences n : InfSet :=
  match n with
    | 0 => eq
    | S pred => InferencesTheseInfSetsObey
      (λ Rules, (InferencesProvenBy Rules) ⊇2
        (KnownRequiredInferences pred))
    end. *)


Lemma CleanExternalMeaning_correct n f m :
  (CleanExternalMeaning n f = Some m) ->
  (m <->2 InfsAssertedBy f).

Lemma MetaInferences_closed_under_transitivity K p c :
    RulesProveInference (MetaInferences K) p c
    ->
    (MetaInferences K) p c.
  intro.
  induction H; [assumption|clear H H0].
  unfold MetaInferences in *.
  intros.
  specialize (IHRulesProveInference1 x y).
  specialize (IHRulesProveInference2 x y).
  destruct (IHRulesProveInference2 H); [|constructor; assumption].
  destruct (IHRulesProveInference1 H0); constructor; assumption.
Qed.

Lemma emptyset_closed_under_transitivity p c :
    RulesProveInference (∅2) p c
    ->
    ∅2 p c.
  intro. induction H; assumption.
Qed.

Lemma KnownInferences_closed_under_transitivity p c n :
    RulesProveInference (KnownInferences n) p c
    ->
    KnownInferences n p c.
    destruct n.
    apply emptyset_closed_under_transitivity.
    apply MetaInferences_closed_under_transitivity.
Qed.

Lemma proofs_monotonic_in_rules R1 R2 :
  (R1 ⊆2 R2) -> (InferencesProvenBy R1 ⊆2 InferencesProvenBy R2).
  intros. induction H.
  apply proof_by_rule. exact (X a b X0).
  apply proof_by_transitivity with b; assumption.
Qed.

Lemma provable_by_subset_of_KnownInferences_means_known n p c R :
    R ⊆2 KnownInferences n ->
    RulesProveInference R p c ->
    KnownInferences n p c.
  intros.
  exact (KnownInferences_closed_under_transitivity n
      (@proofs_monotonic_in_rules
        R (KnownInferences n) H p c H0)
    ).
Qed.

(* Lemma eq_justified These : AllTheseInfSetsObeyAllOf These eq.
  unfold AllTheseInfSetsObeyAllOf,
         InferencesTheseInfSetsObey,
         InfSetObeysInference.
  intros.
  subst b; assumption.
Qed. *)

(* Lemma provable_by_eq_means_eq p c :
  RulesProveInference eq p c -> p = c.
  intro.
  induction H; [assumption | ].
  subst b; assumption.
Qed. *)

Definition fs_pop_then handler :=
  [fuse [const handler] fp_snd].

Fixpoint fs_nth n := match n with
  | 0 => fp_fst
  | S p => fs_pop_then (fs_nth p)
  end.

Notation "@ n" := (fs_nth n) (at level 0).

(* Eval simpl in try_unfold_n 100 [fp_fst (f_pair f_quote f_quote)].
Eval simpl in unfold_step [@0 (qfs_cons const qfs_tail)].
Eval simpl in try_unfold_n 100 [@0 (qfs_cons const qfs_tail)]. *)

Lemma quoted_no_unfold f : unfold_step (quote_f f) = None.
  induction f; cbn.
  reflexivity.
  rewrite IHf1. rewrite IHf2. cbn. reflexivity.
Qed.

Lemma quoted_unfold_to_quoted a :
  try_unfold_to_quoted 1 (quote_f a) = Some a.
  induction a; cbn; [reflexivity|].
  rewrite (quoted_no_unfold a1).
  rewrite (quoted_no_unfold a2).
  rewrite (quote_unquote a1).
  rewrite (quote_unquote a2).
  cbn; reflexivity.
Qed.

Lemma ustep_fn_to_prop a b :
  (unfold_step a = Some (b)) -> UnfoldStep a b.
Qed.

Lemma utqf_fn_to_prop a b :
  UnfoldsToMeansQuotedByFn a b -> UnfoldsToMeansQuoted a b.
  intro.
  destruct H.
  unfold UnfoldsToMeansQuotedByFn.
  dependent induction x.
  cbn in H. dependent destruction H.
  cbn in H.
  destruct (unfold_step a).
  
  unfold try_unfold_to_quoted in H.
  unfold UnfoldsToMeansQuoted.
Qed.


  
Lemma pair_first_quoted_byfn a b :
  UnfoldsToMeansQuotedByFn [fp_fst (f_pair (quote_f a) b)] a.
  unfold UnfoldsToMeansQuotedByFn.
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.

  
Lemma pair_first_quoted a b :
  UnfoldsToMeansQuoted [fp_fst (f_pair (quote_f a) b)] a.
  
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_first :
  UnfoldsToMeansQuotedByFn [fp_fst qfs_tail] f_default.
  unfold UnfoldsToMeansQuotedByFn.
  apply ex_intro with 13.
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_tail handler hout:
    UnfoldsToMeansQuoted [handler qfs_tail] hout
    ->
    UnfoldsToMeansQuoted [(fs_pop_then handler) qfs_tail] hout.
  unfold UnfoldsToMeansQuoted.
  intro.
  destruct H as (steps, H).

  refine(
    fix ind h := match h with
  ).


  induction handler.
  contradict H. intro.
  unfold try_unfold_to_quoted in H. cbn in H.


  apply ex_intro with (10 + steps).
  rewrite <- H.
  unfold try_unfold_to_quoted; cbn.
  reflexivity.
  cbn.
  (* ; reflexivity. *)
Qed.


Lemma stream_nth_quoted s n :
    IsMeansQuotedStream s ->
    ∃ f, UnfoldsToMeansQuoted [@n s] f.
  intro.
  unfold UnfoldsToMeansQuoted.
  induction n.
  (* zero case (@n = f_fst) *)
  destruct H.
  apply ex_intro with f_quote.
  apply ex_intro with 20.
  destruct H.
  cbn; reflexivity.

  apply ex_intro with f_quote. cbn. unfold quote_f. cbn.
  induction n.
  admit.
  induction n.
Qed.

Lemma unfold_unique a b c :
  UnfoldsToMeansQuoted a b ->
  UnfoldsToMeansQuoted a c ->
  b = c.
  intros.

Qed.

Definition f_true := [[f_quote f_default] -> [f_quote f_default]].

(* Lemma KnownRequiredInferences_increasing n :
  KnownRequiredInferences n ⊆2 KnownRequiredInferences (S n).
  intros.
  cbn. *)

(* Lemma True_known n :
  TrueOf (KnownInferences n) f_true.
  apply (t_implies (KnownInferences n) f_default f_default).
  destruct n; [reflexivity|].
  cbn. unfold MetaInferences. intros. assumption.
Qed. *)

Lemma false_implies_everything p c :
  InfsAssertedBy f_false p c.
  apply ia_all with (x := p).
  (* apply ia_unfold with b :=. *)
  admit.
Qed.

Lemma false_not_directly_inferrable :
  InfsAssertedBy f_true f_true f_false -> False.
  intro.
  dependent induction H.

Qed.

Lemma false_never_known n :
  KnownInferences n f_true f_false -> False.
  induction n; [trivial|].

  intro.
  cbn in *. unfold MetaInferences in *.
  specialize (H f_true f_false).

  (* use IHn to eliminate the "or already known" case: *)
  assert (InfsAssertedBy f_false f_true f_false
        → InfsAssertedBy f_true f_true f_false) as H2.
  intro. apply H in H0. destruct H0; [assumption|contradiction].
  clear H IHn n. rename H2 into H.

  


  specialize H with (Infs := (KnownInferences n)).
  apply IHn; clear IHn.

  assert (TrueOf (KnownInferences n) f_false).
  apply H.
  intros; assumption.
  apply True_known.
  clear H.

  dependent destruction H0.
  specialize (H f_false). dependent destruction H; trivial.
  
  repeat (dependent destruction H || dependent destruction H0).
  dependent destruction H.

  apply (t_all (KnownInferences n) f_true f_false).
  
  (* pose (t_implies (KnownInferences n) f_true f_false). *)
  apply  in IHn.
  cbn in *.



  specialize H with (Rules := KnownRequiredInferences n).

  assert (InferencesProvenBy (KnownRequiredInferences n)
          ⊇2 KnownRequiredInferences n).
  intros. apply proof_by_rule; assumption.

  pose (H H0) as r. clearbody r. clear H H0.
  unfold InfSetObeysInference in r.
  specialize r with (UnknownMeanings := λ _, False).
  pose (r (True_required n (λ _, False))) as H. clearbody H. clear r.

  cbn in H.

  specialize H with (qfs_cons f_false qfs_tail).
  destruct H as (ap, (bp, (ua, (ub, i)))).
  apply isqfs_cons. apply isqfs_tail.
  
  (* TODO: coax Coq to understand this *)
  assert (ap = f_true) as apt. admit. rewrite apt in *. clear apt.
  assert (bp = f_false) as bpt. admit. rewrite bpt in *. clear bpt.
  
  exact (IHn (KnownRequiredInferences_closed_under_transitivity n i)).
Qed.

(* 
Lemma false_never_in_lower_bound_sequence n :
  LowerBoundSequence n f_true f_false -> False.
  induction n.
  unfold LowerBoundSequence, InferencesTheseInfSetsObey, InfSetObeysInference ; intros.
  cbn in H.
  (* use the very weak rules "eq",
    so it'll be easy to show that the rules don't prove what False says. *)
  (* specialize H with (Rules := eq). *)
  specialize (H eq X) with (UnknownMeanings := λ _, True). (* doesn't matter *)
  cbn in H.

  (* Right now we basically have (FormulaMeaning True -> FormulaMeaning False),
     and we want to simplify this by _providing_ (FormulaMeaning True).
     So we just say hey look, id x = id x. *)
  assert (∀ x : Formula,
    IsMeansQuotedStream x
    → ∃ ap bp : Formula,
        UnfoldsToMeansQuoted [(fp_fst) (x)] ap /\
        UnfoldsToMeansQuoted [(fp_fst) (x)] bp /\
        RulesProveInference eq ap
        bp).
  intros; clear H.
  destruct (stream_nth_quoted 0 H0) as (q, qe).
  unfold fs_nth in qe.
  (* rewrite qe. *)
  apply ex_intro with q.
  apply ex_intro with q.

  split; [assumption|].
  split; [assumption|].
  (* split; [apply unfold_quoted_done|].
  split; [apply unfold_quoted_done|]. *)
  apply proof_by_rule.
  reflexivity.

  assert (H := H H0); clear H0.

  (* Now, back to the main proving. *)
  specialize H with qfs_tail.
  destruct H as (ap, (bp, (ua, (ub, i)))); [apply isqfs_tail|].
  assert (j := provable_by_eq_means_eq i); clear i.
  subst bp.

  (* Now all we have to do is prove that [const true qfs_tail] and [@0 qfs_tail]
     can never unfold to the same thing.
     There are only finitely many possible unfoldings;
     this tells Coq to exhaust them. *)
  dependent destruction ua.
  dependent destruction ub.
  rewrite x0 in x; clear x0 f.
  dependent destruction x.
  dependent destruction c.
  dependent destruction x.
  dependent destruction x.
  dependent destruction H.
  dependent destruction ua.
  dependent destruction ub.
  rewrite x0 in x; clear x0 f.
  dependent destruction x.
  dependent destruction c.
  dependent destruction x.
  dependent destruction x.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  (* repeat (dependent destruction ua || dependent destruction ub). *)
Qed. *)


Theorem subsets_of_KnownInferences_are_consistent R n :
    R ⊆2 (KnownInferences n) ->
    RulesProveInference R f_true f_false ->
    False.
  intros justified proved.
  exact (false_never_known n (provable_by_subset_of_KnownInferences_means_known n justified proved)).
Qed.


Inductive ReifiedRule : Set :=
  .

Definition rule_external (rule : ReifiedRule) : InfSet.
  admit. Admitted.

Definition rule_internal (rule : ReifiedRule) : Formula.
  admit. Admitted.

Definition and_sym : ReifiedRule.
  admit. Admitted.

Definition IC_reified_rules : list ReifiedRule :=
  and_sym ::
  nil.

Definition axioms rules : Formula :=
  fold_right
  (λ rule agg, [(rule_internal rule) & agg])
  f_true
  rules.

Definition IC_axioms : Formula :=
  axioms IC_reified_rules.

Definition IC_axioms_rule : InfSet := (λ a b, b = IC_axioms).

Definition IC :=
  fold_right
  (λ rule agg a b, rule_external rule a b \/ agg a b)
  IC_axioms_rule
  IC_reified_rules.

Lemma and_sym_known : (rule_external and_sym ⊆2 KnownInferences 1).
Qed.

Lemma IC_external_rules_known :
  Forall
    (λ rule, (rule_external rule ⊆2 KnownInferences 1))
    IC_reified_rules.
  constructor; [apply and_sym_known|].
  trivial.
Qed.

Lemma internalize_rule_known rule :
  (rule_external rule ⊆2 KnownInferences 1) ->
  (KnownInferences 2 f_true (rule_internal rule)).
  
Qed.

Lemma IC_axioms_known :
  Forall
    (λ rule, (KnownInferences 2 f_true (rule_internal rule)))
    IC_reified_rules.
  apply Forall_impl with (λ rule, (rule_external rule ⊆2 KnownInferences 1)).
  apply internalize_rule_known.
  apply IC_external_rules_known.
Qed.

Lemma and_join t a b :
  KnownInferences 2 t a ->
  KnownInferences 2 t b ->
  KnownInferences 2 t [a & b].
  intros.
  unfold KnownInferences, MetaInferences in *.
  intros.
  apply t_and.
  apply H; trivial.
  apply H0; trivial.
Qed.


Lemma axioms_known a
  (rules : list ReifiedRule)
  (known : Forall
    (λ rule, (KnownInferences 2 a (rule_internal rule)))
    rules) : KnownInferences 2 a (axioms rules).
  
  induction rules as [|rule].
  cbn. unfold MetaInferences. intros. apply True_known. assumption.

  dependent destruction known.
  apply IHrules in known; clear IHrules.
  apply and_join; assumption.
Qed.

Lemma IC_axioms_rule_known :
  IC_axioms_rule ⊆2 KnownInferences 2.
  pose (axioms_known IC_axioms_known).

  intros. unfold IC_axioms_rule in H. rewrite H; clear H.
Qed.



Inductive Abstraction F :=
  | abstraction_const : F -> Abstraction F
  | abstraction_usage : Abstraction F
  | abstraction_apply :
      Abstraction F -> Abstraction F -> Abstraction F.



Notation "[ x => B ]" := (λ x, B)
  (at level 0, x at next level, y at next level).



(* ∀x, ∀y, [x & y] -> [y & x] *)
Definition and_sym_axiom := [[@0 &* @1] -> [@1 &* @0]].

Lemma and_sym_known a b : KnownInferences 1 [a & b] [b & a].
  unfold KnownInferences, MetaInferences.
  intros. cbn in *.
  dependent destruction H.
  apply t_and; assumption.
  (* repeat (dependent destruction H). *)
Qed.

Eval cbn in FormulaMeaning eq _ [_ & _].
Lemma and_sym_axiom_known : KnownRequiredInferences 2 f_true and_sym_axiom.
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey,
    InfSetObeysInference.
  intros. cbn in *. intros.
  clear H0. (* we're not going to use the proof of True *)
  
Qed.

Lemma and_assoc1_required a b c : KnownRequiredInferences 1 [a & [b & c]] [[a & b] & c].
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey, InfSetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.

Lemma and_assoc2_required a b c : KnownRequiredInferences 1 [[a & b] & c] [a & [b & c]].
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey, InfSetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.
(* 
Lemma unfold_further :
  RulseProveInference a b *)

Lemma predimp_trans_required a b c :
  AllInfSetsObeyInference [[a |= b] & [b |= c]] [a |= c].
  unfold AllInfSetsObeyInference, InfSetObeysInference; intros; cbn in *.
  intuition idtac.
  specialize H0 with (x := x).
  specialize H1 with (x := x).
  destruct (H0 H) as (ap0, (bp0, (ua0, (ub0, p0)))).
  destruct (H1 H) as (bp1, (cp1, (ub1, (uc1, p1)))).
  clear H0 H1.
  apply ex_intro with ap0.
  apply ex_intro with cp1.
  split; [assumption|].
  split; [assumption|].
  rewrite (unfold_unique ub0 ub1) in *.
  apply proof_by_transitivity with bp1; assumption.
Qed.

Inductive IC : InfSet :=
  | drop a b : IC [a & b] a
  | dup a b : IC [a & b] [[a & a] & b]
  | and_sym a b : IC [a & b] [b & a]
  | and_assoc1 a b c : IC [a & [b & c]] [[a & b] & c]
  | and_assoc2 a b c : IC [[a & b] & c] [a & [b & c]]
  | predimp_trans a b c t :
    IC [t &[[a -> b] & [b -> c]]]
       [t & [a -> c]]
  (* |  *)
  (* | axioms : IC f_true [and_sym_axiom & [some_other_axiom & more_axioms]] *)
  .

Lemma IC_known : IC ⊆2 KnownInferences 2.
  intros.
  destruct H.
  (* admit. admit. *)
  apply and_sym_known.
  apply and_assoc1_required.
  apply and_assoc2_required.
  apply predimp_trans_required.
Qed.

Theorem IC_is_consistent : ~(RulesProveInference IC f_true f_false).
  intro.
  pose 2 as n.
  exact (false_never_known n
    (provable_by_subset_of_KnownInferences_means_known n IC_known H)).
Qed.

Theorem IC_self_describing a b :
  RulesProveInference IC f_true [(quote_f a) -> (quote_f b)] ->
  RulesProveInference IC a b.
Qed.

Theorem IC_deduction a b :
  RulesProveInference IC a b ->
  RulesProveInference IC f_true [(quote_f a) -> (quote_f b)].
  intros.
  (* rule or transitivity? *)
  induction H.

  (* rule case: what rule? *)
  induction H.

  (* mostly just using axioms to fulfill rules: *)
  admit. admit. admit. admit.


  

  (* transitivity: *)
  admit.
Qed.

(* Theorem IC_deduction a b :
  TrueOf (InferencesProvenBy IC) a  *)

Lemma IC_proves_all_known n :
  KnownInferences n ⊆2 InferencesProvenBy IC.
  (* intros. *)

  induction n.

  admit.

  (* apply IHn; clear IHn. *)

  intros.
  unfold KnownInferences in H.
  unfold MetaInferences in H.

  (* pose (InferencesProvenBy IC) as Infs. *)
  assert (∀ Infs, (Infs ⊇2 InferencesProvenBy IC) -> )

  specialize (H Infs).
  pose (H IHn) as I. clearbody I. clear H.

  unfold KnownInferences, MetaInferences.
  

Qed.



Inductive FormulaMeaning2 PreviousMeanings : Formula -> Prop -> Prop :=
  | meaning_and a b A B :
    FormulaMeaning2 PreviousMeanings a A -> 
    FormulaMeaning2 PreviousMeanings b B -> 
    FormulaMeaning2 PreviousMeanings [a & b] (A /\ B)
  | meaning_implies a b :
    FormulaMeaning2 PreviousMeanings [a |= b]
      ((PreviousMeanings a) -> (PreviousMeanings b)).
    
  

Inductive FormulaTrue KnownInferences : Formula -> Prop :=
  | true_unfold a b :
    UnfoldStep a b ->
    FormulaTrue KnownInferences b -> 
    FormulaTrue KnownInferences a
  | true_and a b :
    FormulaTrue KnownInferences a -> 
    FormulaTrue KnownInferences b -> 
    FormulaTrue KnownInferences [a & b]
  (* | true_implies1 qa qb a :
    UnfoldsToMeansQuoted qa a ->
    (KnownInferences a -> False) ->
    FormulaTrue KnownInferences [qa |= qb]
  | true_implies2 qa qb b :
    UnfoldsToMeansQuoted qb b ->
    KnownInferences b ->
    FormulaTrue KnownInferences [qa |= qb] *)
  | true_implies a b :
    (KnownInferences a b) ->
    FormulaTrue KnownInferences
      [(quote_f a) |= (quote_f b)]
  | true_all f :
    (∀ x, FormulaTrue KnownInferences [f x])
    -> FormulaTrue KnownInferences [fuse f].

(* sets of sets of true formulas *)
(* a decreasing sequence (of sets-of-sets),
   with more formulas forced to be true each time *)
Fixpoint Sequence n (IsTrue : Formula -> Prop) := match n with
  | 0 => True
  | S pred => ∀ PreviouslyTrue,
    (Sequence pred) PreviouslyTrue ->
    ∀ f, FormulaTrue (PreviouslyTrue) f -> IsTrue f
  end.
(* or, increasing sequence (of sets of true formulas),
   with more formulas forced to be true each time *)
Definition InferencesBetween Truths (a b: Formula) := (Truths a -> Truths b).
Definition KnownInferences PreviousInferences (a b : Formula) :=
  ∀ Inferences Truths,
    (Inferences ⊇2 PreviousInferences) ->
    (InferencesBetween Truths ⊇2 PreviousInferences) ->
    (Truths ⊇ FormulaTrue Inferences) ->
    (Truths a -> Truths b).
    
Fixpoint KnownTrue n f := match n with
  | 0 => False
  | S pred => ∀ IsTrue,
    (∀ g, (KnownTrue pred) g -> IsTrue g) ->
    FormulaTrue IsTrue f
  end.
(* sets of meanings *)
Fixpoint SequenceM n Meanings := match n with
  | 0 => True
  | S pred => ∀ PreviousMeanings,
    (SequenceM pred) PreviousMeanings ->
    ∀ f M,
      FormulaMeaning2 PreviousMeanings f M ->
      Meanings f = M
  end.

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
    Forall2 (λ rule_p p, UnfoldsToMeansQuoted (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    UnfoldsToMeansQuoted (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).


    
(* Fixpoint unfold_n steps f : Formula :=
  match steps with
    | 0 => f
    | S pred => match unfold_step f with
      | None => f
      | Some g => unfold_n pred g
      end
    end.
Fixpoint try_unfold_n steps f : option Formula :=
  match steps with
    | 0 => None
    | S pred => match unfold_step f with
      | None => Some f
      | Some g => try_unfold_n pred g
      end
    end.

Definition UnfoldsTo f g :=
  ∃ steps, try_unfold_n steps f = Some g.

Eval simpl in unfold_n 30 [fp_fst (f_pair f_quote f_and)].
Lemma pair_fst a b c : 
  UnfoldsTo a c ->
  UnfoldsTo [fp_fst (f_pair a b)] c.
  unfold UnfoldsTo. apply ex_intro with 20.
Qed. *)
  
(* Fixpoint try_unfold_to_quoted steps f : option Formula :=
  match steps with
    | 0 => None
    | S pred => match unfold_step f with
      | None => unquote_formula f
      | Some g => try_unfold_to_quoted pred g
      end
    end. *)

(* Definition UnfoldsToMeansQuotedByFn f g :=
  ∃ steps, try_unfold_to_quoted steps f = Some g. *)

(* Inductive UnfoldsTo
  Interpretation
  (Interpret : Formula -> Interpretation -> Prop)
  : Formula -> Interpretation -> Prop :=
  | unfold_done f i : Interpret f i -> UnfoldsTo Interpret f i
  | unfold_step_then a b i : UnfoldStep a b ->
    UnfoldsTo Interpret b i ->
    UnfoldsTo Interpret a i. *)

(* Quoted formula streams: *)
(* [f => h => h const (f f)] *)
(* Definition qfs_tail_fn := [fuse
    [const [fuse [fuse f_id [const [f_quote f_default]]]]]
    [fuse [const const] [fuse f_id f_id]]
  ].
Definition qfs_tail := [qfs_tail_fn qfs_tail_fn].
Definition qfs_cons head tail := f_pair (quote_f head) tail.
Inductive IsMeansQuotedStream : Formula -> Prop :=
  | isqfs_tail : IsMeansQuotedStream qfs_tail
  | isqfs_cons head tail : IsMeansQuotedStream tail ->
    IsMeansQuotedStream (qfs_cons head tail). *)


(* Definition ObeysIntrinsicMeanings TruthValues KnownJudgedInferences :=
  (∀ a b, KnownJudgedInferences a b ->
    TruthValues [(quote_f a) -> (quote_f b)]) /\
  (∀ a b, TruthValues [a & b] <-> TruthValues a /\ TruthValues b) /\
  (∀ a, TruthValues [f_all a] <->
    (∀ x, TruthValues [a (quote_f x)])) /\
  (∀ a b, UnfoldStep a b -> (TruthValues a <-> TruthValues b))
  . *)


(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
(* Definition MetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  ∀ Infs,
    Infs ⊇2 KnownJudgedInferences ->
    (TrueOf Infs a -> TrueOf Infs b). *)

(* Definition MetaInferences KnownJudgedInferences (a b : Formula) :=
  ∀ TruthValues,
    (ObeysIntrinsicMeanings TruthValues KnownJudgedInferences) ->
    (TruthValues a -> TruthValues b). *)

(* Definition FormulaAsRule f (a b : Formula) : Prop :=
  ∀ Infs, TrueOf Infs f -> Infs a b. *)