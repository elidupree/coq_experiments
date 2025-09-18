Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Vector.
Require Import Coq.Lists.List.
Import ListNotations.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(* Protect myself from accidental infinite loops during dev work *)
(* Set Typeclasses Iterative Deepening. *)
Set Typeclasses Depth 3.

(****************************************************
                 Proof bureaucracy
****************************************************)

Section ProofBureaucracy.
  (* When proving, there are a lot of simplification steps that I want to be applied automatically, with very little effort. As the definitions and lemmas proceed, I want to add more simplification steps to a hints database.

  Unfortunately, the `auto` family of tactics, which apply hints from a database, cancel all the applications if you didn't solve the entire goal. That's not what I want. As a hack to work around this, it's possible to shelve an incomplete goal, and `auto` will interpret this as "success". So we just end every hint with `shelve`. *)

  Ltac autouse_shelving_db steps db :=
    idtac steps; match steps with
      | S ?p => try ((progress (unshelve typeclasses eauto 99 with db));
        autouse_shelving_db p db)
      | _ => idtac "Warning: steps ran out"
    end.

  Create HintDb simplify.
  Ltac simplify := autouse_shelving_db 20 ident:(simplify).

  (* We *do* want to apply intros if it helps simplify, but not if it doesn't, so don't shelve here. Also, since it's the second-choice and can duplicate work, make it high-cost. *)
  (* Hint Extern 12 => intro; intros : simplify. *)

  (* ...and if we *can* solve easily, might as well. *)
  Hint Extern 1 => solve [trivial | constructor | discriminate] : simplify.

  (* One notable simplification step is to rewrite equality hypotheses when one side is just another hypothesis. But it's kinda expensive, so we give it a high-ish cost. *)
  Hint Extern 9 => progress match goal with
    | x : _ |- _ => match goal with
      | eq : x = _ |- _ => rewrite eq in *; clear x eq
      | eq : _ = x |- _ => rewrite <- eq in *; clear x eq
      end
    end; shelve
    : simplify.

  (* `remember`, but not if it's redundant *)
  Ltac dontforget term :=
    lazymatch term with
    | (_ _) => lazymatch goal with
      | _ : _ = term |- _ => idtac
      | _ : term = _ |- _ => idtac
      | _ => remember term
      end
    | _ => idtac 
    end.
End ProofBureaucracy.

(****************************************************
                    
****************************************************)

Section Rules.
  Definition System P := P -> P -> Prop.

  Inductive Derivable [P] (S : System P) (premise : P) (conclusion : P) : Prop :=
    | d_rule (_:S premise conclusion)
    | d_chain (b : P) (_: Derivable S premise b) (_: Derivable S premise conclusion)
    | d_gather (_:∀ci, S conclusion ci -> Derivable S premise ci)
    .

  Lemma Extensions1DoNothing P (S : System P) : ∀ p c, Derivable (Derivable S) p c -> Derivable S p c.
    Set Printing Implicit.
    fix f 3.
    destruct 1.
    assumption.
    apply d_chain with b; apply f; assumption.
    apply d_gather. intros.
    apply f.
    apply H.
    apply d_rule; assumption.
  Qed.

  Inductive DerivabilityOmega [P] (S : System P) : System P -> Prop :=
    | d_rules : DerivabilityOmega S (Derivable S)
    | d_succ (R : System P) : DerivabilityOmega S (Derivable R) -> DerivabilityOmega S (Derivable (Derivable R)).

  Lemma ExtensionsOmegaDoNothing P (S : System P) p c D : DerivabilityOmega S D -> D p c -> Derivable S p c.
    Set Printing Implicit.
    induction 1.
    trivial.
    intro.
    apply IHDerivabilityOmega.
    apply Extensions1DoNothing.
    assumption.
  Qed.

  
  Unset Printing Implicit.
  Definition System3 P := P -> P -> P -> Prop.

  (* a p c = asserter premise conclusion *)
  Definition UsePremises {P} (Ctx : System3 P) := ∀ a p, Ctx a p p.
  Definition UseRules {P} (Rules : System3 P) (Ctx : System3 P) := ∀ a p c, Rules a p c -> Ctx a p c.
  Definition Chain {P} (Ctx : System3 P) := ∀ a x y z, Ctx a x y -> Ctx a y z -> Ctx a x z.
  Definition Gather {P} (Rules : System3 P) (Ctx : System3 P) := ∀ a x y, (∀ z, Rules a y z -> Ctx a x z) -> Ctx a x y.

  Definition CanGatherAsserters {P} (gatherer : P) (Rules : System3 P) (Ctx : System3 P) := ∀ a b, (∀ p c, Rules b p c -> Ctx a p c) -> Ctx gatherer a b.
  Definition CanCollapse {P} (collapser : P) (Ctx : System3 P) := ∀ a c, Ctx a a c -> Ctx collapser a c.
  Definition AnyoneCanGatherAsserters {P} (Rules : System3 P) (Ctx : System3 P) := ∀ m, CanGatherAsserters m Rules Ctx.
  Definition AnyoneCanCollapse {P} (Ctx : System3 P) := ∀ m, CanCollapse m Ctx.


  Definition NoRules P : System3 P := λ a p c, False.
  Definition Absurd {P} (Ctx : System3 P) := ∀ a p c, Ctx a p c.

  Definition ResultsOf {P} (Reasoning : System3 P -> Prop) : System3 P := λ a p c, (∀ (Ctx : System3 P), Reasoning Ctx -> Ctx a p c).
  Definition And {P} (A B : System3 P -> Prop) : (System3 P -> Prop) := λ Ctx, A Ctx ∧ B Ctx.

  Inductive RussellsProps := rp_true | rp_paradox | rp_false.
  Definition Russells : System3 RussellsProps := λ a p c, match a, p, c with
    | rp_paradox, rp_paradox, _ => True
    | _, _, _ => False
    end.
  
  Definition ExtendWith {P} (Reasoning : System3 P -> Prop) (Ctx : System3 P) : System3 P := ResultsOf (And Reasoning (UseRules Ctx)).
  Definition ExtendWith2 {P} (Reasoning : System3 P -> System3 P -> Prop) (Rules : System3 P) : System3 P := ResultsOf (And (Reasoning Rules) (UseRules Rules)).

  Definition BrokenByRussells1 {P} (Rules : System3 P) := (ExtendWith AnyoneCanCollapse Rules).
  Lemma anyone_says_paradox_absurd a c : (BrokenByRussells1 Russells) a rp_paradox c.
    intros Ctx (AnyoneCanCollapse, R).
    apply AnyoneCanCollapse.
    apply R.
    constructor.
  Qed.
  Lemma paradox_only_says_paradox_absurd p c : (BrokenByRussells1 Russells) rp_paradox p c -> p = rp_paradox.
    intro.
    destruct H with (λ (a p c : RussellsProps), p = rp_paradox); trivial.
    split.
    intros a b. trivial.
    intros a p0 c0 R.
    destruct a; destruct p0; cbn; cbv in R; trivial; contradiction.
  Qed.
  Lemma paradox_only_says_what_anyone_does a p c : (BrokenByRussells1 Russells) rp_paradox p c -> (BrokenByRussells1 Russells) a p c.
    intro H.
    apply paradox_only_says_paradox_absurd in H. rewrite H.
    apply anyone_says_paradox_absurd.
  Qed.

  Definition BrokenByRussells2 {P} (Rules : System3 P) := ExtendWith2 AnyoneCanGatherAsserters (BrokenByRussells1 Rules).
  Lemma anyone_says_anyone_paradox a p : (BrokenByRussells2 Russells) a p rp_paradox.
    intros Ctx (GatherAsserters, R2).
    apply GatherAsserters; intros.
    apply R2.
    apply paradox_only_says_what_anyone_does.
    assumption.
  Qed.

  Definition BrokenByRussells {P} (Rules : System3 P) := ExtendWith Chain (BrokenByRussells2 Rules).
    
  Lemma yes_its_broken_by_russells : Absurd (BrokenByRussells Russells).
    unfold Absurd; intros.
    intros Ctx (Chain, R2).
    eapply Chain.
    {
      apply R2.
      apply anyone_says_anyone_paradox.
    }
    {
      apply R2.
      intros Ctx2 (A, R3).
      apply R3.
      apply anyone_says_paradox_absurd.
    }
  Qed.
    


  (* Variable Object : Type. *)

  (* Record Proposition := { relation : Object ; lhs : Object ; rhs : Object }. *)
  (* Notation "( a , b ) ∈ rel" := {| relation := rel ; lhs := a ; rhs := b |} (at level 0). *)
  (* Record Implication Object := { premises : Object -> Prop ; conclusion : Object }. *)
  (* Definition Rule Object := Implication Object -> Prop. *)

  Class System := {
    Object : Type ;
    Proposition : Type ;
    PremiseSet : Type ;
    PremiseSetMember : PremiseSet -> Proposition -> Prop ;
    (* Rule : Type ; *)
    Rules : PremiseSet -> Proposition -> Prop ;
    (* ValidRules : Rule -> Prop ; *)
    (* Theorems : Proposition -> Prop ;
    SystemCanUseRules : ∀ ps c, Rules {| premises := ps ; conclusion := c |} -> (∀ p, ps p -> Theorems p) -> Theorems c ; *)
  }.

  Inductive Derivation {S : System} (premises : PremiseSet) (conclusion : Proposition) :=
    | d_among_premises (_:PremiseSetMember premises conclusion)
    | d_chain
      (last_rule_premises : PremiseSet)
      (last_rule_valid : Rules last_rule_premises conclusion)
      (last_rule_premises_satisfied :
        ∀ p, PremiseSetMember last_rule_premises p ->
             Derivation premises p)
    .
  
  (* Variable ReaderRules : Rule.
  Variable ReaderTheorems : Objects.
  Definition AllTrue ps := ∀ p, ps p -> ReaderTheorems p.
  Variable ReaderCanUseRules : ∀ ps c, ReaderRules {| premises := ps ; conclusion := c |} -> AllTrue ps -> ReaderTheorems c. *)

  Class SystemOfSystems := {
      S :: System ;
      MeansSubsystemHasRule : Proposition -> Object -> PremiseSet -> Proposition -> Prop ;
    }.

  Definition Subsystem {S : SystemOfSystems}
    (subsystem_object : Object) (theorems : Proposition -> Prop) : System := {|
      Object := Object ;
      PremiseSetMember := PremiseSetMember ;
      Rules := λ ps c, ∃ t, theorems t ∧ MeansSubsystemHasRule t subsystem_object ps c
    |}.
  
  Definition RuleDoesValidSubsystemDerivations {S : SystemOfSystems}
    (dps : PremiseSet) (dc : Proposition) :=
      ∀ so sps sc, MeansSubsystemHasRule dc so sps sc ->
        @Derivation (Subsystem so (PremiseSetMember dps)) sps sc.
  
  Definition RuleValidOnMeanings {S : System}
    (ps : PremiseSet) (c : Proposition) (Meaning : Proposition -> Prop) :=
      (∀ p, PremiseSetMember ps p -> Meaning p)
        -> Meaning c.
  
  Lemma AlwaysFineToExtendWithDerivation {S : System} (Meaning : Proposition -> Prop) (RulesValid : ∀ ps c, Rules ps c -> RuleValidOnMeanings ps c Meaning) :
    ∀ ps c, Derivation ps c -> RuleValidOnMeanings ps c Meaning.
    intros ps c D Pm.
    induction D; [apply Pm|apply RulesValid with last_rule_premises]; assumption.
  Qed.
  
  Definition SubsystemRuleValidOnSubsystemMeanings {S : SystemOfSystems} (so : Object)
    (sps : PremiseSet) (sc : Proposition) (SubsystemMeanings : Object -> Proposition -> Prop) (theorems : Proposition -> Prop) :=
      @RuleValidOnMeanings (Subsystem so theorems) sps sc (SubsystemMeanings so).
  
  Definition PropRuleValidOnSubsystemMeanings {S : SystemOfSystems}  (p : Proposition) (SubsystemMeanings : Object -> Proposition -> Prop) (theorems : Proposition -> Prop) :=
    (∀ so sps sc, MeansSubsystemHasRule p so sps sc -> @RuleValidOnMeanings (Subsystem so theorems) sps sc (SubsystemMeanings so)).
  
  Definition RuleValidOnSubsystemMeanings {S : SystemOfSystems}
    (ps : PremiseSet) (c : Proposition) (SubsystemMeanings : Object -> Proposition -> Prop) :=
      (∀ p, PremiseSetMember ps p -> PropRuleValidOnSubsystemMeanings p SubsystemMeanings (PremiseSetMember ps))
        -> PropRuleValidOnSubsystemMeanings c SubsystemMeanings (PremiseSetMember ps).
    
  Lemma AlwaysFineToExtendWithSubsystemDerivationRules {S : SystemOfSystems}
     (SubsystemMeanings : Object -> Proposition -> Prop) :
    ∀ dps dc, RuleDoesValidSubsystemDerivations dps dc -> RuleValidOnSubsystemMeanings dps dc SubsystemMeanings.
    unfold RuleValidOnSubsystemMeanings, PropRuleValidOnSubsystemMeanings, SubsystemRuleValidOnSubsystemMeanings, RuleDoesValidSubsystemDerivations in *.
    intros dps dc D Pm so sps sc Ms.
    
    apply AlwaysFineToExtendWithDerivation.
    (* apply r. *)
    {
      intros ps c Rpsc.
      unfold Rules, Subsystem in Rpsc.
      destruct Rpsc as (rule_asserter, (rule_asserter_hypothesized, rule_asserter_hypothesizes_ps_c)).
      (* Set Printing Implicit. *)
      apply Pm with rule_asserter; assumption.
    }
    {
      apply D; assumption.
    }
  Qed.

  (* … And therefore, if you had a concrete subsystem where the subsystem-meanings were exactly "this rule does valid subsystem derivations", then you would be allowed to both (1) have a rule that did MP on the entries of that subsystem and (2) inject arbitrary valid subsystem derivations into that subsystem. The injection is valid because it has fulfilled the meaning directly, and MP is valid because of the above lemma.

  What's the generalization of this? As the above lemma shows, "Rule does valid subsystem derivations" is a special case of "rule valid on (our) subsystem meanings" – a particular special case which is notable for not being dependent on the concrete meanings in any way. You (probably?) cannot have a subsystem whose meanings are defined as "rule valid on (our) subsystem meanings", because it would be an improper recursive definition. But the principle here should be valid in any situation where you have a subsystem whose meanings happen-to-be a special case of "rule valid on (our) subsystem meanings". *)
  
  Definition MeansValidDerivability {S : SystemOfSystems}
    (dp : Proposition) (theorems : Proposition -> Prop) :=
      ∀ so ps c, MeansSubsystemHasRule dp so ps c ->
        (∀ p, PremiseSetMember ps p ->
          @Derivation (Subsystem so theorems) ps c)
        -> @Derivation (Subsystem so theorems) ps c.
  
  (* ro for relation-object , bu for bucket *)
  Variable ro_prop_relation : Object.
  Variable ro_prop_lhs : Object.
  Variable ro_prop_rhs : Object.

  Variable ro_imp_premises : Object.
  Variable ro_imp_conclusion : Object.
  
  Variable ro_all_true : Object.
  Variable ro_imp_in_bucket : Object.

  Inductive NeededToRepresentProp (p : Proposition) (o : Object) : Propositions := 
    | ntrp_rel : NeededToRepresentProp p o ((o, relation p) ∈ ro_prop_relation)
    | ntrp_l   : NeededToRepresentProp p o ((o, lhs p) ∈ ro_prop_lhs)
    | ntrp_r   : NeededToRepresentProp p o ((o, rhs p) ∈ ro_prop_rhs)
    .

  Definition PropRepresented (p : Proposition) (o : Object) := AllTrue (NeededToRepresentProp p o).

  Variable ReaderAllTrueDoesntLie : ∀ p o, PropRepresented p o -> ReaderTheorems ((o, o) ∈ ro_all_true) -> AllTrue p.


  Inductive NeededToRepresentProps (p : Propositions) (o : Object) : Propositions := 

  Inductive NeededToRepresentImp (i : Implication) (io po : Object) : Propositions := 
    | ntri_ps : NeededToRepresentImp i io po ((io, po) ∈ ro_imp_premises)
    | ntri_c  : NeededToRepresentImp i io po ((io, conclusion i) ∈ ro_imp_conclusion)
    .




  (* Definition IndexTypesType := Type -> Prop.
  Existing Class IndexTypesType.
  Variable IndexTypes : IndexTypesType.
  Variable Object : Type.

  Record IndexedSet (Member : Type) := {
      iset_Index : Type ;
      iset_IndexAllowed : IndexTypes iset_Index;
      iset_Members : iset_Index -> Member
    }. *)
  
  Variable TypeId : Type.
  Variable Types : TypeId -> Type.
  Record IndexedSet (Member : Type) := {
      iset_TypeId : TypeId ;
      iset_Members : Types iset_TypeId -> Member
    }.

  Inductive RuleConstr (env_id : TypeId) :=
    | r_Or (operands : IndexedSet (Types env_id))
    | r_And (operands : IndexedSet (Types env_id))
    | r_constr
    | .

  CoInductive Rule (env_id : TypeId) :=
    | r_Or : IndexedSet (Rule env_id) -> (Rule env_id)
    | r_And : IndexedSet (Rule env_id) -> (Rule env_id)
    | r_constr : (Types env_id) -> Object -> IndexedSet env_id -> (Rule env_id)
    | r_ : IndexedSet (Rule env_id) -> (Rule env_id)
    .
  
  Definition MP := 
End Rules.

Section Specialization.
  
  
End Specialization.