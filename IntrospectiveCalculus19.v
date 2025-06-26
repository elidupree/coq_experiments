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
                    Formulas
****************************************************)

Section Formulas.

  (* Variable Formula : Type. *)
  Variable Relation : Type.

  (* Record ExistentialProposition := {
    ep_r : Relation ;
    ep_a : Formula ;
    ep_b : Formula ;
  }.
  Record Proposition := {
    p_e : ExistentialProposition ;
    p_witness : Formula
  }. *)

  (* Inductive Rule :=
    | rule_base (conclusion : ExistentialProposition)
    | rule_implies (premise : Proposition) (continuation : Rule)
    . *)

  (* Definition Ruleset := list Rule. *)

  (* Variable rules : Ruleset. *)
  (* Variable IsTrue : Proposition -> Prop. *)
  (* Definition Truths := Proposition -> Prop.
  Definition Witnesses :=  *)

  (* Inductive Proof : -> Type :=
    |  *)
  (* Variable base_witness : -> Formula. *)
  (* Inductive Obeys (truths : Truths) : Rule -> Prop :=
    | obeys_base conclusion : truths conclusion -> Obeys truths {| p_e := (rule_base conclusion) ; p_witness := witness (rule_base conclusion) |} . *)

  (* Definition base_witnesses := ∀ (a b : Formula), Formula.
  Definition base_valid (r : Relation) (w : base_witnesses) := ∀ (a b : Formula), IsTrue {| p_e := {| ep_r := r ; ep_a := a ; ep_b := b |} ; p_witness := w a b |}. *)

  Inductive Rule :=
    | rule_conclusion (relation : Relation) (operands : list nat)
    | rule_implies (relation : Relation) (witness : nat) (operands : list nat) (continuation : Rule)
    .
  
  Inductive Witness : Relation -> list Witness -> Type.

  (* Variable RuleAvailable : Rule -> Prop. *)

  Inductive VariablesProvePremise : list Witness -> Relation -> list nat -> Prop :=.
  Inductive VariablesProve : list Witness -> Rule -> Prop :=
    | base_witness : 
    | vo_implies l r w o c : VariablesProvePremise r w o -> VariablesProve l c -> VariablesProve l (rule_implies r w o c)
  with Specialization (r : Rule) : .

  Inductive ex_but_no_predicate (A:Type) : Prop :=
    ex_but_no_predicate_intro : A -> ex_but_no_predicate A.

  Inductive EbnpHasProperty [A:Type] (P:A -> Prop) : ex_but_no_predicate A -> Prop :=
    ebnp_has_property_intro : forall x:A, P x -> EbnpHasProperty P (ex_but_no_predicate_intro x).

  Record FancyNatSystem := {
      fns_Witness : Type ;

      fns_IsZero : list fns_Witness -> Prop ;
      fns_IsSucc : list fns_Witness -> Prop ;
      fns_IsNatW : list fns_Witness -> Prop ;

      fns_zero_constructor_rule : ∃ w, fns_IsZero (w::nil) ;
      fns_succ_constructor_rule : ∀ w x : fns_Witness, fns_IsNatW (w::x::nil) -> ∃ y : fns_Witness, fns_IsSucc (y::x::nil) ;
      
      fns_zero_nat_rule : ∀ w : fns_Witness, fns_IsZero (w::nil) -> ∃ x, fns_IsNatW (x::w::nil) ;
      fns_succ_nat_rule : ∀ x y : fns_Witness, fns_IsSucc (y::x::nil) -> ∃ w : fns_Witness, fns_IsNatW (w::y::nil) ;
    }.

  Record FancyNatSystem := {
      ss_Witness : Type ;

      ss_IsZero : ss_Witness -> Prop ;
      ss_IsSucc : ss_Witness -> ss_Witness -> Prop ;
      ss_IsNatW : ss_Witness -> ss_Witness -> Prop ;

      ss_zero_constructor_rule : ex ss_IsZero ;
      ss_succ_constructor_rule : ∀ w x : ss_Witness, ss_IsNatW w x -> ∃ y : ss_Witness, ss_IsSucc y x ;
      
      ss_zero_nat_rule : ∀ w : ss_Witness, ss_IsZero w -> ∃ x, ss_IsNatW x w ;
      ss_succ_nat_rule : ∀ x y : ss_Witness, ss_IsSucc y x -> ∃ w : ss_Witness, ss_IsNatW w y ;
    }.

  (* Record WitnessBasedPremise (VarIdentity : Type) (relation_arities : list nat) := {
      wbp_arity_without_witness : nat ;
      wbp_in : In wbp_arity_without_witness relation_arities ;
      wbp_vars : Vector.t VarIdentity (S wbp_arity_without_witness)
    }.

  Record WitnessBasedRule (relation_arities : list nat) := {
      wbr_VarIdentity : Type ;
      wbr_conclusion_arity : nat ;
      wbr_in : In wbr_conclusion_arity relation_arities ;
      wbr_conclusion_vars : Vector.t wbr_VarIdentity (S wbr_conclusion_arity) ;
      wbr_premises : list (WitnessBasedPremise wbr_VarIdentity relation_arities)
    }.
    
  Record WitnessBasedSystem := {
      relation_arities : list nat ;
      rules : list (WitnessBasedRule relation_arities)
    }. *)

  Record WitnessBasedRule (RelationIdentity VarIdentity : Type) := {
      wbr_conclusion_relation : RelationIdentity ;
      wbr_conclusion_vars : list VarIdentity ;
      wbr_premises : list (RelationIdentity * list VarIdentity)
    }.
    
  Record WitnessBasedSystem := {
      wbs_RelationIdentity : Type ;
      wbs_VarIdentity : Type ;
      wbs_rules : list (WitnessBasedRule wbs_RelationIdentity wbs_VarIdentity)
    }.
    
  Record SystemSystem := {
      ss_Witness : Type ;

      ss_Rule : list ss_Witness -> Prop ;
      ss_Nil : list ss_Witness -> Prop ;
      ss_IsAnyWitness : list ss_Witness -> Prop ;
      ss_Substitutes : list ss_Witness -> Prop ; (* variables + context = values *)
      ss_RulesetSatisfiesPremises : list ss_Witness -> Prop ; (* ruleset, premise-list, context *)
      ss_RulesetProves : list ss_Witness -> Prop ; (* ruleset, witnesses *)

      ss_use_rule :
        ∀ ruleset rule premises conclusion context result x,
          ss_Rule [premises; conclusion; rule] ->
          ss_RulesetSatisfiesPremises [ruleset; premises; context; x] ->
          ss_Substitutes [conclusion; context; result] ->
          ∃ w, ss_RulesetProves [ruleset; result ; w] ;

      ss_premises_nil :
        ∀ ruleset premises context,
          ss_Nil [premises] ->
          ∃ w, ss_RulesetSatisfiesPremises [ruleset; premises; context; w] ;

      ss_premises_cons :
        ∀ ruleset premises premise context proof x,
          ss_Substitutes [premise; context; proof] ->
          ss_RulesetSatisfiesPremises [ruleset; premises; context; x] ->
          ∃ w, ss_RulesetSatisfiesPremises [ruleset; premises; context; w] ;

    }.
  
  Record SystemSystem1 := {
      Witness : Type ;
      VarIdentity : Type ;
      RelationMembership : Type ;
      RuleApplication : Type ;
      
      rm_nullary : Relation -> RelationMembership ;
      rm_onemore_arg : VarIdentity -> RelationMembership -> RelationMembership ;

      ra_forall : VarIdentity -> RuleApplication -> RuleApplication ;
      ra_let : VarIdentity -> Witness -> RuleApplication -> RuleApplication ;
      (* ra_let : VarIdentity -> Witness -> RuleApplication -> RuleApplication ; *)

      Specializes : RuleApplication -> RuleApplication -> Prop ;
    }.
  
  Record System := {
      Witness : Type ;
      RuleAvailable : Rule -> Prop ;
      base_witness : ∀ (relation : Relation) (operands : list nat), RuleAvailable (rule_conclusion relation operands) -> list Witness -> Witness ;
      (* implies_witness :  ; *)

    }.
    

End Formulas.