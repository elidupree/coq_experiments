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

Section Graph.

  Definition set T := T -> Prop.

  Variable RoleId : Type.
  Variable VertexId : Type.
  Variable EdgeId : Type.
  Variable Graph : Type.
  Variable GraphIncludes : Graph -> VertexId -> EdgeId -> RoleId -> Type.
  Variable GraphExcludes : Graph -> VertexId -> EdgeId -> RoleId -> Type.
  Variable GraphIncludesOneOf : Graph -> Graph -> Type.
  Variable GraphExcludesOneOf : Graph -> Graph -> Type.

  Hypothesis gi_ge : ∀ g v e r, GraphIncludes g v e r -> GraphExcludes g v e r -> False.
  Hypothesis gioo : ∀ g1 g2, GraphIncludesOneOf g1 g2 -> (∀ v e r, GraphIncludes g2 v e r -> GraphExcludes g1 v e r) -> False.
  Hypothesis geoo : ∀ g1 g2, GraphExcludesOneOf g1 g2 -> (∀ v e r, GraphIncludes g2 v e r -> GraphIncludes g1 v e r) -> False.

  
  Inductive SubgraphConstraint := rule (present : Graph) (absent : Graph).

  Inductive ContainsObeyer (g ng : Graph) : (p np : Graph) -> Prop :=
    oc_cons present absent vmap emap :
      (∀ v e r, present v e r -> g (vmap v) (emap e) r) ->
      (∀ v e r, absent v e r -> ¬ g (vmap v) (emap e) r) ->
      ContainsObeyer g (rule present absent).

  Definition DefiesAll (g : Graph) (cs : set SubgraphConstraint) := ∀ c, cs c -> ¬ ContainsObeyer g c.

  Inductive IsDefier (g ng : Graph) (p np : Graph) (vmap : VertexId -> VertexId) (emap : EdgeId -> EdgeId) :=
    | broke_requirement v e r : g (vmap v) (emap e) r -> np v e r -> IsDefier g ng p np vmap emap
    | broke_exclusion v e r : ng (vmap v) (emap e) r -> p v e r -> IsDefier g ng p np vmap emap.

  Definition LacksObeyer (g ng p np : Graph) :=
    ∀ vmap emap,
      IsDefier g ng p np vmap emap.

  Definition LacksObeyerOfAny (g ng : Graph) (cs : ∀ (p np : Graph), Prop) :=
    ∀ p np, cs p np -> LacksObeyer g ng p np.

  Variable SubgraphDec : Graph -> Graph -> bool.
  Variable GraphSet : Type.
  Variable AnySubgraph : Graph -> GraphSet -> Prop.



  Definition ForbiddenSubgraphSet := set (Graph) 
End Graph.