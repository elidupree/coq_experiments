Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import List.
Require Import String.

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

Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.

Section Formulas.
  Inductive Formula :=
    | f_atom
    | f_branch (_ _:Formula).
  
  Inductive Rewrite :=
    | r_ignore
    | r_replace (_ _:Formula)
    | r_branch (_ _:Rewrite).

  Inductive RRewrites : Rewrite -> Formula -> Formula -> Prop :=
    | rr_ignore f : RRewrites r_ignore f f
    | rr_replace a b : RRewrites (r_replace a b) a b
    | rr_branch a b a1 b1 a2 b2 :
        RRewrites a a1 a2 -> RRewrites b b1 b2 ->
        RRewrites (r_branch a b) (f_branch a1 b1) (f_branch a2 b2).

  Definition RewriteSet := Rewrite -> Prop.

  Inductive RsRewrites (Rs : RewriteSet) (a b : Formula) : Prop :=
    | rsr r : Rs r -> RRewrites r a b -> RsRewrites Rs a b.
  

End Formulas.

(****************************************************
        Implementing variables via rewrites
****************************************************)
Section ImplementingVariablesViaRewrites.
  (* 
    slot ?? atom -> atom done
    branch (left cons) (_ _ space) _ -> branch (left space) (_ _ cons) _
    branch (left space) (_ _ done) _ -> branch (right space) (_ _ space) _ 
    branch (right space) _ (_ _ done) -> branch done _ (_ _ space)

    coConstruct (_ space) (_ space) -> coConstruct (_ "atom") (_ "atom")
    coConstruct (_ space) (_ space) -> coConstruct (_ "branch") (_ "branch")

    coConstruct (_ done) (_ done) -> ???

    move (_ "atom") (_ space) -> move (_ space) (_ "atom")
    copy (_ "atom") (_ space) (_ space) -> copy (_ space) (_ "atom") (_ "atom")
    "move to staging, then copy" etc
    
   *)
End ImplementingVariablesViaRewrites.

(****************************************************
            Embedding finite rewrite lists
****************************************************)
Section EmbeddingFiniteRewriteLists.
  Definition next_atom f := f_branch f_atom f.

  Definition empty_scratchspace := f_atom.
  Definition t_formula := next_atom empty_scratchspace.
  Definition t_rewrite := next_atom t_formula.
  Definition t_rewrites := next_atom t_formula.
  Definition t_rrewrites := next_atom t_formula.
  Definition typed_var (t : Formula) (args : Formula) :=
    f_branch t (f_branch empty_scratchspace args).

  Fixpoint embed_formula (f : Formula) : Formula :=
    typed_var t_formula match f with
    | f_atom => f_atom
    | f_branch a b => f_branch (embed_formula a) (embed_formula b)
    end.

  Fixpoint embed_rewrite (r : Rewrite) : Formula :=
    typed_var t_rewrite match r with
    | r_ignore => f_atom
    | r_replace a b => f_branch (embed_formula a) (embed_formula b)
    | r_branch a b => f_branch (embed_rewrite a) (embed_rewrite b)
    end.
  
  Fixpoint embed_rewrites (r : list Rewrite) : Formula :=
    typed_var t_rewrites match r with
    | nil => f_atom
    | cons a b => f_branch (embed_rewrite a) (embed_rewrites b)
    end.
  
  Fixpoint embed_rrewrites r a b (rr : RRewrites r a b) : Formula :=
    typed_var t_rrewrites match rr with
    | rr_ignore f => f_atom
    | rr_replace a b => f_branch (embed_formula a) (embed_formula b)
    | rr_branch a b a1 b1 a2 b2 rra rrb => f_branch (embed_rewrite a) (embed_rewrite b)
    end.
  
  (* Inductive RRewrites : Rewrite -> Formula -> Formula -> Prop :=
    | rr_ignore f : RRewrites r_ignore f f
    | rr_replace a b : RRewrites (r_replace a b) a b
    | rr_branch a b a1 b1 a2 b2 :
        RRewrites a a1 a2 -> RRewrites b b1 b2 ->
        RRewrites (r_branch a b) (f_branch a1 b1) (f_branch a2 b2). *)
  Definition embed_rr_ignore : Rewrite :=
    
    
    

End EmbeddingFiniteRewriteLists.