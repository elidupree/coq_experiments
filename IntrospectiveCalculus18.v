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

(* Section Formulas. *)
  Inductive Formula :=
    | f_atom
    | f_branch (_ _:Formula).

  Declare Scope formula_scope.
  Bind Scope formula_scope with Formula.
  Notation "★" := f_atom.
  Notation "( a , b )" := (f_branch a b).
  
  Inductive Rewrite :=
    | r_ignore
    | r_replace (_ _:Formula)
    | r_branch (_ _:Rewrite).
  Declare Scope rewrite_scope.
  Bind Scope rewrite_scope with Rewrite.
  Notation "'_'" := r_ignore : rewrite_scope.
  Notation "a ⇒ b" := (r_replace a b) (at level 80, no associativity) : rewrite_scope.
  Notation "a !" := (r_replace a a) (at level 80, no associativity) : rewrite_scope.
  Notation "[ a , b ]" := (r_branch a b) : rewrite_scope.

  Inductive RRewrites : Rewrite -> Formula -> Formula -> Prop :=
    | rr_ignore f : RRewrites r_ignore f f
    | rr_replace a b : RRewrites (r_replace a b) a b
    | rr_branch a b a1 b1 a2 b2 :
        RRewrites a a1 a2 -> RRewrites b b1 b2 ->
        RRewrites (r_branch a b) (a1, b1) (a2, b2).

  Definition RewriteSet := Rewrite -> Prop.

  Inductive RsRewrites (Rs : RewriteSet) (a b : Formula) : Prop :=
    | rsr r : Rs r -> RRewrites r a b -> RsRewrites Rs a b.
  

(* End Formulas. *)

(****************************************************
        Implementing variables via rewrites
****************************************************)
(* Section ImplementingVariablesViaRewrites. *)
  (* object :~ ((symbol) (args...))
     where args are objects
     need:
     ∀ s : Symbol, o : Object, s ≠ o
     to achieve this:
     ∀ s t : Symbol, f : Formula, s ≠ (t, f)
     easiest way: just make LHS of symbol always the same. make it ★
     then RHS of symbol can be anything

     inside symbols, we can have names/namespaces, which are unrestricted except they cannot be symbols (LHS always (★,★)?)
     *)
  
  (* how an op moves constructors[...+inductive instances] from zero or more places to zero or more places, leaving them "empty" *)
  (*  *)

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

  (* Reified Inductive Constructor / Type *)
  Inductive Name := name_base | name_branch (_ _:Name).
  (* TODO... *)
  Fixpoint name_f n := match n with name_base => ★ | name_branch a b => (name_f a, name_f b) end.
  Inductive Symbol := symbol (_ : Name).
  Inductive Object := object (symbol : Symbol) (args : list Object).
  Inductive Ric := ric { name : Name ; ric_base : list (list Ric) ; ric_num_recursive : nat }.
  Definition Rit := list Ric.

  Definition Ready (n : Name) : Object := object (symbol ()).
  Definition Step (n m : Name) : Rewrite := [[★!, [(name_f n)!, _]], ].
  Inductive RicNamespaces.

  Inductive Process := {

    }.
  
  Definition RitProcess (n : Name) : list Rewrite :=.
    (* lifecycle begins by changing the starting-data-root to an instance of this Process, at the initial state; it can then receive constructors?

    typical process:
    received branch : "start" left subtree, enter state delegating to that.
    in "delegate to #n" and subtree n is that process's output type (distinct from its process type): start next / finish (only if you have no current input! having current input is an error/deadend.)
    received atom : finish

    starting a process expects preexisting state to be right type (including "nonexistent")

     *)
    (* for each [child] and constructor, "move constructor into child
    [child] = subprocess we may delegate a subtree of the input into, likely ourselves
     *)
    (*  *)
    (* RitProcess P (e.g. "build Rit"/"destroy Rit"),
      for each constructor C,
        (C=>P,init),d0 => (_=>P,(C,#A0)),d1 and d0->d1 is "start C" (e.g. empty -> C shape containing empties, nop)
        for each argument A to C of type T, with subprocess Q:T->U,
          (_=>P,(C,A),(..,(T,d0),..) =>,(..,((_=>Q,init),d0),..)
          for each constructor D,
            (D=>P,(C,A),(..,(_=>?),..) => (_=>P,(C,A)),(..,(D=>?),..)
          (_=>P,(C,A)),(..,((_=>Q,finished),d1),..) => (_=>P,(C,A+1)),(..,(T,d1),..)
        (_=>P,(C,#An)),d0 => (_=>P,finished),d1 and d0->d1 is "finish C" (e.g. nop, C shape containing empties -> empty)

      note that "start C" and "start first arg of C" could be merged into 1 step, and same for "finish C",
      and for no-args, "start C" and "finish C" could be merged
      *)
        
(* End ImplementingVariablesViaRewrites. *)

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