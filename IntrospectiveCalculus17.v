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
                    Contexts
****************************************************)
Section Context.
  Inductive WhichChild := left | right.
  Definition map_children A B (spec : A -> B) (a : WhichChild -> A) (w : WhichChild) := spec (a w).

  Inductive NodeMeaning C :=
    | or (cs:WhichChild -> C)
    | branch (cs:WhichChild -> C).
    
  Class CState C := {
    cs_meaning : C -> NodeMeaning C
  }.
  
  Inductive Context := c_cons {
    c_S : Type;
    c_CS :: CState c_S;
    c_root : c_S;
  }.
  Global Arguments c_cons {c_S} {c_CS} c_root.

  Definition c_meaning (c : Context) : NodeMeaning Context :=
    let (S,CS,root) := c in
    match cs_meaning root with
      | or cs => or (map_children c_cons cs)
      | branch cs => branch (map_children c_cons cs)
    end.
  
  Instance Context_CS S {CS : CState S} : CState Context := {| cs_meaning := c_meaning |}.
  
  CoInductive Specializes (spec : Context -> Context) : NodeMeaning Context -> NodeMeaning Context -> Prop :=
    | spec_to_or b cs : (∀ w, Specializes spec b (c_meaning (cs w))) -> Specializes spec b (or cs)
    | spec_or_to bs c w : Specializes spec (c_meaning (bs w)) c -> Specializes spec (or bs) c
    | spec_branch_to_branch bs cs : (∀ w, spec (bs w) = (cs w))  -> Specializes spec (branch bs) (branch cs)
    .

  Inductive CImplies a b :=
    | cimp spec : Specializes spec (c_meaning a) (c_meaning b) -> CImplies a b.
    
  Section Properties.

    Lemma imp_refl a : CImplies a a.
      change (CImplies a (id a)).
      apply cimp.
      apply id_vs; assumption.
    Qed.
    
    Instance id_vs : ValidSpecialization id.
      constructor.
      econstructor; [eassumption|reflexivity].
    Qed.

    Definition compose {A B C} (g : B -> C) (f : A -> B) := λ x, g (f x).
    
    Instance vs_trans spec1 spec2 : ValidSpecialization spec1 -> ValidSpecialization spec2 -> ValidSpecialization (compose spec2 spec1).
      constructor.
      intros.
      apply H0 in H1.
      destruct H1.
      apply H in H1.
      destruct H1.

      econstructor; [eassumption|].
      intros. unfold compose. rewrite -> H3. rewrite -> H2. reflexivity.
    Qed.

    Lemma imp_refl a : CImplies a a.
      change (CImplies a (id a)).
      apply cimp.
      apply id_vs; assumption.
    Qed.

    Lemma imp_trans a b c : CImplies a b -> CImplies b c -> CImplies a c.
      destruct 1 as (spec1, V1).
      destruct 1 as (spec2, V2).
      change (spec2 (spec1 a)) with (compose spec2 spec1 a).
      apply cimp.
      apply vs_trans; assumption.
    Qed.
  End Properties.
End Context.

(****************************************************
                Concrete ContextSets
****************************************************)
Section ConcreteCSes.
  Inductive CsNull := cs_null.
  Instance CsNull_CS : CState CsNull := {| CsMayBeBranch := λ c cs, False |}.
  Definition c_null : Context := c_cons cs_null.

  (* Inductive CsAny := 
    cs_any (T:Type) (t:T).
  Instance CsAny_CS : CState CsAny := {| CsMayBeBranch := λ c cs, True |}.
  Definition c_any : Context := c_cons (cs_any tt). *)

  Inductive CsAny := 
    cs_any_at (l : list WhichChild).
  Inductive CsAny_MayBeBranch : CsAny -> (WhichChild -> CsAny) -> Prop :=
    | cambb l : CsAny_MayBeBranch (cs_any_at l) (λ w, (cs_any_at (w::l))).
  Instance CsAny_CS : CState CsAny := {| CsMayBeBranch := λ c cs, False |}.
  Definition c_any : Context := c_cons (cs_any_at nil).

  Section Properties.
    Definition const {A B} (a : A) (b : B) := a.
    Lemma imp_null a : CImplies a c_null.
      change (CImplies a (const c_null a)).
      apply cimp.
      constructor; intros.
      unfold const in H.
      dependent destruction H.
      destruct H.
    Qed.
    
    Lemma imp_any a : CImplies c_any a.
      (* augh! You'd have to exhibit a surjective mapping from any into the other context... which you can't because I didn't claim that anything here is decidable. *)
    Qed.
  End Properties.
End ConcreteCSes.