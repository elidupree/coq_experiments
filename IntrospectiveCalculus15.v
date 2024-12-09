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
  Class CState C := {
        CsMayBeAny : C -> Prop
      ; CsMayBeBranch : C -> C -> C -> Prop
    }.
  
  
  Inductive Context := c_cons {
    c_S : Type
    ; c_CS :: CState c_S
    ; c_root : c_S }.

  
  (* Inductive CorrespondingBranch B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (bl br : B) (s : S) : Prop :=
    cb_cons sl sr : CsMayBeBranch s sl sr -> paired bl sl -> paired br sr -> CorrespondingBranch paired bl br s. *)
  Inductive AnySatisfied B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (b : B) : Prop :=
    cb_cons : CsMayBeAny b -> AnySatisfied paired b.

  Inductive BranchSatisfied B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (b : B) (sl sr : S) : Prop :=
    | bs_any : CsMayBeAny b -> BranchSatisfied paired b sl sr
    | bs_branch bl br : CsMayBeBranch b bl br -> paired bl sl -> paired br sr -> BranchSatisfied paired b sl sr.
  
  CoInductive ValidSpecialization B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) : Prop := {
      (* vs_branches_agree : ∀ b bl br s, paired b s -> CsMayBeBranch b bl br -> CorrespondingBranch paired bl br s ;  *)
      vs_anys_satisfied : ∀ b s, paired b s -> CsMayBeAny s -> CsMayBeAny b ; 
      vs_branches_satisfied : ∀ b s sl sr, paired b s -> CsMayBeBranch s sl sr -> BranchSatisfied paired b sl sr ; 
      vs_injective : ∀ b s1 s2, paired b s1 -> paired b s2 -> ∃ p2, ValidSpecialization p2 ∧ p2 s1 s2
    }.
  
  Section Properties.
    Lemma eq_valid B {BC : CState B} : ValidSpecialization eq.
      cofix Q; constructor.
      {
        intros. destruct H; assumption.
      }
      {
        intros. destruct H. eapply bs_branch. eassumption. all: reflexivity.
      }
      {
        intros. destruct H, H0. exists eq. split. assumption. reflexivity.
      }
    Qed.

  End Properties.
End Context.

(****************************************************
                Concrete ContextSets
****************************************************)
Section ConcreteCSes.
  Inductive PushL (Cs : Context) : Context :=
    pushL_cons lr l r : IsBranch lr l r -> Cs l -> PushL Cs lr.

  Inductive PullR (Cs : Context) : Context :=
    pullR_cons lr l r : ACIsBranch lr l r -> Cs lr -> PullR Cs r.

  Section Properties.
    Lemma PushL_valid Cs : CsValid Cs -> CsValid (PushL Cs).
      intro csv.
      constructor.
      intros c s is_spec Pc.
      destruct Pc.


      destruct c as (V, c). destruct s as (W, s).
      destruct is_spec as (values, H).
      destruct H;
      (* var lr isn't branch *) [admit|].
      (* remember {| c_Var := V; c_Form := c |}. *)
      dependent destruction Pc.
      dependent destruction H3.
      (* CIsBranch-unique: *)
      replace lc with l in *; [|admit].
      replace rc with r in *; [|admit].
      clear H3.
      epose (csv_includes_specializations _ (ac_cons ls) _ H4) as ic2; clearbody ic2.
      (* injection Heqa. *)
      apply pushL_cons with (ac_cons ls) (ac_cons rs).
      constructor; assumption.
      assumption.
      Unshelve.
      econstructor; eassumption.


      intro csv.
      constructor.
      intros CA CB is_spec pA.
      destruct pA.
      destruct CB. cbv delta [ac]. destruct c_Form0.
      (* change (PushL Cs (ac c_root0)). *)
      (* compute in is_spec. *)
      destruct is_spec.

      destruct H2;
      (* var lr isn't branch *) [admit|].
      (* apply pushL_cons. *)
      change (PushL Cs (ac c_root0)).
      apply pushL_cons with _ (specialization_cs values) (inl alone) l1 r1.
      assumption.
      (* branch-uniqueness and ceq-trans *) admit.
      apply csv_includes_specializations with (ac alone).
      unfold IsAnySpecialization, ac.
      apply ias_cons with (λ v, inr (values v)).
      (* ceq_refl *) admit.
      assumption.
    Qed.
  End Properties.
End ConcreteCSes.