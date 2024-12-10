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
Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 85, right associativity) : type_scope.
Notation "P '⊆' Q" := (∀ x, P x -> Q x) (at level 70, no associativity) : type_scope.
Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Inductive UnionX2 T (Rs : (T -> T -> Prop) -> Prop) (x y : T) : Prop :=
  u2_cons R : Rs R -> R x y -> UnionX2 Rs x y.
Notation "'⋃₂' Rs" := (UnionX2 Rs) (at level 200, right associativity).

Section Context.
  Inductive WhichChild := left | right.
  Definition map_children A B (map : A -> B) (a : WhichChild -> A) (w : WhichChild) := map (a w).

  Class CState C := {
    CsMayBeBranch : C -> (WhichChild -> C) -> Prop
  }.
  
  Inductive Context := c_cons {
    c_S : Type;
    c_CS :: CState c_S;
    c_root : c_S;
  }.
  Arguments c_cons {c_S} {c_CS} c_root.

  Inductive CMayBeBranch : Context -> (WhichChild -> Context) -> Prop :=
    cmbb S (CS : CState S) s sc : CsMayBeBranch s sc -> CMayBeBranch (c_cons s) (map_children c_cons sc).
  
  Instance Context_CS S {CS : CState S} : CState Context := {| CsMayBeBranch := CMayBeBranch |}.

  Section AbandonedApproaches.
    (* Inductive CorrespondingBranch B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (bl br : B) (s : S) : Prop :=
      cb_cons sl sr : CsMayBeBranch s sl sr -> paired bl sl -> paired br sr -> CorrespondingBranch paired bl br s. *)
    (* Inductive AnySatisfied B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (b : B) : Prop :=
      cb_cons : CsMayBeAny b -> AnySatisfied paired b. *)

    (* Inductive BranchSatisfied B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) (b : B) (sc : WhichChild -> S) : Prop :=
      (* | bs_any : CsMayBeAny b -> BranchSatisfied paired b sl sr *)
      | bs_branch bc : CsMayBeBranch b bc -> (∀ w, paired (bc w) (sc w)) -> BranchSatisfied paired b sc. *)
    (* CoInductive ValidSpecialization B S {BC : CState B} {SC : CState S} (paired : B -> S -> Prop) : Prop := {
        (* vs_branches_agree : ∀ b bl br s, paired b s -> CsMayBeBranch b bl br -> CorrespondingBranch paired bl br s ;  *)
        (* vs_anys_satisfied : ∀ b s, paired b s -> CsMayBeAny s -> CsMayBeAny b ;  *)
        vs_branches_satisfied : ∀ b s sc, paired b s -> CsMayBeBranch s sc -> BranchSatisfied paired b sc ; 
        vs_injective : ∀ b s1 s2, paired b s1 -> paired b s2 -> ∃ p2, ValidSpecialization p2 ∧ p2 s1 s2 ;
      }. *)

    (* | bs_any : CsMayBeAny b -> BranchSatisfied paired b sl sr *)
  End AbandonedApproaches.
  
  Inductive BranchSatisfied (paired : Context -> Context -> Prop) (b : Context) (sc : WhichChild -> Context) : Prop :=
    | branch_satisfied bc : CMayBeBranch b bc -> (∀ w, paired (bc w) (sc w)) -> BranchSatisfied paired b sc.
  
  Class ValidSpecialization (paired : Context -> Context -> Prop) : Prop := {
      vs_branches_satisfied : ∀ b s sc, paired b s -> CMayBeBranch s sc -> BranchSatisfied paired b sc ; 
      vs_injective : ∀ b s1 s2, paired b s1 -> paired b s2 -> paired s1 s2 ;
    }.
  
  Inductive CImplies (b s : Context) : Prop :=
    cimp (paired : Context -> Context -> Prop) : ValidSpecialization paired -> paired b s -> CImplies b s.

  Section Properties.
    Instance eq_vs : ValidSpecialization eq.
      constructor.
      {
        intros. destruct H.
        econstructor; [eassumption|reflexivity].
      }
      {
        congruence.
      }
    Qed.

    Instance vs_max : ValidSpecialization CImplies.
      constructor.
      {
        intros.
        destruct H as (P, PV, Pbs).
        destruct (vs_branches_satisfied _ Pbs H0).
        apply branch_satisfied with bc.
        assumption.
        intro.
        econstructor. eassumption. apply H1.
      }
      {
        intros.
        destruct H as (P1, P1V, P1bs1).
        destruct H0 as (P2, P2V, P2bs2).
      }

    Inductive TransitiveClosure T (R : T -> T -> Prop) : T -> T -> Prop :=
      | tc_single a b
          : R a b -> TransitiveClosure R a b
      | tc_trans a b c :
        TransitiveClosure R a b ->
        TransitiveClosure R b c ->
        TransitiveClosure R a c
        .
    
    Lemma tc_by_steps_from_head T (R : T -> T -> Prop) x w : TransitiveClosure R x w -> ∀ (P : T -> Prop), (∀ y, R x y -> P y) -> (∀ y z, R y z -> P y -> P z) -> P w.
      induction 1; intros.
      apply H0; assumption.
      apply IHTransitiveClosure2; [|assumption].
      intros.
      apply H2 with b. assumption.
      apply IHTransitiveClosure1; assumption.
    Qed.

    Instance tc_spec R : (ValidSpecialization R) -> ValidSpecialization (TransitiveClosure R).
      intro RsV.
      constructor.
      {
        intros b s sc Tbs Cssc.
        revert sc Cssc.
        induction Tbs as [b s P|].
        {
          intros.
          destruct RsV.
          destruct (vs_branches_satisfied0 b s sc); trivial. 
          apply branch_satisfied with bc; trivial.
          intros; apply tc_single; trivial.
        }
        {
          intros cc Cccc.
          destruct (IHTbs2 cc Cccc) as (bc, Cbbc, Pbcsc).
          destruct (IHTbs1 bc Cbbc) as (ac, Caac, Pacbc).
          apply branch_satisfied with ac.
          exact Caac.
          intro. apply tc_trans with (bc w).
          apply Pacbc.
          apply Pbcsc.
        }
      }
      {
        intros b s1 s2 Tbs1 Tbs2.
        induction Tbs1 as [b s1 Rbs1|]; [|tauto].
        (* apply (tc_by_steps_from_head Tbs1); clear s1 Tbs1.
        intros s1 Rbs1.
        apply tc_single.
        apply vs_injective with b. assumption. *)

        apply (tc_by_steps_from_head Tbs2); clear s2 Tbs2.
        {
          intros s2 Rbs2.
          apply tc_single.
          apply vs_injective with b; assumption.
        }
        {
          intros.
          apply tc_trans with y; [|apply tc_single]; assumption.
        }
      }
    Qed.
    Inductive RCompose T (R S : T -> T -> Prop) (x z : T) : Prop :=
      | cr_compose y
          : R x y -> S y z -> RCompose R S x z.
    
    Instance rc_spec R S : ValidSpecialization R -> ValidSpecialization S -> ValidSpecialization (RCompose R S).
      intros RV SV.
      constructor; intros.
      {
        destruct H.
        destruct RV as (RV, _).
        destruct SV as (SV, _).
        destruct (SV _ _ _ H1 H0) as (yc, Cyyc, Sycsc).
        destruct (RV _ _ _ H Cyyc) as (bc, Cbbc, Rbcyc).
        apply branch_satisfied with bc.
        assumption.
        intros.
        split with (yc w).
        apply Rbcyc.
        apply Sycsc.
      }
      {
        destruct H, H0.
        destruct RV as (_, RV).
        destruct SV as (_, SV).
        constructor with y.
        apply RV in H.
      }


    Lemma imp_trans a b c : CImplies a b -> CImplies b c -> CImplies a c.
      destruct 1 as (P1, V1, P1ab).
      destruct 1 as (P2, V2, P2bc).
      apply cimp with (RCompose P1 P2).
      {
        constructor; intros.
        {
          destruct H.
        }
      }
  End Properties.
End Context.

(****************************************************
                Concrete ContextSets
****************************************************)
Section ConcreteCSes.
  Inductive Any :=
    any_at (l : list WhichChild).
  Inductive Any_MayBeBranch (root : Any) : (WhichChild -> Any) -> Prop :=
    | combb s sc : root s -> CsMayBeBranch s sc -> ChoicesOf_MayBeBranch root (λ w, eq (sc w))
  
  Instance ChoicesOf_CS S {CS : CState S} : CState (ChoicesOf S) := {| CsMayBeBranch := @ChoicesOf_MayBeBranch _ _ |}.
  
  Definition ChoicesOf S := (S -> Prop).
  (* Definition ChoicesOf Case S := (Case -> S). *)
  Inductive ChoicesOf_MayBeBranch S {CS : CState S} (root : ChoicesOf S) : (WhichChild -> ChoicesOf S) -> Prop :=
    | combb s sc : root s -> CsMayBeBranch s sc -> ChoicesOf_MayBeBranch root (λ w, eq (sc w))
    .
  Instance ChoicesOf_CS S {CS : CState S} : CState (ChoicesOf S) := {| CsMayBeBranch := @ChoicesOf_MayBeBranch _ _ |}.

  Inductive HasChild (w : WhichChild) S {CS : CState S} (c : S) : S -> Prop :=
    hc cs : CsMayBeBranch c cs -> HasChild w c (cs w).
    
  Definition Pull (w : WhichChild) (c : Context) : Context :=
    let (S,CS,root) := c in
      @c_cons _ _ (HasChild w root).

  Inductive Push (w : WhichChild) S :=
    | push_root
    | push_

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