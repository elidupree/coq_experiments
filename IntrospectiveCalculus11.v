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

(****************************************************
                   Tree structure
****************************************************)

Inductive WhichChild := wc_left | wc_right.
Definition Location := list WhichChild.
Bind Scope list_scope with Location.
Notation "'𝕃'" := wc_left.
Notation "'ℝ'" := wc_right.
Hint Extern 5 => progress change (list WhichChild) with Location in *; shelve : simplify.

Notation "P '⊆' Q" := (∀ x, P x -> Q x) (at level 70, no associativity) : type_scope.
Notation "P '∩' Q" := (λ x, P x ∧ Q x) (at level 80, right associativity) : type_scope.
Notation "P '∪' Q" := (λ x, P x ∨ Q x) (at level 85, right associativity) : type_scope.
Notation "P '≡' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity) : type_scope.
Notation "P '≡2' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.


Definition LSet := Location -> Prop.
Definition LSSet := LSet -> Prop.
Definition LRel := Location -> Location -> Prop.

Inductive AssertedRewrites (S : LSet) : Location -> Location -> Prop :=
  | rewrites x y z : S x -> S y -> AssertedRewrites S (x++z) (y++z).

Definition ARewritesRespectB A B :=
  ∀ x y, (AssertedRewrites A) x y -> B x -> B y.


  (* λ x y, ∀ z w, S (x++z) -> S (y++z). *)
Search (∀ S, (S -> S) -> (S -> Prop) -> (S -> Prop)).
Definition PrefixRewrites (S : LSet) : Location -> Location -> Prop :=
  λ x y, ∀ z w, S (x++z) -> S (y++z).


Inductive SubtreeMap (S : LSet) (d : Location) : LSet :=
  | sm_cons x : S x -> SubtreeMap S d (x++d). 

Infix "++₁" := SubtreeMap (right associativity, at level 60).

Definition UnifiablePairAssuming (Indep : LSSet) (x y : Location)
  := ∀   S   e,   Indep   S -> ( S      (x++e) <->  S      (y++e)).
Definition UnifiablePair (Indep : LSSet) (x y : Location)
  := ∀   S d e,   Indep   S -> ((S++₁d) (x++e) <-> (S++₁d) (y++e)).
Definition UnifiableSet (Indep : LSSet) (U : LSet)
  := ∀ S x y d e, Indep   S -> U x -> U y -> (S++₁d) (x++e) -> (S++₁d) (y++e).

Definition IndepAbleWithRelAssuming (Unified : LRel) (S : LSet)
  := ∀ x y f  , Unified x y ->  (S++₁f)  x ->     (S++₁f)  y.
Definition IndepAbleWithRel (Unified : LRel) (S : LSet)
  := ∀ x y f g, Unified x y ->  (S++₁f) (x++g) -> (S++₁f) (y++g).
Definition IndepAbleWithSets (Unif : LSSet) (S : LSet)
  := ∀ U x y f g, Unif U  -> U x -> U y -> (S++₁f) (x++g) -> (S++₁f) (y++g).

Definition IndepSetPermitsUnifyingSet (S U : LSet)
  := ∀ x y d e, U x -> U y -> (S++₁d) (x++e) -> (S++₁d) (y++e).
Definition UnifiableAllSetVersion (Indep : LSSet) (U : LSet)
  := ∀ S, Indep S -> IndepSetPermitsUnifyingSet S U.
Definition IndepAbleAllSetVersion (Unif : LSSet) (S : LSet)
  := ∀ U, Unif U -> IndepSetPermitsUnifyingSet S U.

  
Definition IndepSetPermitsUnifyingSetUnrolled (S U : LSet)
  := ∀ x y z d e, U x -> U y -> S z -> (z++d) = (x++e) -> ∃ w, S w ∧ (w++d) = (y++e).
Definition IndepSetPermitsUnifyingSetRolled (S U : LSet)
  := ∀ x y d e, (U++₁e) x -> (U++₁e) y -> (S++₁d) x -> (S++₁d) y.

Notation "∀ₛ x ∈ S , P" := (∀ x, S x -> P) (at level 200, x binder, right associativity).

Inductive SubtreeMaps (S : LSet) : LSSet :=
  | sms_cons d : SubtreeMaps S (SubtreeMap S d). 

Definition IndepSetPermitsUnifyingObscured (S U : LSet)
  := ∀ x y,
    ∀ₛ Uᵈ ∈ SubtreeMaps U,
    ∀ₛ Sᵈ ∈ SubtreeMaps S,
    Uᵈ x -> Uᵈ y -> Sᵈ x -> Sᵈ y.


Class IndepSets (Indep : LSSet) := {
  _ : Indep ≡ IndepAble (Unifiable Indep)
}.

Class UnifRel (Unified : LRel) := {
  _ : Unified ≡2 Unifiable (IndepAble Unified)
}.

(* Parameter IUCompatible : LSet -> LSet -> Prop. *)
Definition IUCompatible (I U : LSet)
  := ∀ x y d e, (U++₁e) x -> (U++₁e) y -> (I++₁d) x -> (I++₁d) y.
Definition Unifiable (Indep : LSSet) (U : LSet)
  := ∀ I, Indep I -> IUCompatible I U.
Definition IndepAble (Unif : LSSet) (I : LSet)
  := ∀ U, Unif U -> IUCompatible I U.

Definition IndepUnifCompatible (Indep Unif : LSSet)
  := ∀ I U, Indep I -> Unif U -> IUCompatible I U.

Definition IndepUnifFullyConstraining (Indep Unif : LSSet)
  := IndepUnifCompatible (IndepAble Unif) (Unifiable Indep).
  
Definition IndepMaximal (Indep Unif : LSSet)
  := Indep ≡ IndepAble Unif.

Section IndepUnifAbleProperties.
  (* Variable Indep Unif : LSSet.
  Variable compat : IndepUnifCompatible Indep Unif. *)

  Lemma IndepAble_negative_in_Unif Unif1 Unif2 :
    Unif1 ⊆ Unif2 -> IndepAble Unif2 ⊆ IndepAble Unif1.
    intros UinU I II U UU.
    apply II; apply UinU; assumption.
  Qed.
  Lemma Unifiable_negative_in_Indep Indep1 Indep2 :
    Indep1 ⊆ Indep2 -> Unifiable Indep2 ⊆ Unifiable Indep1.
    intros IinI U UU I II.
    apply UU; apply IinI; assumption.
  Qed.
  Lemma compat_negative_in_Unif Indep Unif1 Unif2 :
    Unif1 ⊆ Unif2 -> IndepUnifCompatible Indep Unif2 -> IndepUnifCompatible Indep Unif1.
    intros UinU compat I U II UU.
    apply (IndepAble_negative_in_Unif _ UinU); trivial.
    intros U0 UU0.
    apply compat; trivial.
  Qed.
  Lemma compat_negative_in_Indep Indep1 Indep2 Unif :
    Indep1 ⊆ Indep2 -> IndepUnifCompatible Indep2 Unif -> IndepUnifCompatible Indep1 Unif.
    intros IinI compat I U II UU.
    apply (Unifiable_negative_in_Indep _ IinI); trivial.
    intros I0 II0.
    apply compat; trivial.
  Qed.

  Lemma Indep_IndepAble Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    : Indep ⊆ IndepAble Unif.
    intros I II U UU.
    apply compat; trivial.
  Qed.
  Lemma Unif_Unifiable Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    : Unif ⊆ Unifiable Indep.
    intros U UU I II.
    apply compat; trivial.
  Qed.

  Lemma IndepAble_stagnates Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    : IndepAble (Unifiable Indep) ⊆ IndepAble Unif.
    apply IndepAble_negative_in_Unif. apply Unif_Unifiable. assumption.
  Qed.

  Lemma IndepAble_stagnates_2 Indep Unif 
    (constrained : IndepUnifFullyConstraining Indep Unif)
    : IndepAble Unif ⊆ IndepAble (Unifiable Indep).
    intros I II U UU.
    apply constrained; assumption.
  Qed.

  Lemma Unifiable_stagnates Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    : Unifiable (IndepAble Unif) ⊆ Unifiable Indep.
    apply Unifiable_negative_in_Indep. apply Indep_IndepAble.
    assumption.
  Qed.

  Lemma Unifiable_stagnates_2 Indep Unif 
    (constrained : IndepUnifFullyConstraining Indep Unif)
    : Unifiable Indep ⊆ Unifiable (IndepAble Unif).
    intros I II U UU.
    apply constrained; assumption.
  Qed.

  Lemma IndepAble_still_compat Indep Unif
    (compat : IndepUnifCompatible Indep Unif)
    : IndepUnifCompatible (IndepAble Unif) Unif.
    (* apply compat_negative_in_Unif with Unif; trivial. *)
    intros I U II UU.
    apply II; assumption.
  Qed.
  Lemma Unifiable_still_compat Indep Unif
    (compat : IndepUnifCompatible Indep Unif)
    : IndepUnifCompatible Indep (Unifiable Indep).
    (* apply compat_negative_in_Indep with Indep; trivial. *)
    intros I U II UU.
    apply UU; assumption.
  Qed.

  Lemma IndepAble_makes_fully_constraining Unif
    : IndepUnifFullyConstraining (IndepAble Unif) Unif.
    intros I U II UU.
    apply UU; assumption.
  Qed.
  Lemma Unifiable_makes_fully_constraining Indep
    : IndepUnifFullyConstraining Indep (Unifiable Indep).
    intros I U II UU.
    apply II; assumption.
  Qed.
  (* Lemma fully_constraining_means_compat Indep Unif 
    (compat : IndepUnifFullyConstraining Indep Unif)
    : IndepUnifCompatible Indep Unif.
    intros I U II UU.
    apply compat.
    apply Indep_IndepAble with Indep; trivial.
    apply Unif_Unifiable. *)

  Lemma IndepAbleUnifiable_indep_stagnates Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    (constrained : IndepUnifFullyConstraining Indep Unif)
    : IndepAble Unif ≡ IndepAble (Unifiable Indep).
    split.
    apply IndepAble_stagnates_2; assumption.
    apply IndepAble_stagnates; assumption.
  Qed.

  Lemma IndepAbleUnifiable_still_compat Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    (constrained : IndepUnifFullyConstraining Indep Unif)
    : IndepUnifCompatible (IndepAble Unif) (Unifiable Indep).
    
    intros I U II UU.
    {
      apply constrained.
      {
        eapply IndepAble_negative_in_Unif; [|exact II].
        trivial.
      }
      {
        eapply Unifiable_negative_in_Indep; [|exact UU].
        trivial.
      }
    }
  Qed.
  Lemma IndepAbleUnifiable_still_constraining Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    (constrained : IndepUnifFullyConstraining Indep Unif)
    : IndepUnifFullyConstraining (IndepAble Unif) (Unifiable Indep).
    
    (* apply IndepAble_still_compat in compat.
    apply Unifiable_still_compat in compat. *)
    
    (* repeat intro. *)
    intros I U II UU.
    {
      apply constrained.
      {
        eapply IndepAble_negative_in_Unif; [|exact II].
        apply Unif_Unifiable; assumption.
      }
      {
        eapply Unifiable_negative_in_Indep; [|exact UU].
        apply Indep_IndepAble; assumption.
      }
    }
  Qed.
    
    repeat intro.
    (* intros I U II UU x y d e Ux Uy H. *)

    apply IndepAble_still_compat in compat.
    (* apply Unifiable_still_compat in compat.
    apply compat; trivial. *)
    repeat intro.

    eapply compat_negative_in_Unif.
    apply Unif_Unifiable.
    eapply Unifiable_still_compat.
    intros; exact H.
    exact compat.

    (* intros I U II UU. *)
    (* eapply compat_negative_in_Unif. apply Unifiable_stagnates. *)
    epose (IndepAble_still_compat _ (Unifiable_stagnates compat) (Unifiable_still_compat Indep _ compat)).
    apply IndepAble_still_compat in compat.
    apply Unifiable_still_compat in compat.
    eapply compat_negative_in_Unif in compat.
    pose (Unifiable_still_compat i) as u.
    apply II; assumption.
  Qed.

  (* Lemma IUCompat_ *)

  Lemma both_extensions_still_compatible Indep Unif 
    (compat : IndepUnifCompatible Indep Unif)
    U I 
    (UU : Unifiable Indep U)
    (II : IndepAble Unif I)
    : IUCompatible I U.

    red; intros. unfold Unifiable, IndepAble in *.

  Lemma Unifiable_cares_not_for_extending_Indep :
    Unifiable (IndepAble Unif) ≡ Unifiable Indep.
    intro U.
    split; [apply Unifiable_idempotent|].
    {
      (* unfold Unifiable. *)
      intros UU I II.
      repeat intro.
      eapply (II _ _).
      exact H.
      exact H0.
      assumption.
    }
  Qed.

  Lemma Indep_subtrees Unif 
    I (II : IndepAble Unif I) d
    : IndepAble Unif (I++₁d).
    intros U UU. 
    apply II in UU.
    intros x y e f Ufx Ufy H.
    unfold IUCompatible in UU.
    (* remember (x0 ++ f). *)
    (* specialize (UU _ _ _ _ H0 H1 H). *)

    (* remember x.
    remember y.
    destruct Ufx.
    destruct Ufy.
    remember (x0 ++ f).
    destruct H.
    remember x2.
    destruct H.
    
    specialize (UU _ _ _ _ (sm_cons _ _ _ H0) (sm_cons _ _ _ H1) (sm_cons _ _ _ H)).
     *)
    remember x.
    destruct H.
    remember x0.
    destruct H.
    specialize (UU ((x1 ++ d) ++ e) y (d ++ e) f Ufx Ufy).
    rewrite <- app_assoc in Heql.
    rewrite <- app_assoc in UU.
    specialize (UU (sm_cons _ _ _ H)).
    destruct UU.
    rewrite app_assoc.
    constructor.
    constructor.
    assumption.
  Qed.

  Lemma Unif_subtrees Indep 
    U (UU : Unifiable Indep U) d
    : Unifiable Indep (U++₁d).
    intros I II. 
    apply UU in II.
    intros x y e f Ufx Ufy H.
    unfold IUCompatible in II.
    remember x.
    destruct Ufx as (x5, Ufx).
    destruct Ufx as (x5, Ufx).
    remember y.
    destruct Ufy as (y5, Ufy).
    destruct Ufy as (y5, Ufy).
    rewrite <- app_assoc in Heql.
    rewrite <- app_assoc in Heql0.
    rewrite <- app_assoc in H.
    specialize (II (x5 ++ d ++ f) (y5 ++ d ++ f) e (d ++ f) (sm_cons _ _ _ Ufx) (sm_cons _ _ _ Ufy) H).
    rewrite <- app_assoc.
    assumption.
  Qed.
