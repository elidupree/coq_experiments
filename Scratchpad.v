(* Set Implicit Arguments.
Set Asymmetric Patterns. *)
Require Import Unicode.Utf8.

CoInductive MaybeNat :=
  | mn_0 : MaybeNat
  | mn_S : MaybeNat -> MaybeNat.
Inductive LegitNat : MaybeNat -> Prop :=
  | legit_0 : LegitNat mn_0
  | legit_S n : LegitNat n -> LegitNat (mn_S n).

Print LegitNat_ind.
Lemma legit_pred n : LegitNat (mn_S n) -> LegitNat n.
  intro lSn.
  apply (@LegitNat_ind (λ m, ∀ p, (m = mn_S p) -> LegitNat p)) with (mn_S n); intros.
  discriminate.
  injection H1 as <-; assumption.
  assumption.
  reflexivity.
  
  Show Proof.
Defined.

Definition lp_reduced := Eval cbv -[LegitNat_ind] in legit_pred.
Print lp_reduced.

Definition lp_reduced_manual n : LegitNat (mn_S n) -> LegitNat n.
refine (
  λ lSn,
    (LegitNat_ind
      (λ m, ∀ p , m = mn_S p → LegitNat p)
      (λ p (H : mn_0 = mn_S p),
        match H in (_ = a)
          return match a with
          | mn_0 => True
          | mn_S _ => (LegitNat p)
          end
        with eq_refl => I end
        )

      (λ m (lm : LegitNat m)
        (IH : ∀ p, m = mn_S p → LegitNat p)
        p (H : mn_S m = mn_S p),
        match
          match H in (_ = a)
            return (match a with mn_0 => False | mn_S m2 => m = m2 end)
            with eq_refl => eq_refl
          end
          in (_ = a) return (LegitNat a) with
          | eq_refl => lm
        end)
        
      (mn_S n)
      lSn
    )
    n eq_refl).
Defined.

Parameter OpaqueFormula : Type.
Parameter q_0 : OpaqueFormula.
Parameter q_S : OpaqueFormula -> OpaqueFormula.

Definition ZeroOrSucc q := ∀ C, (q = q_0 -> C) -> (∀ p, q = (q_S p) -> C) -> C. 
Definition InductiveNat n :=
  ∀ (P : OpaqueFormula → Prop)
    (zero_case : P q_0)
    (succ_case : ∀ m, P m → P (q_S m)),
    P n.
Definition CoinductiveNat n :=
  ∀ C, (∀ State, State -> ()) -> C.
Parameter weaklyEqual : OpaqueFormula -> OpaqueFormula -> Prop.
Parameter weq_refl : ∀ q, weaklyEqual q q.

Definition HigherDestruct q := ∀ (zero_case : Prop) (succ_case : OpaqueFormula -> Prop), ((weaklyEqual q q_0) -> zero_case) ∧ (∀ p, (weaklyEqual q (q_S p) -> succ_case p)).


Definition IsSucc Sn n :=
  ∀ P, P (q_S n) -> P Sn.
Definition PredsAre (P : OpaqueFormula -> Prop) m :=
  ∀ p, IsSucc m p -> P p. 

Lemma ind_zs_pred n : (∀ n, InductiveNat n -> HigherDestruct n) -> InductiveNat (q_S n) -> InductiveNat n.
  intros hd iSn.
  unfold InductiveNat; intros.
  apply (iSn (λ m, InductiveNat m ∧ ∀ p (is_succ : weaklyEqual m (q_S p)), InductiveNat p)).

  {
    split.
     unfold InductiveNat; trivial.
    
    intros.
    assert (HigherDestruct q_0).
    apply hd; unfold InductiveNat; trivial.
    apply (H True _).
    assumption.
  }
  {
    split.
    { unfold InductiveNat; intros. apply succ_case0.
     destruct H. apply H. assumption. assumption. }
    destruct H.
    intros.
    
    assert (HigherDestruct (q_S m)).
    { apply hd. unfold InductiveNat; intros. apply succ_case0.
     apply H. assumption. assumption. }
    
    apply (H1 False _). assumption.
    
  }
  apply weq_refl.
  assumption.
  assumption.
Qed.


  refine (
    _ (lSn 
      (PredsAre P) _ _)).
  intros.
  apply x; unfold IsSucc; trivial.
  
  {
    unfold PredsAre; intros.
    
  }

  {
  intros.
  apply H.

  }
  intros.
  injection H1 as <-.
  apply
