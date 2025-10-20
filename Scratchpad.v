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

Parameter OpaqueFormula : Prop.
Parameter q_0 : OpaqueFormula.
Parameter q_S : OpaqueFormula -> OpaqueFormula.

(* Definition ZeroOrSucc q := ∀ C, (q = q_0 -> C) -> (∀ p, q = (q_S p) -> C) -> C.  *)
(* Definition InductiveNat n : Prop :=
  ∀ (P : OpaqueFormula → Prop)
    (zero_case : P q_0)
    (succ_case : ∀ m, P m → P (q_S m)),
    P n. *)
(* Definition CoinductiveNat n :=
  ∀ C, (∀ State, State -> ()) -> C. *)
Parameter OpaqueEq : OpaqueFormula -> OpaqueFormula -> Prop.
Parameter oeq_refl : ∀ q, OpaqueEq q q.

Definition HigherDestructAllCases q
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop) :=
  ((OpaqueEq q q_0) -> ZeroCase q) ∧
  (∀ p, (OpaqueEq q (q_S p) -> (SuccCase p q))).
Definition HigherDestruct0 := ∀
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop),
  ZeroCase q_0 -> HigherDestructAllCases q_0 ZeroCase SuccCase.
Definition HigherDestructS p := ∀
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop),
  (SuccCase p (q_S p)) -> HigherDestructAllCases (q_S p) ZeroCase SuccCase.


(* Definition IsSucc Sn n :=
  ∀ P, P (q_S n) -> P Sn.
Definition PredsAre (P : OpaqueFormula -> Prop) m :=
  ∀ p, IsSucc m p -> P p.  *)

(* Lemma ind_pred n : (∀ n, InductiveNat n -> HigherDestruct n) -> InductiveNat (q_S n) -> InductiveNat n.
  intros hd iSn.
  unfold InductiveNat; intros.
  apply (iSn (λ m, InductiveNat m ∧ ∀ p (is_succ : OpaqueEq m (q_S p)), InductiveNat p)).

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
  apply oeq_refl.
  assumption.
  assumption.
Qed. *)


Definition StrictInductiveNat n : Prop :=
  ∀ (P : OpaqueFormula → Prop)
    (zero_case : HigherDestruct0 -> P q_0)
    (succ_case : ∀ m, HigherDestructS m -> P m → P (q_S m)),
    P n.

Lemma sind_0 : HigherDestruct0 -> StrictInductiveNat q_0.
  unfold StrictInductiveNat; intros; apply zero_case; assumption.
Qed.

Lemma sind_S n : HigherDestructS n -> StrictInductiveNat n -> StrictInductiveNat (q_S n).
  unfold StrictInductiveNat; intros; apply succ_case. assumption. apply H0; assumption.
Qed.

Lemma sind_pred n : StrictInductiveNat (q_S n) -> StrictInductiveNat n.
  intros  iSn.
  unfold StrictInductiveNat; intros.
  apply (iSn (λ m, StrictInductiveNat m ∧ ∀ p (is_succ : OpaqueEq m (q_S p)), StrictInductiveNat p)); trivial.
  
  {
    split.
    { apply sind_0; assumption. }
    
    intros.
    apply (H (λ _, True) (λ p _, StrictInductiveNat p)).
    exact I.
    assumption.
  }
  {
    split; destruct H0.
    { apply sind_S; assumption. }
    
    intros.
    apply (H (λ _, False) (λ p _, StrictInductiveNat p)); assumption.
  }
  { apply oeq_refl. }
Qed.



Parameter OpaqueIsZero : OpaqueFormula -> Prop.
Parameter oi0 : OpaqueIsZero q_0.
Parameter OpaqueIsSucc : OpaqueFormula -> OpaqueFormula -> Prop.
Parameter oiS : ∀ p, OpaqueIsSucc p (q_S p).

Definition FulfillsAllApplicableCases q
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop) :=
  (OpaqueIsZero q -> ZeroCase q) ∧
  (∀ p, OpaqueIsSucc p q -> SuccCase p q).

(* "ZeroCase q_0 ->" can easily be changed to "∀ q, OpaqueIsZero q -> ZeroCase q ->", which should allow StrictInductiveNat2 to use OpaqueIsZero instead of q_0, etc. *)
Parameter FulfillsZero_FulfillsAll : ∀
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop),
  ZeroCase q_0 -> FulfillsAllApplicableCases q_0 ZeroCase SuccCase.
Parameter FulfillsSucc_FulfillsAll : ∀ p 
  (ZeroCase : OpaqueFormula -> Prop)
  (SuccCase : OpaqueFormula -> OpaqueFormula -> Prop),
  (SuccCase p (q_S p)) -> FulfillsAllApplicableCases (q_S p) ZeroCase SuccCase.

Definition StrictInductiveNat2 n : Prop :=
  ∀ (P : OpaqueFormula → Prop)
    (zero_case : P q_0)
    (succ_case : ∀ p, P p → P (q_S p)),
    P n.

Lemma sind2_0 : StrictInductiveNat2 q_0.
  unfold StrictInductiveNat2; intros; apply zero_case; assumption.
Qed.

Lemma sind2_S p : StrictInductiveNat2 p -> StrictInductiveNat2 (q_S p).
  unfold StrictInductiveNat2; intros.  apply succ_case.
  apply H; assumption.
Qed.

Lemma sind_pred2 n : StrictInductiveNat2 (q_S n) -> StrictInductiveNat2 n.
  intros iSn.
  (* unfold StrictInductiveNat2; intros. *)
  apply (iSn (λ m, StrictInductiveNat2 m ∧ ∀ p (is_succ : OpaqueIsSucc p m), StrictInductiveNat2 p)); trivial.
  
  {
    split.
    { apply sind2_0; assumption. }
    
    intros.
    apply (FulfillsZero_FulfillsAll (λ _, True) (λ p _, StrictInductiveNat2 p)).
    exact I.
    assumption.
  }
  {
    split; destruct H.
    { apply sind2_S; assumption. }
    
    intros.
    apply (FulfillsSucc_FulfillsAll p (λ _, False) (λ p _, StrictInductiveNat2 p)); assumption.
  }
  { apply oiS. }
Qed.


Definition StrictInductiveSuccIsNat n : Prop :=
  ∀ (N : OpaqueFormula → Prop) (SiN : OpaqueFormula → Prop)
    (zero_case : N q_0)
    (succ_case : ∀ p, N p → N (q_S p))
    (succ_is_nat_case : ∀ p, N (q_S p) → SiN p),
    SiN n.

Lemma sind_pred3 n : StrictInductiveSuccIsNat n -> StrictInductiveNat2 n.
  intros.
  apply H with StrictInductiveNat2.
  { apply sind2_0. }
  { apply sind2_S. }
  { apply sind_pred2. }
Qed.

Definition NatRules (N : OpaqueFormula → Prop) : Prop := N q_0 ∧ ∀ p, N p → N (q_S p).
Definition SuccIsNatRules (N SiN : OpaqueFormula → Prop) : Prop := NatRules N ∧ ∀ p, N (q_S p) → SiN p.

(* result of simply stripping a q_S from each conclusion of NatRules (which elimates the impossible zero case) *)
Definition NatOfQSRules (N N2 : OpaqueFormula → Prop) : Prop := ∀ p, N p → N2 p.

Definition StrictInductiveNat3 n : Prop :=
  ∀ (N : OpaqueFormula → Prop), NatRules N -> N n.

Parameter InductiveNatsRespectSymbolMatching :
  ∀ p,
    StrictInductiveNat3 (q_S p)
    ->
    (∀ N N2, NatRules N -> NatOfQSRules N N2 -> N2 p).

Definition StrictInductiveNat3_0 : StrictInductiveNat3 q_0 :=
  (λ N (NN : NatRules N),
      proj1 NN).
Definition StrictInductiveNat3_succ p : StrictInductiveNat3 p -> StrictInductiveNat3 (q_S p) :=
  λ (Pn : StrictInductiveNat3 p),
    (λ N (NN : NatRules N),
      proj2 NN p (Pn N NN)).

(* this proof is a bit messy but it works to enact the purpose (showing that it's provable with no magic except a single use of InductiveNatsRespectSymbolMatching in the relevant case) *)
Lemma sind_pred4 n : StrictInductiveSuccIsNat n -> StrictInductiveNat3 n.
  intros Premise.
  red in Premise.
  apply Premise with StrictInductiveNat3.
  { intros p H. apply H. }
  Show Proof.
  { intros p H N H2. apply H2. apply H. split. apply H2. apply H2. }
  { intros p H. pose (InductiveNatsRespectSymbolMatching p H). intros N2 NN2. apply p0 with N2. apply NN2. red. trivial. }
Defined.
Definition sind_pred4_reduced := Eval compute in sind_pred4.
Print sind_pred4.
Print sind_pred4_reduced.

Definition sind_pred4_reduced_manually n : StrictInductiveSuccIsNat n -> StrictInductiveNat3 n :=
  λ (Premise : StrictInductiveSuccIsNat n),
  Premise

    (* "we claim both N and SiN can just be the type of inductive naturals" *)
    StrictInductiveNat3
    StrictInductiveNat3

    (* zero case: *)
    StrictInductiveNat3_0

    (* succ case: *)
    StrictInductiveNat3_succ

    (* SiN case: *)
    (λ p (Pn : StrictInductiveNat3 (q_S p)),
      (λ N (NN : NatRules N),
        (InductiveNatsRespectSymbolMatching p Pn)
          N N
          NN
          (λ p2 P2n, P2n))).


Definition ONatRules (N : OpaqueFormula → Prop) : Prop := (∀ z, OpaqueIsZero z → N z) ∧ (∀ p q, OpaqueIsSucc p q → N p → N q).
(* result of rewriting ONatRules on two sets:
  * in ONatRules, the idea is to say when "N obeys the rules of natural numbers", by saying exactly when it forces a number to count as a natural based on others
  * in OSuccsAreNatRules, we restrict this to exactly when ONatRules force *a number's successors* to obey the rules of natural numbers, based on what numbers count as naturals. This eliminates all cases that require OpaqueIsZero, because no number's successors are guaranteed to all be zero. *)
Definition OSuccsAreNatRules (N SiN : OpaqueFormula → Prop) : Prop := ONatRules N ∧ ∀ p, N p → SiN p.

Definition StrictInductiveNat4 n : Prop :=
  ∀ (N : OpaqueFormula → Prop), ONatRules N -> N n.

Definition StrictInductiveNat4_0 z : OpaqueIsZero z -> StrictInductiveNat4 z :=
  (λ zz N (NN : ONatRules N),
      proj1 NN z zz).

Definition StrictInductiveNat4_succ p q : OpaqueIsSucc p q -> StrictInductiveNat4 p -> StrictInductiveNat4 q :=
  λ pqs (Pn : StrictInductiveNat4 p),
    (λ N (NN : ONatRules N),
      proj2 NN p q pqs (Pn N NN)).

(* OPredOfNatRules differs from OSuccsAreNatRules in that it produces a result exactly when there *exists* a natural number that is the successor of this predecessor, not merely when *all* successors of it are nats. (Due to the concrete rules of natural numbers, it happens to be that this is "stricter" rather than "orthogonal".) *)
Definition OPredOfNatRules (N PoN : OpaqueFormula → Prop) : Prop := ONatRules N ∧ ∀ p q, OpaqueIsSucc p q → N q → PoN p.

Definition StrictInductiveSuccsAreNat4 n : Prop :=
  ∀ (N SiN : OpaqueFormula → Prop), OSuccsAreNatRules N SiN -> SiN n.
Definition StrictInductivePredOfNat4 n : Prop :=
  ∀ (N SiN : OpaqueFormula → Prop), OPredOfNatRules N SiN -> SiN n.

Parameter InductiveNatsRespectSymbolMatching4 :
  ∀ p q, OpaqueIsSucc p q ->
    StrictInductiveNat4 q
    ->
    StrictInductiveSuccsAreNat4 p.

Definition sind_pred5_reduced_manually n : StrictInductivePredOfNat4 n -> StrictInductiveNat4 n :=
  λ (Premise : StrictInductivePredOfNat4 n),
  Premise

    (* "we claim both N and SiN can just be the type of inductive naturals" *)
    StrictInductiveNat4
    StrictInductiveNat4

    (conj
      (conj
        StrictInductiveNat4_0
        StrictInductiveNat4_succ)

      ((λ p q pqs (qn : StrictInductiveNat4 q),
      (λ N (NN : ONatRules N),
        (InductiveNatsRespectSymbolMatching4 p q pqs qn)
          N N
          (conj NN
          (λ p2 P2n, P2n))))))
    .



CoInductive FunctionType :=
  ft : (FunctionType -> Prop) -> FunctionType -> FunctionType.

CoInductive ASet T : Type :=
  | as_nil : ASet T
  | as_branch : T -> ASet T -> ASet T -> ASet T.
Arguments as_nil {T}.
Arguments as_branch [T].
CoInductive FunctionType :=
  ft : (ASet FunctionType) -> FunctionType -> FunctionType.
(* Parameter FunctionType : Type. *)
Definition FunctionTypes := ASet FunctionType.
(* Parameter ft : (FunctionType -> Prop) -> FunctionType -> FunctionType. *)

Inductive ASContains [T] : ASet T -> T -> Prop :=
  | asc_here t l r : ASContains (as_branch t l r) t
  | asc_l t h l r : ASContains l t -> ASContains (as_branch h l r) t
  | asc_r t h l r : ASContains r t -> ASContains (as_branch h l r) t.
(* Definition Props := Prop -> Prop. *)
Definition EnvIncludes (Superset Subset : FunctionTypes) := (∀ p, ASContains Subset p -> ASContains Superset p).
Definition CanApplyInEnv (A : FunctionTypes) (B : FunctionType) (env : FunctionTypes) := EnvIncludes env A -> ASContains env B.
Definition CanApplyAnyInEnv (Fs : FunctionTypes) env := (∀ A B, ASContains Fs (ft A B) -> CanApplyInEnv A B env).

(* Inductive Proof (Rules : FunctionTypes) (Premises : FunctionTypes) (Conclusion : FunctionType) : Type :=
  | atr_premises : ASContains Premises Conclusion -> Proof Rules Premises Conclusion
  | atr_chain Idx (ts : Idx -> FunctionType) : ASContains Rules (ft (aset ts) Conclusion) -> (∀ (idx:Idx), Proof Rules Premises (ts idx)) -> Proof Rules Premises Conclusion. *)
(* Record AnyAppTree : Type := { aat_ft : FunctionType ; aat_at : AppTree aat_ft }. *)
(* Definition Proof (Rules : FunctionTypes) (Premises : FunctionTypes) (Conclusion : FunctionType) := ∀ env, EnvIncludes env Premises -> CanApplyAnyInEnv Rules env -> ASContains env Conclusion. *)
CoFixpoint AllFunctionTypes : FunctionTypes :=
  as_branch (as_nil) (as_branch ) ().
CoFixpoint OneStep (Rules : FunctionTypes) (Context : FunctionTypes) : FunctionTypes :=
  match Context with
  | as_nil => as_nil
  | as_branch t l r => as_branch t (OneStep Rules l) (OneStep Rules r)
  end.
  
(* Record AnyProof (Rules : FunctionTypes) := { ap_Premises : FunctionTypes ; ap_Conclusion : FunctionType ; ap_prf : Proof Rules ap_Premises ap_Conclusion }.
Arguments ap_Premises [Rules].
Arguments ap_Conclusion [Rules]. *)
(* Definition ap_ft [Rules] (p : AnyProof Rules) : FunctionType := ft (ap_Premises p) (ap_Conclusion p). *)
Definition Star : FunctionTypes -> FunctionTypes -> FunctionTypes :=
  λ (Rules Inputs : FunctionTypes), aset (λ (p : AnyProof Rules), ap_ft p).

Inductive MPPremises A B : FunctionTypes :=
  | mpp1 : MPPremises A B (ft A B)
  | mpp2 a : A a -> MPPremises A B a.

Inductive MP : FunctionTypes :=
  | mp A B : MP (ft (MPPremises A B) B).

Definition MPStar := Star MP.

(* "set of function types" is (Prop -> Prop) I guess
Set := (Prop -> Prop)
CanApplyInEnv f env := ∀ v, env v -> env (f v)
CanApplyAnyInEnv Functions env := (∀ f, Functions f -> CanApplyInEnv f env)
* : Set -> Set -> Set
* :=
  λ (Functions : Set), λ (Inputs : Set), λ (Output : Prop), ∀ env, env Inputs -> CanApplyAnyInEnv f env -> env Output *)

Definition SetOfTypes := Prop -> Prop.
Definition MemberOfEach (S : SetOfTypes) : Prop := ∀T, S T -> T.