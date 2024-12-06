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

Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '≡₂' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '∩₂' Q" := (λ x y, P x y ∧ Q x y) (at level 80, right associativity) : type_scope.
Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 85, right associativity) : type_scope.
Reserved Notation "P '≡ₓ' Q" (at level 70, no associativity).


Section Context.
  
  Inductive NodeMeaning V S :=
    | var (v:V)
    | branch (l r:S).
  Arguments var [V] {S}.
  Arguments branch {V} [S].

  Class CState V S := {
    cs_meaning : S -> NodeMeaning V S
  }.

  Inductive NmIsVar V S : NodeMeaning V S -> V -> Prop :=
    | nmiv v : NmIsVar (var v) v.
  Inductive NmIsBranch V S : NodeMeaning V S -> S -> S -> Prop :=
    | nmib l r : NmIsBranch (branch l r) l r.

  Inductive Context V := c_cons {
    c_S : Type
    ; c_CS :: CState V c_S
    ; c_root : c_S }.
  Inductive AnyContext := ac_cons {
    c_Var : Type
    ; c_Form : Context c_Var }.
  Definition CCurried [V] R := ∀ c_S (c_CS : CState V c_S) (c_root : c_S), R.
  Definition ACCurried R := ∀ V c_S (c_CS : CState V c_S) (c_root : c_S), R.
  Definition CUncurry [V] [R] : CCurried R -> Context V -> R := Eval compute in Context_rect _.
  Definition ACUncurry [R] : ACCurried R -> AnyContext -> R := Eval compute in λ P, AnyContext_rect _ (λ V C, (CUncurry (P V) C)).
  Definition ACUncurry2 [R] : @ACCurried (@ACCurried R) -> AnyContext -> AnyContext -> R := Eval compute in λ P Cv, ACUncurry (ACUncurry P Cv).
    
  (* Definition IsVar V (C : Context V) v : Prop :=
    NmIsVar (cs_meaning (c_root C)) v.
  Definition IsBranch V (lr l r : Context V) : Prop :=
    NmIsBranch (cs_meaning (c_root lr)) (c_root l) (c_root r). *)

  Definition IsVarCurried V v S [_C: CState V S] s : Prop :=
    NmIsVar (cs_meaning s) v.
  Definition IsBranchCurried V S [_C: CState V S] lr l r : Prop :=
    NmIsBranch (cs_meaning lr) l r.

  Definition IsVar V v : Context V -> Prop :=
    Context_rect _ (IsVarCurried v).

  (* Inductive Context V := c_cons {
    c_S : Type
    ; c_CS : CState V c_S
    ; c_root : c_S }. *)
  (* CoInductive CEquiv V (a b : Context V) : Prop :=
    | ceq_var v : IsVar a v -> IsVar b v -> CEquiv a b
    | ceq_branch la lb ra rb :
      IsBranch a la ra -> IsBranch b lb rb ->
      CEquiv la lb -> CEquiv ra rb -> CEquiv a b. *)
  CoInductive CEquivCurried [V S1] [_C1 : CState V S1]
    (s1 : S1) [S2] [_C2 : CState V S2] (s2 : S2) : Prop :=
    | ceq_var v : IsVarCurried v s1 -> IsVarCurried v s2 -> CEquivCurried s1 s2
    | ceq_branch l1 r1 l2 r2 :
      IsBranchCurried s1 l1 r1 -> IsBranchCurried s2 l2 r2 ->
      CEquivCurried l1 l2 -> CEquivCurried r1 r2 -> CEquivCurried s1 s2
      .
  (* Notation "P '≡ₓ' Q" := (CEquivCurried P Q) (at level 70, no associativity) : type_scope. *)

  (* There are several different ways we could express this…
    `values` can either be (V -> Context W), or (V -> SC) for some third state-type C, or technically even (V -> SB) - but in that last approach,you'd be tempted to say `=` instead of `CEquiv`, and that doesn't work because _CB may have different states that express the same meaning, and still has to count as a specialization in that case. *)
  CoInductive IsSpecializationCurried V SA [_CA : CState V SA] sa W SB [_CB : CState W SB] sb (values : V -> Context W) : Prop :=
    | iss_var v : IsVarCurried v sa -> CUncurry (CEquivCurried sb) (values v) -> IsSpecializationCurried sa sb values
    | iss_branch (la ra : SA) (lb rb : SB) :
      IsBranchCurried sa la ra -> IsBranchCurried sb lb rb ->
      IsSpecializationCurried la lb values ->
      IsSpecializationCurried ra rb values ->
      IsSpecializationCurried sa sb values.
  
  (* Inductive IsAnySpecialization V W (Cv : Context V) (Cw : Context W) : Prop := *)
  Inductive IsAnySpecializationCurried V SA [_CA : CState V SA] sa W SB [_CB : CState W SB] sb : Prop :=
    | ias_cons values : IsSpecializationCurried sa sb values -> IsAnySpecializationCurried sa sb.

  Definition IsAnySpecialization : AnyContext -> AnyContext -> Prop :=
    ACUncurry2 (@IsAnySpecializationCurried).

(* 
  Definition meaning_map [V S T] (f : S -> T) (m : NodeMeaning V S) : NodeMeaning V T :=
    match m with
    | var w => var w
    | branch l r => branch (f l) (f r)
    end.

  Instance specialization_cs
    V W Sb Sv [_Cb : CState V Sb] [_Cv : CState W Sv] (values : V -> Sv)
    : CState W (Sb + Sv)
    := { cs_meaning := λ S : Sb + Sv,
          match S with
          | inl s => match cs_meaning s with
            | var v => meaning_map inr (cs_meaning (values v))
            | branch l r => branch (inl l) (inl r)
            end
          | inr s => meaning_map inr (cs_meaning s)
          end
      }.
   *)

  (* Definition specialize
    V W Sb Sv [_Cb : CState V Sb] [_Cv : CState W Sv] (values : V -> Sv)
    (s : Sb) := inl s. *)
    
  
  Definition ContextSet := AnyContext -> Prop.

  Class CsValid (Cs : ContextSet) := {
        csv_includes_specializations :
          ∀ CA CB, IsAnySpecialization CA CB -> Cs CA -> Cs CB
      }.

  (* Class CsValid (Cs : ContextSet) := {
        csv_includes_specializations :
          ∀ V W Sb Sv Sc
            (_Cb : CState V Sb) (_Cv : CState W Sv) (_Cc : CState W Sc)
            (values : V -> Sv)
            (sb:Sb) (sc:Sc),
            (* let _adfd : CState W (Sb + Sv) := specialization_cs values in *)
            (@CEquiv _ _ _ _ (specialization_cs values) sc (inl sb)) ->
            Cs V Sb _Cb sb -> Cs W Sc _Cc sc
      }. *)
  
  
    
    
    

  Section AbandonedApproaches.
    (* .
      constructor.
      destruct 1.
      destruct (cs_meaning s).
      destruct (cs_meaning (Values v)).
      exact (var v0).
      exact (branch (inr l) (inr r)).
      exact (branch (inl l) (inl r)).
      destruct (cs_meaning s).
      exact (var v).
      exact (branch (inr l) (inr r)).
  Defined.
  Print specialization_cs. *)


    (* Inductive WhichChild := wc_left | wc_right.
    Definition Location := list WhichChild.
    Bind Scope list_scope with Location.
    Notation "'𝕃'" := wc_left.
    Notation "'ℝ'" := wc_right.
    Hint Extern 5 => progress change (list WhichChild) with Location in *; shelve : simplify. *)

    (* CoInductive Context V :=
      | c_var (v:V)
      | c_branch (l r : Context V)
      . *)

    (* Fixpoint InContext V (C : Context V) (x : Location) (v : V) : Prop :=
      match (x, C) with
      | (nil, c_var v) => True
      | (𝕃::x, c_branch l r) => InContext l x v
      | (ℝ::x, c_branch l r) => InContext r x v
      | _ => False
      end.
    
    Definition CEquiv V (C D : Context V) : Prop :=
      InContext C ≡₂ InContext D. *)
    (* Notation "P '≡ₓ' Q" := (CEquiv P Q) (at level 70, no associativity) : type_scope. *)
    
    (* CoFixpoint specialize V (C : Context V) W (values : V -> Context W) :=
      match C with
      | c_var v => values v
      | c_branch l r => c_branch (specialize l values) (specialize r values)
      end. *)
    
    (* Definition ContextSet := ∀ V, Context V -> Prop. *)
(*     
    Class CsValid (Cs : ContextSet) := {
        csv_includes_specializations :
          ∀ V (Cv : Context V) W (values : V -> Context W) (Cw : Context W),
            (Cw ≡ₓ specialize Cv values) -> Cs _ Cv -> Cs _ Cw
      }.

    Definition ConformsTo (x y : Location) : ContextSet :=
      λ V C, ∀ m d e, MemberAtLinealRelation (C m) x d e -> MemberAtLinealRelation (C m) y d e. *)
  End AbandonedApproaches.
End Context.