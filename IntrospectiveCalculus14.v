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

Notation "P '⊆' Q" := (∀ x, P x -> Q x) (at level 70, no associativity) : type_scope.
Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '≡' Q" := (∀ x, P x <-> Q x) (at level 70, no associativity) : type_scope.
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
  
  (* CoInductive IsLeftChildUhh V S1 (_C1 : CState V S1) : NodeMeaning V S1 -> ∀ S2, CState V S2 -> S2 -> Prop :=
    ilc_ (l1 r1 : S1) S2 (CL2 : CState V S2) (l2 : S2) : 
    CEquiv l1 l2 -> IsLeftChildUhh (branch l1 r1) CL2 l2. *)


  Inductive NmIsVar V S : NodeMeaning V S -> V -> Prop :=
    | nmiv v : NmIsVar (var v) v.
  Inductive NmIsBranch V S : NodeMeaning V S -> S -> S -> Prop :=
    | nmib l r : NmIsBranch (branch l r) l r.

  Inductive Context V := c_cons {
    c_S : Type
    ; c_CS :: CState V c_S
    ; c_root : c_S }.
  Arguments c_cons {V c_S c_CS}.
  Inductive AnyContext := ac_cons {
    c_Var : Type
    ; c_Form : Context c_Var }.
  (* Arguments ac_cons [V c_S c_CS]. *)
  (* Definition CCurried [V] R := ∀ c_S (c_CS : CState V c_S) (c_root : c_S), R.
  Definition ACCurried R := ∀ V c_S (c_CS : CState V c_S) (c_root : c_S), R.
  Definition CUncurry [V] [R] : CCurried R -> Context V -> R := Eval compute in Context_rect _.
  Definition ACUncurry [R] : ACCurried R -> AnyContext -> R := Eval compute in λ P, AnyContext_rect _ (λ V C, (CUncurry (P V) C)).
  Definition ACUncurry2 [R] : @ACCurried (@ACCurried R) -> AnyContext -> AnyContext -> R := Eval compute in λ P Cv, ACUncurry (ACUncurry P Cv).
  Definition ac [V] [c_S] [c_CS : CState V c_S] (c_root : c_S) := ac_cons (c_cons c_root). *)
    
  (* Definition CIsVar V (C : Context V) v : Prop :=
    NmIsVar (cs_meaning (c_root C)) v.
  Definition CIsBranch V (lr l r : Context V) : Prop :=
    NmIsBranch (cs_meaning (c_root lr)) (c_root l) (c_root r). *)

  Definition IsVarCurried V v S {_C: CState V S} s : Prop :=
    NmIsVar (cs_meaning s) v.
  Definition IsBranchCurried V S {_C: CState V S} lr l r : Prop :=
    NmIsBranch (cs_meaning lr) l r.

  (* Definition CIsVar V v : Context V -> Prop :=
    Context_rect _ (IsVarCurried v).
  Inductive CIsBranch V : Context V -> Context V -> Context V -> Prop :=
    ib_cons S (_C: CState V S) lr l r : IsBranchCurried lr l r -> CIsBranch (c_cons lr) (c_cons l) (c_cons r). *)

  Definition nm_map_states [V S T] (f : S -> T) (m : NodeMeaning V S) : NodeMeaning V T :=
    match m with
    | var w => var w
    | branch l r => branch (f l) (f r)
    end.
    
  Instance cc V : CState V (Context V) := {
      cs_meaning := λ c, let (S, _C, s) := c in
        nm_map_states c_cons (cs_meaning s)
    }.
    (* Eval compute in cc.
    Eval cbv delta [cc c_root nm_map_states] in cc. *)
  
  Definition CIsVar V (v : V) (C : Context V) : Prop := IsVarCurried v C.
  Definition CIsBranch V (lr l r : Context V) : Prop := IsBranchCurried lr l r.
  Inductive ACIsBranch : AnyContext -> AnyContext -> AnyContext -> Prop :=
    acib_cons V (lr l r : Context V) : CIsBranch lr l r -> ACIsBranch (ac_cons lr) (ac_cons l) (ac_cons r).


  CoInductive CPred [V] P (VarCase : V -> P -> Prop) (BranchCase : P -> P -> P -> Prop) (c : Context V) (p : P) : Prop :=
    | cpred_var v : CIsVar v c -> VarCase v p -> CPred VarCase BranchCase c p
    | cpred_branch l r pl pr :
      CIsBranch c l r -> BranchCase p pl pr ->
      (CPred VarCase BranchCase l pl) -> 
      (CPred VarCase BranchCase r pr) ->
      CPred VarCase BranchCase c p
      .
  
  Definition CEquivP [V] : Context V -> Context V -> Prop :=
    CPred (@CIsVar V) (@CIsBranch V).
  Definition IsThisSpecializationP V W (values : V -> Context W) : Context V -> Context W -> Prop :=
    CPred (λ v, CEquivP (values v)) (@CIsBranch W).

  (* the reversed way de-facto requires implementing the state-type of a specialization *)
  (* Definition IsThisSpecializationvP2 V W (values : V -> Context W) : Context W -> Context V -> Prop :=
    CPred (λ v, CEquivP (values v)) (_). *)
    (* ...unless...? *)
    
  (* Definition CEquivs [V] : Context V -> (Context V -> Prop) -> Prop
    (* := *)
    . refine 
    (@CPred _ (Context V -> Prop) (λ v others, others ⊆ @CIsVar V v) (λ lr l r, _)).
    admit.
  Admitted. *)
  Record Specialization V W := specialize { spec_base : Context V ; values : V -> Context W }.
  Inductive SpecsToVar V W : W -> Specialization V W -> Prop :=
    stv v cv w values : CIsVar v cv -> CIsVar w (values v) -> SpecsToVar w (specialize cv values).
  Inductive SpecsToBranch V W : Specialization V W -> Specialization V W -> Specialization V W -> Prop :=
    sib_var cv : CIsVar v cv -> 
    sib_branch lr l r values : CIsBranch lr l r -> SpecsToBranch (specialize lr values) (specialize l values) (specialize r values).
  Definition IsThisSpecializationvP2 V W : Context W -> Specialization V W -> Prop :=
    CPred (@SpecsToVar _ _) (@SpecsToBranch _ _).

  Inductive WhichChild := left | right.

  (* path head starts at subtree *)
  (* Inductive CSubtree V := csubtree (c:Context V) (path:list WhichChild). *)
  Record SpecializationSubtree V W := specsub { specsub_base : Context V ; specsub_values : V -> Context W ; specsub_subtree : list WhichChild }.
  Inductive PathVar V := path_var (path:list WhichChild) (var:V).
  Inductive PvIsVar V : V -> PathVar V -> Prop :=
     pviv v : PvIsVar v (path_var nil v).
  Inductive PvWrapsOneOf V : PathVar V -> PathVar V -> PathVar V -> Prop :=
     pvb_left lr l r lp rp : PvIsVar (path_var (left::lp) lr) (path_var l lp) (path_var r rp).
  Definition VarAt V : PathVar V -> Context V -> Prop :=
    CPred (@PvIsVar _) 
  Inductive VarAt W : W -> list WhichChild -> Context W -> Prop :=
    | va_var w cw : CIsVar w cw -> VarAt w nil cw
    | va_branch w lr l r a : CIsBranch lr l r -> VarAt w a l -> 
    .
  Inductive SpecSubsToVar V W : W -> SpecializationSubtree V W -> Prop :=
    | sstv_var v cv w values : CIsVar v cv -> CIsVar w (values v) -> SpecSubsToVar w (specsub cv values nil)
    | sstv_left lr l r w values a : CIsBranch lr l r ->
      SpecSubsToVar w (specsub l values a) ->
      SpecSubsToVar w (specsub lr values (left::a))
    | sstv_right lr l r w values a : CIsBranch lr l r ->
      SpecSubsToVar w (specsub r values a) ->
      SpecSubsToVar w (specsub lr values (right::a))
    .
  Inductive SpecSubsToBranch V W : SpecializationSubtree V W -> SpecializationSubtree V W -> SpecializationSubtree V W -> Prop :=
    sstb lr l r values a : CIsBranch lr l r ->
      SpecSubsToBranch (specsub lr values a) (specsub l values (left::a)) (specsub r values (right::a)).

  Definition SpecSubsTo V W : Context W -> SpecializationSubtree V W -> Prop :=
    CPred (@SpecSubsToVar _ _) (@SpecSubsToBranch _ _).

  (* Inductive Context V := c_cons {
    c_S : Type
    ; c_CS : CState V c_S
    ; c_root : c_S }. *)
  (* CoInductive CEquiv V (a b : Context V) : Prop :=
    | ceq_var v : CIsVar a v -> CIsVar b v -> CEquiv a b
    | ceq_branch la lb ra rb :
      CIsBranch a la ra -> CIsBranch b lb rb ->
      CEquiv la lb -> CEquiv ra rb -> CEquiv a b. *)
  CoInductive CEquiv [V] (a b : Context V) : Prop :=
    | ceq_var v : CIsVar v a -> CIsVar v b -> CEquiv a b
    | ceq_branch la ra lb rb :
      CIsBranch a la ra -> CIsBranch b lb rb ->
      CEquiv la lb -> CEquiv ra rb -> CEquiv a b
      .
  Notation "P '≡ₓ' Q" := (CEquiv P Q) (at level 70, no associativity) : type_scope.

  (* There are several different ways we could express this…
    `values` can either be (V -> Context W), or (V -> SC) for some third state-type C, or technically even (V -> SB) - but in that last approach,you'd be tempted to say `=` instead of `CEquiv`, and that doesn't work because _CB may have different states that express the same meaning, and still has to count as a specialization in that case. *)
  CoInductive IsThisSpecialization V W (values : V -> Context W) (c : Context V) (s : Context W) : Prop :=
    | its_var v : CIsVar v c -> s ≡ₓ (values v) -> IsThisSpecialization values c s
    | its_branch (lc rc : Context V) (ls rs : Context W) :
      CIsBranch c lc rc -> CIsBranch s ls rs ->
      IsThisSpecialization values lc ls ->
      IsThisSpecialization values rc rs ->
      IsThisSpecialization values c s.
  
  (* Inductive IsAnySpecialization V W (Cv : Context V) (Cw : Context W) : Prop := *)
  (* Inductive IsAnySpecializationCurried V SA [_CA : CState V SA] sa W SB [_CB : CState W SB] sb : Prop :=
    | ias_cons values : IsSpecializationCurried sa sb values -> IsAnySpecializationCurried sa sb. *)
     
  (* Inductive Context2 V := c2_cons {
    c2_S : Type
    ; c2_CS :: CState V c2_S
    ; c2_root : c2_S }.
  Arguments c2_cons {V c2_S c2_CS}.
  Instance cc2 V : CState V (Context2 V) := {
      cs_meaning := λ c, nm_map_states c2_cons (cs_meaning (c2_root c))
    }. *)
  (* Definition C2CRepack V : Context2 V -> Context V := Context2_rect _ (@c_cons _).
  Definition CC2Repack V : Context V -> Context2 V := Context_rect _ (@c2_cons _). *)
  (* Inductive SpecializationState V W :=
    | spec_outer (_:Context V)
    | spec_value (_:Context W).
  Arguments spec_outer {V W} _.
  Arguments spec_value {V W} _.

  Instance specialization_cs
    V W (values : V -> Context W)
    : CState W (SpecializationState V W)
    := { cs_meaning := λ c,
          match c with
          | spec_outer (c_cons St _C s) => match cs_meaning s with
            | var v => nm_map_states spec_value (cs_meaning (values v))
            | branch l r => branch (spec_outer (c_cons l)) (spec_outer (c_cons r))
            end
          | spec_value s => nm_map_states spec_value (cs_meaning s)
          end
      }.
  Eval compute in specialization_cs.
  Definition foo W := @c_cons W (Context W).
  Definition specialize V W (c : Context V) (values : V -> Context2 W) : Context W := @c_cons W (SpecializationState V W) (specialization_cs values) (spec_outer c). *)

  Inductive CIsAnySpecialization V (c : Context V) W (s : Context W) : Prop :=
    | ias_cons values : IsThisSpecialization values c s -> CIsAnySpecialization c s.

  (* Definition specialize
    V W Sb Sv [_Cb : CState V Sb] [_Cv : CState W Sv] (values : V -> Sv)
    (s : Sb) := inl s. *)

  Definition ACIsAnySpecialization (c s : AnyContext) : Prop := let (V, c) := c in let (W, s) := s in CIsAnySpecialization c s.
    
  
  Definition ContextSet := AnyContext -> Prop.

  Class CsValid (Cs : ContextSet) := {
        csv_includes_specializations :
          ∀ c s, ACIsAnySpecialization c s -> Cs c -> Cs s
      }.
  

  Section AbandonedApproaches.

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

  Section Properties.
    Lemma CEq_spec V (c s : Context V) : c ≡ₓ s -> CIsAnySpecialization c s.
      intro eq.
      econstructor.
      revert c s eq.
      cofix Q.
      destruct eq.
      eapply its_var.
      eassumption.
      admit.
      eapply its_branch.
      eassumption. eassumption.
      apply Q; assumption.
      apply Q; assumption.
    Qed.
  End Properties.
End Context.
Notation "P '≡ₓ' Q" := (CEquiv P Q) (at level 70, no associativity) : type_scope.

(****************************************************
                Concrete ContextSets
****************************************************)
Section ConcreteCSes.
  Inductive PushL (Cs : ContextSet) : ContextSet :=
    pushL_cons lr l r : ACIsBranch lr l r -> Cs l -> PushL Cs lr.

  Inductive PullR (Cs : ContextSet) : ContextSet :=
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