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
Set Typeclasses Depth 3.

(****************************************************
                    ??????????
****************************************************)

Inductive Location :=
  | l_root : Location
  | l_left : Location -> Location
  | l_right : Location -> Location
  .
Parameter LChain : Location -> Location -> Location -> Prop.

Parameter l_left_child : Location -> Location.
Parameter l_right_child : Location -> Location.

Definition UnificationPredicate :=
  Location -> Location -> Prop.

Definition UPRespectsSubtrees (UP : UnificationPredicate) :=
  ∀ l m,
    UP l m <->
    (UP (l_left_child l) (l_left_child m) ∧
     UP (l_right_child l) (l_right_child m)).

Definition UPComplete (UP : UnificationPredicate) :=
  ∀ l m,
    UP l m <-> (
      ∀ n, (UP n l -> UP n m) ∧ (UP l n -> UP m n)
    ).

Lemma complete_trans UP a b c : UPComplete UP -> UP a b -> UP b c -> UP a c.
  intros.
  destruct (H b c).
  destruct (H2 H1 a).
  apply H4. assumption.
Qed.
Lemma complete_refl UP a : UPComplete UP -> UP a a.
  intros.
  (* destruct (H a a). *)
  apply H. intros. split.
  trivial.
  trivial.
Qed.
Lemma complete_sym UP a b : UPComplete UP ->  UP a b -> UP b a.
  intros.
  destruct (H a b).
  destruct (H1 H0 a).
  apply H4.
  apply complete_refl.
  apply H.
  destruct (H1 H0 b).
  apply H. intros. split.
  intro.
  destruct (H n b).
  destruct (H2 H1 b).
  apply H4. assumption.
Qed.
Lemma its_just_equivalence UP
  (refl : ∀ a, UP a a)
  (sym : ∀ a b, UP a b -> UP b a)
  (trans : ∀ a b c, UP a b -> UP b c -> UP a c)
  : UPComplete UP.
  split; intros.
  split; intros.
  eapply trans; eassumption.
  eapply trans; [eapply sym|]; eassumption.
  apply H. apply refl.
Qed.

Definition UPNaiveSubset (A B : UnificationPredicate) :=
  ∀ l m, A l m -> B l m.

Definition CompletedUP (UP : UnificationPredicate) : UnificationPredicate :=
  λ l m, ∀ UP2, UPNaiveSubset UP UP2 -> UPRespectsSubtrees UP2 -> UP2 l m.

Definition UPSubset (A B : UnificationPredicate) :=
  ∀ l m, CompletedUP A l m -> CompletedUP B l m.




Definition Context Var :=
  Location -> Var -> Prop.

Definition Superset Var (A B : Context Var) :=
  ∀ l v, A l v -> B l v.

Inductive EqualLocs Var (C : Context Var) (l1 l2 : Location) : Prop :=
  | el_shared_var v : C l1 v -> C l2 v -> EqualLocs C l1 l2
  | el_subtree lb1 lb2 lext : 
      LChain lb1 lext l1 -> LChain lb2 lext l2 ->
      EqualLocs C lb1 lb2 ->
      EqualLocs C l1 l2
  (* | ie_trans l v : ImplicitExtension (ImplicitExtension C) l v -> ImplicitExtension C l v *)
  .
Inductive ImplicitExtension Var (C : Context Var) : Context Var :=
  | ie_varpass v l1 l2 lext le1 le2 v2 : 
      C l1 v -> C l2 v ->
      LChain l1 lext le1 -> LChain l2 lext le2 ->
      C le1 v2 ->
      ImplicitExtension C le2 v2
  (* | ie_trans l v : ImplicitExtension (ImplicitExtension C) l v -> ImplicitExtension C l v *)
  .

Inductive Subst V1 V2 (VarMap: V1 -> Context V2) :
  Context V1 -> Context V2 :=
  subst l1 l2 l12 A v w : A l1 v -> (VarMap v) l2 w -> LChain l1 l2 l12 -> (Subst VarMap A) l12 w.

Inductive Narrow C1 C2 Var (CaseMap : C2 -> Context C1 Var) :
  Context Case V1 -> Context Case V2 :=
  subst l1 l2 l12 A c v w : A l1 c v -> (VarMap v) l2 c w -> LChain l1 l2 l12 -> (Subst VarMap A) l12 c w.

\ l w -> \exists l1 l2 v B,  and A l1 v and (VarMap v) l2 w and l1++l2 = l

Class Constraints C V := {
    ObeysVar : C -> V -> Prop
  ; LeftChild : C -> C -> Prop
  ; RightChild : C -> C -> Prop
}.

CoInductive ObeysSameStructureAndVarConstraints C D CV DV {CT:Constraints C CV} {DT:Constraints D DV} (VarConstraints : D -> CV -> Prop)
  (c : C) (d : D) : Prop :=
  ss_cons :
  (∀ ca,  LeftChild c ca -> ∃ da, LeftChild d da
    ∧ ObeysSameStructureAndVarConstraints VarConstraints ca da) ->
  (∀ ca,  RightChild c ca -> ∃ da, RightChild d da
    ∧ ObeysSameStructureAndVarConstraints VarConstraints ca da) ->
  (∀ cv,  ObeysVar c cv -> VarConstraints d cv) ->
  ObeysSameStructureAndVarConstraints VarConstraints c d
  .

Definition StrictSuperset C D V {CT:Constraints C V} {DT:Constraints D V} (c : C) (d : D) := ObeysSameStructureAndVarConstraints ObeysVar c d.
Definition CStrictEquiv C D V {CT:Constraints C V} {DT:Constraints D V} (c : C) (d : D) := StrictSuperset c d ∧ StrictSuperset d c.


Definition VarMappedSuperset C D CV DV {CT:Constraints C CV} {DT:Constraints D DV} (c : C) (d : D) (var_map : CV -> D) :=
  ObeysSameStructureAndVarConstraints (λ d2 cv, StrictSuperset (var_map cv) d2) c d.

Definition SpecializationSuperset C D CV DV {CT:Constraints C CV} {DT:Constraints D DV} (c : C) (d : D) :=
  ∀ E EV (ET:Constraints E EV) (DEmbed : DV -> E),
    ∃ (CMap : CV -> E), VarMappedSuperset
      

Definition SpecializationSuperset C D CV DV {CT:Constraints C CV} {DT:Constraints D DV} (c : C) (d : D) :=
  ∃ embed_vars : CV -> D,
    ObeysSameStructureAndVarConstraints (λ d2 cv, CStrictEquiv d2(embed_vars cv)) c d.

CoInductive StrictSubset C D V {CT:Constraints C V} {DT:Constraints D V}
  (c : C) (d : D) : Prop :=
  ea_cons :
  (∀ ca,  LeftChild c ca -> ∃ da, LeftChild d da
    ∧ StrictSubset ca da) ->
  (∀ ca,  RightChild c ca -> ∃ da, RightChild d da
    ∧ StrictSubset ca da) ->
  (∀ v,  ObeysVar c v -> ObeysVar d v) ->
  StrictSubset c d
  .
  (* in, out, combined *)
(* CoInductive IsExtensionSubsetOfInner I IV C {ICT:Constraints I IV} {CCT:Constraints C IV}
  (i : I) (c : C) : Prop :=
  se_cons :
  (∀ v, ObeysVar c v -> StrictSubset) ->
  SubsetEmbedding c d
  . *)
CoInductive IsExtensionSubsetOfOuter I IV O OV C {ICT:Constraints I IV} {CCT:Constraints C IV} {OCT:Constraints O OV} {embed_vars : OV -> I}
  (o : O) (c : C) : Prop :=
  se_cons :
  (∀ oa,  LeftChild o oa -> ∃ ca, LeftChild c ca
    ∧ IsExtensionSubsetOfOuter oa ca) ->
  (∀ oa,  RightChild o oa -> ∃ ca, RightChild c ca
    ∧ IsExtensionSubsetOfOuter oa ca) ->
  (∀ v, ObeysVar o v -> StrictSubset (embed_vars v) c) ->
    IsExtensionSubsetOfOuter o c
  .

Class Constraints C := {
    MysteryConstraint : Type
  ; MysteriouslyConstrained : C -> MysteryConstraint -> Prop
  ; LeftChild : C -> C -> Prop
  ; RightChild : C -> C -> Prop
}.

Inductive ConstrainedNode C := {
    cn_constraints :: Constraints C
  ; cn_root : C
}.

(* Definition Subset (S T : ContextSet) :=
  ∀ ta tb, ct_branch (cs_root T) ta tb ->
    ∃ sa sb, ct_branch (cs_root S) sa sb. *)

(* Inductive Subset {C} {D} {CT:Context C} {DT:Context D} (c : C) (d : D)
  subset_cons
    (embed : C -> D)
    :
    (∀ d) *)

(* 

  , 
   *)


Class Embedding C D {CT:Constraints C} {DT:Constraints D} := {
    MysteriesEmbed : @MysteryConstraint C CT -> @MysteryConstraint D DT -> Prop
}.

CoInductive EmbeddingAgrees C D {CT:Constraints C} {DT:Constraints D} {ECD : @Embedding _ _ CT DT}
  (c : C) (d : D) : Prop :=
  ea_cons :
  (∀ ca,  LeftChild c ca -> ∃ da, LeftChild d da
    ∧ EmbeddingAgrees ca da) ->
  (∀ ca,  RightChild c ca -> ∃ da, RightChild d da
    ∧ EmbeddingAgrees ca da) ->
  (∀ ca,  MysteriouslyConstrained c ca -> ∃ da, 
  MysteriouslyConstrained d da
    ∧ 
    MysteriesEmbed ca da) ->
  EmbeddingAgrees c d
  .
  

CoInductive EmbedsAsSubset
  {C} {D} {CT:Constraints C} {DT:Constraints D}
  (embed : C -> D)
  (mystery_map : @MysteryConstraint _ CT -> D)
  (c : C) : Prop :=
  eas_cons :
  (∀ ca,  LeftChild c ca ->  LeftChild (embed c) (embed ca)
    ∧ EmbedsAsSubset embed mystery_map ca) ->
  (∀ ca, RightChild c ca -> RightChild (embed c) (embed ca)
    ∧ EmbedsAsSubset embed mystery_map ca) ->
  (∀ ca, MysteriouslyConstrained c ca ->
    MysteriouslyConstrained (embed c) (mystery_map ca)
    ) ->
  EmbedsAsSubset embed mystery_map c.


Inductive Superset 
  {C} {D} {CT:Constraints C} {DT:Constraints D}
  (c : C) : D -> Prop :=
  | superset_cons embed mystery_map :
    EmbedsAsSubset embed mystery_map c -> Superset c (embed c).

  (* (c : ConstrainedNode C) : ConstrainedNode D -> Prop :=
Definition Superset2 := *)

Inductive CDisjunction C := {
    cdDisjunct : Type
    (* ; cdGet : cdDisjunct -> ConstrainedNode C *)
    ; cd_constraints : cdDisjunct -> Constraints C
    ; cd_root : cdDisjunct -> C
  }.

Definition DisSuperset {C} {D}
  (c : CDisjunction C) (d : CDisjunction D) :=
  ∀ ddis : cdDisjunct d,
    ∃ cdis : cdDisjunct c,
      @Superset _ _ (cd_constraints c cdis) (cd_constraints d ddis) 
        (cd_root c cdis) (cd_root d ddis).



    ∃ da,
      ct_branch c ca cb
      ∧ Subset ca da
      ∧ Subset cb db
    ) -> Subset c d.

(* CoInductive LeftOf {C} {CT:Context C} (c : C) := *)
  (* all cases of uhh
    given branch c a b,
      obviously must obey a
      but also,
      e.g. in
      (a b) a & (b a) a
      this comes out to (a a) on the left
      formally, ct_branch includes
      ab a b, ba b a, S ab a, S ba a

      Lefts: 00a 01a
      Rights: 1a
      ...huh.

      however, consider
      Lefts: a
      Rights: a, 01b??? or does that not even constrain A

      what matters is if _a_ has more constraints
      which already matters!
      
      prevent: LHS reaches same place but RHS goes different places
      ...but, allow splitting?
      *)