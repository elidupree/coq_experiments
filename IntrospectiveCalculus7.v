Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import List.
Require Import String.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 3.

(****************************************************
               Contexts and relations
****************************************************)

(* The most basic level of objects we act-upon are called "contexts". You can view a context either as a formula, which is a binary tree, or as a list of formulas, represented as a tree of formulas which are each trees.

The definition of "Context" has no opinion on what objects are at the leaves of such a tree, or whether it's finite or infinite, or even whether you can look at a Context and tell whether it's a branch or leaf: all you know is that branch nodes can exist. *)
Implicit Types C E : Prop.
Inductive BranchGuarantees C : Prop :=
  | bg_no_guarantees : BranchGuarantees C
  | bg_is_branch : C -> C -> BranchGuarantees C
  .
Arguments bg_no_guarantees {C}.
Arguments bg_is_branch [C].

Inductive BGGuaranteesBranch C :
  BranchGuarantees C -> C -> C -> Prop :=
  | bggb_cons a b :
    BGGuaranteesBranch (bg_is_branch a b) a b
  .

Class Context C := {
  ct_guarantees : C -> BranchGuarantees C
}.

Definition CGuaranteesBranch C [CT: Context C] ab a b : Prop :=
  BGGuaranteesBranch (ct_guarantees ab) a b
  .


Inductive Extension C E : Prop :=
  | ext_base : C -> Extension C E
  | ext_ext : E -> Extension C E
  .
Arguments ext_base [C] [E].
Arguments ext_ext [C] [E].
(* Inductive ExtChildren C E : Prop :=
  | ext_children : Extension C E -> Extension C E -> ExtChildren C E
  . *)

Class ExtensionStructure C E := {
    ext_left_child : ∀ s : E, Extension C E
  ; ext_right_child : ∀ s : E, Extension C E
}.
Class Embedding C E := {
  embed : E -> C
}.

Definition ext_guarantees {C} {CT: Context C} {E} {ES : ExtensionStructure C E} (x : Extension C E) : BranchGuarantees (Extension C E) :=
  match x with
  | ext_base c => match ct_guarantees c with
    | bg_no_guarantees => bg_no_guarantees
    | bg_is_branch a b => bg_is_branch (ext_base a) (ext_base b)
    end
  | ext_ext e => bg_is_branch (ext_left_child e) (ext_right_child e)
  end.

Instance ct_ext {C} {CT: Context C} {E} {ES : ExtensionStructure C E}
  : Context (Extension C E)
  := { ct_guarantees := ext_guarantees }.

Definition embedding_referent C E {EE : Embedding C E} (x : Extension C E) :=
  match x with
  | ext_base c => c
  | ext_ext s => embed s
  end.
  
Definition EmbeddingAgrees C E {CT: Context C} {EE : Embedding C E} (ab : C) (a b : Extension C E) :=
  CGuaranteesBranch ab (embedding_referent a) (embedding_referent b).

Definition ContextComplete C (CT: Context C) :=
  ∀ E (ES : ExtensionStructure C E),
    ∃ EE : Embedding C E,
      ∀ e, EmbeddingAgrees (embed e) (ext_left_child e) (ext_right_child e).

Inductive AnyE C : Prop :=
  | anye E : ExtensionStructure C E -> E -> AnyE C.

Definition CompletedContext C := Extension C (AnyE C).
Definition cc_rewrap C E {ES : ExtensionStructure C E} (x : Extension C E) : Extension C (AnyE C) :=
  match x with
  | ext_base c => ext_base c
  | ext_ext e => ext_ext (anye ES e)
  end.
Definition cc_left_child {C} (e : AnyE C) : Extension C (AnyE C) :=
  match e with
  | anye _ _ e => cc_rewrap (ext_left_child e)
  end.
Definition cc_right_child {C} (e : AnyE C) : Extension C (AnyE C) :=
  match e with
  | anye _ _ e => cc_rewrap (ext_right_child e)
  end.
  
Instance cc_ext_structure {C} {E} {ES : ExtensionStructure C E}
  : ExtensionStructure C (AnyE C)
  := {
    ext_left_child := cc_left_child
  ; ext_right_child := cc_right_child }.



Inductive AECollapseE C : Prop :=
  | aece_inner E : ExtensionStructure C E -> E -> AECollapseE C
  | aece_outer E : ExtensionStructure (CompletedContext C) E -> E -> AECollapseE C
  .
Definition aece_rewrap_inner C E {ES : ExtensionStructure C E} (x : Extension C E) : Extension C (AECollapseE C) :=
  match x with
  | ext_base c => ext_base c
  | ext_ext e => ext_ext (aece_inner ES e)
  end.
Definition aece_rewrap_outer C E {ES : ExtensionStructure (CompletedContext C) E} (x : Extension (CompletedContext C) E) : Extension C (AECollapseE C) :=
  match x with
  | ext_base x2 => match x2 with
    | ext_base c => ext_base c
    | ext_ext e => match e with
      | anye _ _ e => ext_ext (aece_inner _ e)
      end
    end
  | ext_ext e => ext_ext (aece_outer _ e)
  end.
Definition aece_left_child {C} (e : AECollapseE C) : Extension C (AECollapseE C) :=
  match e with
  | aece_inner E _ e => aece_rewrap_inner (ext_left_child e)
  | aece_outer E _ e => aece_rewrap_outer (ext_left_child e)
  end.
Definition aece_right_child {C} (e : AECollapseE C) : Extension C (AECollapseE C) :=
  match e with
  | aece_inner E _ e => aece_rewrap_inner (ext_right_child e)
  | aece_outer E _ e => aece_rewrap_outer (ext_right_child e)
  end.
Instance aece_ext_structure {C}
  : ExtensionStructure C (AECollapseE C)
  := {
    ext_left_child := aece_left_child
  ; ext_right_child := aece_right_child }.

(* Definition cc_collapse {C} (e: AnyE (CompletedContext C)) : CompletedContext C :=
  match e with
  | anye _ ES e => ext_ext (anye aece_ext_structure (aece_outer _ e)) 
  end.
Instance cc_collapse_embedding {C} : Embedding (CompletedContext C) (AnyE (CompletedContext C)) :=
  { embed := cc_collapse }. *)
Definition cc_collapse {C} {E} {ES : ExtensionStructure (CompletedContext C) E} (e : E) : CompletedContext C :=
  ext_ext (anye aece_ext_structure (aece_outer _ e)).
Instance cc_collapse_embedding {C} {E} {ES : ExtensionStructure (CompletedContext C) E} : Embedding (CompletedContext C) E :=
  { embed := cc_collapse }.

  (* TODO: embeddings may also remap base values! *)

Lemma CompletedContext_complete C {CT: Context C} : @ContextComplete (CompletedContext C) _.
  intros E ES.
  exists cc_collapse_embedding.
  intro e.
  cbn.
  (* Set Printing Implicit. *)
  unfold EmbeddingAgrees, CGuaranteesBranch; cbn.

  (* remember (ext_left_child e).
  destruct e0. *)
  destruct (ext_left_child e).
  {
    destruct c.
    {
      cbn.
      destruct (ext_right_child e).
      {
        destruct c0.
        constructor.
        {
          destruct a.
          (* unfold embedding_referent. *)
          Set Printing Implicit.
          cbn.
          constructor.
    }
  {
  cbn.
  constructor.
  }

  constructor.
  unfold aece_rewrap_outer.
  (* destruct (ext_right_child e).
  remember (ext_left_child e). *)
  destruct (cc_rewrap (aece_rewrap_outer (ext_left_child e))).
  destruct (cc_rewrap (aece_rewrap_outer (ext_right_child e))).
  constructor.
  destruct .
  constructor.

Inductive CEquivPredMaySay C (CT: Context C) (P : C -> C -> Prop) : C -> C -> Prop :=
  | cepv_refl c : CEquivPredMaySay _ _ c c
  | cepv_branch ab1 ab2 a1 b1 a2 b2 :
    CGuaranteesBranch _ ab1 a1 b1 ->
    CGuaranteesBranch _ ab2 a2 b2 ->
    P a1 a2 -> P b1 b2 -> CEquivPredMaySay _ _ ab1 ab2
  .
Definition CEquivPredValid C (CT: Context C) (P : C -> C -> Prop) :=
  ∀ a b, P a b -> CEquivPredMaySay _ P a b.
Definition CEquiv C (CT: Context C) (a b : C) :=
  ∃ P, CEquivPredValid _ P ∧ P a b.

Inductive BOWRepresented C (CT: Context C) S (embed : S -> C) :
  BaseOrWrapped C S -> C -> Prop :=
  | bowr_equiv_to c d P :
    CEquivPredValid _ P ->
    P c d ->
    BOWRepresented _ embed (bow_base _ c) d
  | bowr_embedded s : 
    BOWRepresented _ embed (bow_wrapped _ s) (embed s)
  .

(* Definition BranchRepresented C (CT: Context C) S (embed : S -> C) (a b : BaseOrWrapped C S) ab :=
  BOWRepresented _ embed a cb
  CGuaranteesBranch _ ab (embed a) (embed b) *)
Inductive BranchRepresented C (CT: Context C) S (embed : S -> C) (a b : BaseOrWrapped C S) (cab : C) : Prop :=
  | branch_represented_cons ca cb :
    BOWRepresented _ embed a ca ->
    BOWRepresented _ embed b cb ->
    CGuaranteesBranch _ cab ca cb ->
    BranchRepresented _ embed a b cab
  .

Definition BRRepresented C (CT: Context C) S (embed : S -> C) (branch : BranchRequirement C S) :=
  match branch with
  | br_branch a b => BranchRepresented _ embed a b
  end.
  
Definition BranchStructure C S := ∀ s : S, BranchRequirement C S.

Definition ContextComplete C (CT: Context C) :=
  ∀ S (structure : BranchStructure C S),
    ∃ embed : S -> C,
      ∀ s, BRRepresented _ embed (structure s) (embed s).

Inductive CompletedContext C : Prop :=
  | cc_base : C -> CompletedContext C
  | cc_extra_branch S (structure : BranchStructure C S)
      : S -> CompletedContext C.


(* Definition BSBranch C S (CT: Context C)
  (structure : BranchStructure C S) (ab a b : S) : Prop
  :=
  match structure ab with
  | (br_equiv_to ab) => match (structure a, structure b) with
    | (br_equiv_to a, br_equiv_to b) => True
    | _ => False
    end
  | (br_branch a b) => True
  end. *)

(* Inductive CCBranch C (CT: Context C) :=
  | cc_branch_inC ab a b : ct_branch ab a b -> 
      CCBranch _ (bs_val ab) (bs_val a) (bs_val b)
  | cc_branch_wrapped a b : BsBranch _ (bs_branch a b) a b
  | cc_branch_cons S (structure : ∀ s : S, BranchRequirement C S) (ab a b : S)
      : CCBranch _ s 
      match (structure ab, structure a, structure b) with
      | (br_equiv_to ab, br_equiv_to a, br_equiv_to b) => embed s = c
      | br_branch a b => ct_branch (embed s) (embed a) (embed b)
      end. *)

(* Definition CCBranch C (CT: Context C) (ab a b : CompletedContext C) :=
  match ab with
  | cc_cons SAB structureAB ab => match structureAB ab with
    | (br_equiv_to ab) => match (a, b) with
      | (cc_cons SA structureA a, cc_cons SB structureB b) =>
        match (structureA a, structureB b) with
        | (br_equiv_to a, br_equiv_to b) => True
        | _ => False
        end
      end
    | (br_branch aS bS) => 
    end
  end. *)


Definition cbb_referent C S structure (bow : BaseOrWrapped C S) :=
  match bow with
  | bow_base c => cc_base c
  | bow_wrapped s => cc_extra_branch structure s
  end.
Definition cbb_guarantees C (CT: Context C) (c : CompletedContext C) : BranchGuarantees (CompletedContext C) :=
  match c with
  | cc_base c => match ct_guarantees c with
    | bg_no_guarantees => bg_no_guarantees _
    | bg_is_branch a b => bg_is_branch (cc_base a) (cc_base b)
    end
    (* | br_branch a b => bg_is_branch (cc_cons structure a) (cc_cons structure b)
    end *)
  | cc_extra_branch S0 structure s => match structure s with
    | br_branch a b => bg_is_branch (cbb_referent structure a) (cbb_referent structure b)
    end
  end.  

Instance ccc C (CT: Context C) : Context (CompletedContext C) := {
  ct_guarantees := cbb_guarantees _ }.


(* Definition cc_collapse_embed C :
  BranchStructure C (CompletedContext (CompletedContext C)).
  intro c0.
  destruct c0 as (S0, structure0, s0).
  destruct (structure0 s0) as [c1 | a1 b1].
  {
    destruct c1 as (S1, structure1, s1).
    destruct (structure1 s1) as [c2 | a2 b2].
    exact (br_equiv_to _ c2).
    apply br_branch.
    destruct (structure1 a1) as [c2 | a2 b2].
  } *)

(* Definition cc_collapse_embedding C S0
  (structure0 : BranchStructure (CompletedContext C) S0)
  (s0 : S0) (toEmbed : CCCollapseState (structure0 s0))
  : BranchRequirement C (CCCollapseState (structure0 s0)) :=
  match toEmbed with
  | cccs_val _ structure1 _ s1 => match structure1 s1 with
    | br_equiv_to c2 => br_equiv_to _ c2
    | br_branch a1 b1 => br_branch _ (cccs_val _ _ _ a1) (cccs_val _ _ _ b1)
    end 
  | cccs_branch _ _ => br_branch _ (cccs_branch _ _ _) (cccs_branch _ _ _)
  end.

Definition cc_collapse_value C S0
  (structure0 : BranchStructure (CompletedContext C) S0)
  (s0 : S0) : CCCollapseState (structure0 s0) :=
  match structure0 s0 with
  | br_equiv_to c1 => match c1 with
    | cc_cons S1 structure1 s1 => cccs_val _ _ _ s1
    end
  | br_branch a1 b1 => cccs_branch _ _ _
  end.

Definition cc_collapse C S0
  (structure0 : BranchStructure (CompletedContext C) S0)
  (s0 : S0) : CompletedContext C :=
  cc_cons
  (cc_collapse_embedding structure0 s0)
  (cc_collapse_value structure0 s0). *)

Inductive CCCollapseState C : Prop :=
  | cccs_inner S1 : BranchStructure C S1 -> S1 -> CCCollapseState C
  | cccs_wrapped S0 : BranchStructure (CompletedContext C) S0 -> S0 -> CCCollapseState C
  .

Definition cccs_inner_referent C S1 structure1 (bow : BaseOrWrapped C S1) : BaseOrWrapped C (CCCollapseState C) :=
  match bow with
  | bow_base c => bow_base _ c
  | bow_wrapped s1 => bow_wrapped _ (cccs_inner structure1 s1)
  end.
Definition cccs_outer_referent C S0 structure0 (bow : BaseOrWrapped (CompletedContext C) S0) : BaseOrWrapped C (CCCollapseState C) :=
  match bow with
  | bow_base cc1 => match cc1 with
    | cc_base c => bow_base _ c
    | cc_extra_branch S1 structure1 s1 => bow_wrapped _ (cccs_inner structure1 s1)
    end
  | bow_wrapped s0 => bow_wrapped _ (cccs_wrapped structure0 s0)
  end.
Definition cc_collapse_structure C (s : CCCollapseState C) : BranchRequirement C (CCCollapseState C) :=
  match s with
  | cccs_inner S1 structure1 s1 => match structure1 s1 with
    | br_branch a b => br_branch (cccs_inner_referent structure1 a) (cccs_inner_referent structure1 b)
    end
  | cccs_wrapped S0 structure0 s0 => match structure0 s0 with
    | br_branch a b => br_branch (cccs_outer_referent structure0 a) (cccs_outer_referent structure0 b)
    end
  end
  .


(* Definition cc_collapse C
  (cc0 : CompletedContext (CompletedContext C)) : CompletedContext C :=
  match cc0 with
  | cc_base cc1 => match cc1 with
    | cc_base c => cc_base c
    | cc_extra_branch S1 structure1 s1 => cc_extra_branch (@cc_collapse_structure C) (cccs_inner structure1 s1)
    end
  | cc_extra_branch S0 structure0 s0 => match structure0 s0 with
    | br_branch a b => cc_extra_branch (@cc_collapse_structure C) (cccs_wrapped structure0 s0)
    end
  end. *)

Definition cc_collapse C S0 
  (structure0 : BranchStructure
  (CompletedContext C) S0) (s0 : S0) : CompletedContext C :=
  match structure0 s0 with
  | br_branch a b => cc_extra_branch (@cc_collapse_structure C) (cccs_wrapped structure0 s0)
  end.

Definition cc_collapse_bow_represented C S0 
  (structure0 : BranchStructure
  (CompletedContext C) S0) (bow0 : BaseOrWrapped (CompletedContext C) S0) :=
  match bow0 with
  | bow_base cc1 => match cc1 with
    | cc_base c => cc_base c
    | cc_extra_branch S1 structure1 s1 => cc_extra_branch (@cc_collapse_structure C) (cccs_inner structure1 s1)
    end
  | bow_wrapped s0 => cc_extra_branch (@cc_collapse_structure C) (cccs_wrapped structure0 s0)
  end.

Inductive CcCollapseEquivalence C (CT: Context C) :
  (CompletedContext C) -> (CompletedContext C) -> Prop :=
  | ccce_refl c : CcCollapseEquivalence _ c c
  | ccce_collapsed S0 structure0 (s0 : S0) :
    CcCollapseEquivalence _ (cc_extra_branch structure0 s0) (cc_extra_branch (@cc_collapse_structure C) (cccs_))
  .

Lemma cc_complete C (CT: Context C)
  : ContextComplete (ccc _).

  intros S0 structure0.

  exists (cc_collapse structure0).

  intro s0.
  (* unfold cc_collapse at 2. *)
  destruct (structure0 s0) as [a0 b0].

  apply branch_represented_cons with (cc_collapse_bow_represented structure0 a0) (cc_collapse_bow_represented structure0 b0).
  
  {
    destruct a0.
    eapply bowr_equiv_to.
    (* destruct c. cbn.
    eapply bowr_equiv_to. *)
    admit.
    admit.
    (* eapply bowr_equiv_to. *)
    (* admit. *)
    refine (bowr_embedded _ _ _).
    eapply bowr_equiv_to.
    eapply bowr_embedded.
    CEquivPredValid 
    .
  }
  
  cbn.

  econstructor.


  
    unfold cc_collapse_value at 2.
    unfold cc_collapse_embedding at 2.
  destruct (structure0 s0) as [c1 | a1 b1].
  { 
    (* unfold cc_collapse.
    unfold cc_collapse_value. *)


    destruct c1 as [S1 structure1 s1].

    apply brr_val.
    cbn.
    destruct (structure1 s1) as [c1 | a1 b1].
    cbn.
  }

  cbn.



      ∃ c:C, BranchRequirement C C
      ∀ P : BranchRequirement C S -> Prop,
        (∀ c:C, P (br_equiv_to _ c)) -> 
        (∀ a b:S,
          P (br_branch a b)) -> 
        P s.
      match structure s with
      | br_equiv_to : 
      end.
      embed s 
  

Definition ContextComplete C (CT: Context C) :=
  ∀ bs : BranchStructure C,
    ∃ x : C, BranchStructureRepresented _ bs x.


CoInductive BranchStructure C :=
  | bs_val : C -> BranchStructure C
  | bs_branch : BranchStructure C -> BranchStructure C -> BranchStructure C.

Definition IsVal C (CT: Context C)
  (bs : BranchStructure C) (c : C) : Prop :=
  match bs with
  | bs_val d => d = c
  | bs_branch a b => False
  end.
Definition IsBranch C (CT: Context C)
  (bs : BranchStructure C) (a b : BranchStructure C) : Prop :=
  match bs with
  | bs_val d => False
  | bs_branch a2 b2 => a2 = a ∧ b2 = b
  end.


CoInductive BranchStructureRepresented C (CT: Context C)
  : BranchStructure C -> C -> Prop :=
  | bsr_val c bsc : IsVal _ bsc c -> BranchStructureRepresented _ bsc c
  | bsr_branch ab a b bsa bsb bsab :
    (ct_branch ab a b) ->
    IsBranch _ bsab bsa bsb ->
    BranchStructureRepresented _ bsa a ->
    BranchStructureRepresented _ bsb b ->
    BranchStructureRepresented _ bsab ab
  .
  
Definition ContextComplete C (CT: Context C) := ∀ bs :
  BranchStructure C, ∃ x : C, BranchStructureRepresented _ bs x.

Inductive BsBranch C (CT: Context C) : (BranchStructure C) -> (BranchStructure C) -> (BranchStructure C) -> Prop :=
  | bs_branch_inC ab a b : ct_branch ab a b -> 
      BsBranch _ (bs_val ab) (bs_val a) (bs_val b)
  | bs_branch_wrapped a b : BsBranch _ (bs_branch a b) a b
  .

Instance bsc C (CT: Context C) : Context (BranchStructure C) := {
ct_branch :=
  BsBranch _ }.

CoFixpoint bs_collapse C (bsbs:BranchStructure (BranchStructure C)) :
  BranchStructure C.
  destruct bsbs.
  { exact b.
    (* destruct b.
    exact (bs_val c).
    exact (bs_branch b1 b2). *)
  }
  exact (bs_branch (bs_collapse _ bsbs1) (bs_collapse _ bsbs2)).
Defined.

Lemma bs_complete C (CT: Context C) : ContextComplete (bsc _).
  unfold ContextComplete; intros.
  exists (bs_collapse bs).
  revert bs.
  cofix Q. destruct bs.
  (* cofix Q. destruct bs. *)
  {
    revert Q b.
    cofix R. destruct b.
    apply bsr_val. cbn.

    (* exact Q. *)
  (* exact cheat. *)
    destruct b.
    apply bsr_val.
    cbn.
  (* exact cheat. *)
    eapply bsr_branch; eassumption.

    (* revert Q b. *)
    (* cofix R. destruct b.
    apply bsr_val. *)
  }
  eapply bsr_branch.
  constructor.
  exact cheat.
Qed.

(* Analogous to "sets of inference rules", we define "context sets", which are just that – sets of contexts (representing a set as a predicate). A ContextSet is required to be agnostic to everything except what's defined in Context. *)

Definition ContextSet := ∀ C (CT: Context C), C -> Prop.
Declare Scope cs_scope.
Bind Scope cs_scope with ContextSet.

Class AsCS T := {
    as_cs : T -> ContextSet
  }.
Instance cs_as_cs : AsCS ContextSet := {
    as_cs := id
  }.

(* …and analogous to "derivability between rulesets", we have the subset relation between ContextSets. (And also equivalence between ContextSets, which is the same as mutual-subset). *)

Definition CsSubset (R S : ContextSet) : Prop :=
  ∀ C (CT: Context C) c, R _ _ c -> S _ _ c.
Notation "P '⊆' Q" := (CsSubset P Q) (at level 70, no associativity) : type_scope.
Definition CsEquiv (R S : ContextSet) : Prop :=
  ∀ C (CT: Context C) c, R _ _ c <-> S _ _ c.
Notation "P '≡' Q" := (CsEquiv P Q) (at level 70, no associativity) : type_scope.
Lemma CsSubset_of_CsEquiv R S : R ≡ S -> R ⊆ S.
  unfold CsEquiv, CsSubset. intros. apply H. assumption.
Qed.
Lemma CsEquiv_refl A : A ≡ A.
  unfold CsEquiv; intros; split; trivial.
Qed.
Lemma CsEquiv_sym A B : A ≡ B -> B ≡ A.
  unfold CsEquiv; intros; split; intro; apply H; assumption.
Qed. 
Lemma CsEquiv_trans A B C : A ≡ B -> B ≡ C -> A ≡ C.
  unfold CsEquiv; intros; split; intro.
  apply H. apply H0. assumption.
  apply H0. apply H. assumption.
Qed.

(* We are particularly interested in a specific, constrained subclass of context-relations: _Computable unification predicates_.

These are (computable, infinite) trees of Boolean operations on equality constraints between subtrees of a context. *)

Inductive Location :=
  | l_root : Location
  | l_left : Location -> Location
  | l_right : Location -> Location
  .

Inductive SubtreeAt C (CT: Context C) : Location -> C -> C -> Prop :=
  | sal_root c : SubtreeAt _ l_root c c
  | sal_left l ab a b c : ct_branch ab a b -> SubtreeAt _ l a c -> SubtreeAt _ (l_left l) ab c
  | sal_right l ab a b c : ct_branch ab a b -> SubtreeAt _ l b c -> SubtreeAt _ (l_right l) ab c
  .

Inductive CsUnify (l m : Location) C (CT: Context C) (c : C) : Prop :=
  | cs_unify x : SubtreeAt _ l c x -> SubtreeAt _ m c x -> CsUnify l m _ c
  .

(* First, we define an expansive definition of unification predicates using Coq's `CoInductive`. Coq guarantees that any _global_ instance of this type is computable, but the programs aren't reified in Coq, so we can't prove _in Coq_ that every instance of this type is implemented by a program. Nevertheless, this is the simplest way to define it, so maybe it helps make the proofs more understandable. *)

CoInductive UnificationPredicate :=
  | up_unify : Location -> Location -> UnificationPredicate
  | up_or : UnificationPredicate -> UnificationPredicate -> UnificationPredicate
  | up_and : UnificationPredicate -> UnificationPredicate -> UnificationPredicate
  .

(* CoInductive CsUp (up : UnificationPredicate) C (CT: Context C) (c : C) : Prop := *)
(* CoFixpoint CsUp (up : UnificationPredicate) : ContextSet :=
  match up with
  | up_unify l m => CsUnify l m
  | up_or s t => CsOr (CsUp s) (CsUp t)
  | up_and s t => CsAnd (CsUp s) (CsUp t)
  end. *)

CoInductive CtxObeysUp C (CT: Context C) (c : C) : UnificationPredicate -> Prop :=
  | cou_unify l m : CsUnify l m _ c -> CtxObeysUp _ c (up_unify l m)
  | cou_or_left R S : (CtxObeysUp _ c R) -> CtxObeysUp _ c (up_or R S)
  | cou_or_right R S : (CtxObeysUp _ c S) -> CtxObeysUp _ c (up_or R S)
  | cou_and R S : (CtxObeysUp _ c R) -> (CtxObeysUp _ c S) -> CtxObeysUp _ c (up_and R S)
  .
  
Instance up_as_cs : AsCS UnificationPredicate := {
    as_cs := λ up _ _ c, CtxObeysUp _ c up
  }.


Definition CsMonism : ContextSet := λ _ _ c, ct_branch c c c.
(* Inductive CsMonism C (CT: Context C) (c : C) : Prop :=
  | cs_monism : ct_branch c c c -> CsMonism _ c
  . *)

Lemma monism_element_everywhere l C (CT: Context C) (c : C) : CsMonism _ c -> SubtreeAt _ l c c.
  intros; cbn.
  induction l; [constructor|..].
  all: econstructor; [apply H|assumption].
Qed.

Lemma monism_unifies_all l m : CsMonism ⊆ CsUnify l m.
  unfold CsSubset; intros; cbn.
  exists c; apply monism_element_everywhere; assumption.
Qed.

(* CoFixpoint monism_smallest (up : UnificationPredicate) : CsMonism ⊆ (as_cs up) :=
  match up with
  | up_unify l m => (monism_unifies_all l m)
  | up_or s t => cou_or_left monism_smallest
  | up_and s t => cou_and monism_smallest monism_smallest
  end. *)
  
Lemma monism_in_all_ups (up : UnificationPredicate) : CsMonism ⊆ (as_cs up).
  unfold CsSubset; intros; cbn.
  revert up; cofix Q; destruct up.

  apply cou_unify; apply monism_unifies_all; assumption.
  apply cou_or_left; apply Q.
  apply cou_and; apply Q.
Qed.

(* Explicit Computable Unification Predicates *)
Inductive CUP :=
  | cup_children_equal
  | cup_pulldownLL_in (_:CUP)
  | cup_pulldownLR_in (_:CUP)
  | cup_right_obeys (_:CUP)
  | cup_left_of (_:CUP)
  | cup_or (_ _:CUP)
  | cup_and (_ _:CUP)
  | cup_iterate (_:CUP)
  .

Inductive CsChildrenEqual C (CT: Context C) : C -> Prop :=
  | cs_children_equal cc c : ct_branch cc c c -> CsChildrenEqual _ cc
  .

Inductive CsPulldownLLIn (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_pulldownLL_in abc ab ac a b c : ct_branch abc ab c -> ct_branch ab a b -> ct_branch ac a c -> S _ _ ac -> CsPulldownLLIn S _ abc
  .

Inductive CsPulldownLRIn (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_pulldownLR_in abc ab bc a b c : ct_branch abc ab c -> ct_branch ab a b -> ct_branch bc b c -> S _ _ bc -> CsPulldownLRIn S _ abc
  .

Inductive CsRightObeys (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_right_obeys ab a b : ct_branch ab a b -> S _ _ b -> CsRightObeys S _ ab
  .

Inductive CsLeftOf (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_left_of ab a b : ct_branch ab a b -> S _ _ ab -> CsLeftOf S _ a
  .

Inductive CsOr (R S : ContextSet) C (CT: Context C) (c : C) : Prop :=
  | cs_or_left : R _ _ c -> CsOr R S _ c
  | cs_or_right : S _ _ c -> CsOr R S _ c
  .

Inductive CsAnd (R S : ContextSet) C (CT: Context C) (c : C) : Prop :=
  | cs_and : R _ _ c -> S _ _ c -> CsAnd R S _ c
  .

CoInductive CsIterate (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_iterate ab a b : ct_branch ab a b -> S _ _ ab -> CsIterate S _ b -> CsIterate S _ ab
  .

Fixpoint CsCUP (cup : CUP) : ContextSet :=
  match cup with
  | cup_children_equal => CsChildrenEqual
  | cup_pulldownLL_in a => CsPulldownLLIn (CsCUP a)
  | cup_pulldownLR_in a => CsPulldownLRIn (CsCUP a)
  | cup_right_obeys a => CsRightObeys (CsCUP a)
  | cup_left_of a => CsLeftOf (CsCUP a)
  | cup_or a b => CsOr (CsCUP a) (CsCUP b)
  | cup_and a b => CsAnd (CsCUP a) (CsCUP b)
  | cup_iterate a => CsIterate (CsCUP a)
  end.
Instance cup_as_cs : AsCS CUP := {
    as_cs := CsCUP
  }.

(* Definition CUP_to_UP (cup : CUP) : UnificationPredicate :=
  match cup with *)

Lemma monism_in_CsIterate S : CsMonism ⊆ S -> CsMonism ⊆ CsIterate S.
  unfold CsSubset; intros; cbn.
  cofix Q.
  econstructor. eassumption. apply H; assumption. assumption.
Qed.

Ltac solve_monism_in_whatever := unfold CsSubset; intros; cbn in *; econstructor; eauto.
Lemma monism_in_all_cups (cup : CUP) : CsMonism ⊆ (as_cs cup).
  induction cup; try solve [solve_monism_in_whatever].
  apply monism_in_CsIterate; assumption.
Qed.

