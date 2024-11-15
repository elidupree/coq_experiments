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

(* One notable simplification step is to rewrite equality hypotheses when one side is just another hypothesis. But it's kinda expensive. *)
Hint Extern 9 => progress match goal with
  | x : _ |- _ => match goal with
    | eq : x = _ |- _ => rewrite eq in *; clear x eq
    | eq : _ = x |- _ => rewrite <- eq in *; clear x eq
    end
  end; shelve
  : simplify.

(****************************************************
               Contexts and relations
****************************************************)

(* The most basic objects we act-upon are called "contexts". You can view a context either as a formula, which is a binary tree, or as a list of formulas, represented as a tree of formulas which are each trees.

The basic definition of "Context" has no opinion on what objects are at the leaves of such a tree, or whether it's finite or infinite: all you know is that some nodes can be branch nodes. *)

Inductive NodeLinks C :=
  | nl_leaf : NodeLinks C
  | nl_branch : C -> C -> NodeLinks C
  .
Arguments nl_leaf {C}.
Arguments nl_branch [C].

Inductive NLIsBranch C : NodeLinks C -> C -> C -> Prop :=
  | nlib_cons a b : NLIsBranch (nl_branch a b) a b.

Class Context C := {
  ct_node_links : C -> NodeLinks C
}.

Definition IsBranch C [CT: Context C] ab a b : Prop :=
  NLIsBranch (ct_node_links ab) a b.

(* ...But really, if you possess two contexts `a` and `b`, you should be able to construct a node that's a branch between `a` and `b`. In fact, we go so far as to say that you should be able to construct *any computable finite or infinite branch structure* over existing nodes. We capture this in the concept of an "extension". *)

Class Extension C E := {
    ext_left_child : ∀ s : E, C + E
  ; ext_right_child : ∀ s : E, C + E
}.

Definition ext_links {C} {CT: Context C} {E} {ES : Extension C E} (x : C + E) : NodeLinks (C + E) :=
  match x with
  | inl c => match ct_node_links c with
    | nl_leaf => nl_leaf
    | nl_branch a b => nl_branch (inl a) (inl b)
    end
  | inr e => nl_branch (ext_left_child e) (ext_right_child e)
  end.

Instance ct_ext {C} {CT: Context C} {E} {ES : Extension C E}
  : Context (C + E)
  := { ct_node_links := ext_links }.

(* ...and if you have an extension, you may want to be able to *embed* that extension within the original context type, with an agreeing branch-structure. A "complete" context-type is one where you can always do this. *)

Class Embedding C E := {
  embed : E -> C
}.

Definition embed_sum C E {EE : Embedding C E} (x : C + E) :=
  match x with inl c => c | inr s => embed s end.
Definition EmbeddingAgrees C E {CT: Context C} {ES : Extension C E} (EE : Embedding C E) :=
  ∀ ab, IsBranch (embed ab)
    (embed_sum (ext_left_child ab))
    (embed_sum (ext_right_child ab)).

Class CompleteContext C := {
    cc_ct :: Context C
  ; cc_complete : ∀ E (ES : Extension C E), ∃ EE : Embedding C E, EmbeddingAgrees EE
  }.

(****************************************************
      Explicit construction of complete context
****************************************************)

CoInductive CoinductiveExtension C := {
    cie_left_child : C + (CoinductiveExtension C)
  ; cie_right_child : C + (CoinductiveExtension C)
}.
Definition CompletedContext C : Type := C + (CoinductiveExtension C).

Instance cc_ext_structure {C}
  : Extension C (CoinductiveExtension C)
  := {
    ext_left_child := @cie_left_child C
  ; ext_right_child := @cie_right_child C }.

Definition rr_to_r A B C (m : C -> B) (x : (A + B) + C) : A + B :=
  match x with inl c => c | inr s => inr (m s) end.

CoFixpoint cie_from_extension {C} {E} {ES : Extension (CompletedContext C) E} (e : E) : CoinductiveExtension C :=
  {|
      cie_left_child  := rr_to_r cie_from_extension (ext_left_child e)
    ; cie_right_child := rr_to_r cie_from_extension (ext_right_child e)
  |}.

Instance cc_embeds_extension {C} {E} {ES : Extension (CompletedContext C) E} : Embedding (CompletedContext C) E :=
  { embed := λ e, inr (cie_from_extension e) }.
  
Lemma CompletedContext2_complete C {CT: Context C} : CompleteContext (CompletedContext C).
  refine ({| cc_ct := _ |}).
  
  intros E ES.
  exists cc_embeds_extension.
  intro e.
  unfold IsBranch; cbn.
  (* What remains is just 9 trivial cases. *)
  destruct (ext_left_child e) as [[?|?]|?];
    destruct (ext_right_child e) as [[?|?]|?];
    constructor.
Qed.

(****************************************************
                More about contexts
****************************************************)

CoInductive CEquiv C {CT : Context C} : C -> C -> Prop :=
  | ceq_refl c : CEquiv c c
  | ceq_branch ab1 a1 b1 ab2 a2 b2: CEquiv a1 a2 -> CEquiv b1 b2 -> IsBranch ab1 a1 a2 -> IsBranch ab1 a1 a2 -> CEquiv ab1 ab2.

Notation "a '≜' b" := (CEquiv a b) (at level 70, no associativity) : type_scope.

(****************************************************
                   Context sets
****************************************************)

(* Analogous to "sets of inference rules", we define "context sets", which are just that – sets of contexts (representing a set as a predicate). A ContextSet is required to be agnostic to everything except what's defined in Context. *)

Definition ContextSet := ∀ C (CT: Context C), C -> Prop.
Declare Scope cs_scope.
Bind Scope cs_scope with ContextSet.

(* We're going to define many concrete types that represent specific limited ranges context sets, so make a class to abstract over that. *)
Class AsCS T := {
    as_cs : T -> ContextSet
  }.
Instance cs_as_cs : AsCS ContextSet := {
    as_cs := id
  }.
Definition InCS {C} {CT: Context C} (c : C) (S : ContextSet) := S _ _ c.
Notation "c '∈' S" := (InCS c S) (at level 70, no associativity) : type_scope.
Notation "c '⋵' S" := (InCS c (as_cs S)) (at level 70, no associativity) : type_scope.
Hint Extern 4 => progress match goal with
  | |- ?S _ _ ?x => change (x ∈ S)
  end; shelve : simplify.
Hint Extern 5 => progress match goal with
  | H : ?S _ _ ?x |- _ => change (x ∈ S) in H
  end; shelve : simplify.

(* …and analogous to "derivability between rulesets", we have the subset relation between ContextSets. (And also equivalence between ContextSets, which is the same as mutual-subset). *)

Definition CsSubset (R S : ContextSet) : Prop :=
  ∀ C (CT: CompleteContext C) c, R _ _ c -> S _ _ c.
Notation "P '⊆' Q" := (CsSubset P Q) (at level 70, no associativity) : type_scope.
Notation "P '⊑' Q" := (CsSubset (as_cs P) (as_cs Q)) (at level 70, no associativity) : type_scope.
Definition CsEquiv (R S : ContextSet) : Prop :=
  ∀ C (CT: CompleteContext C) c, R _ _ c <-> S _ _ c.
Notation "P '≡' Q" := (CsEquiv P Q) (at level 70, no associativity) : type_scope.
Notation "P '≐' Q" := (CsEquiv (as_cs P) (as_cs Q)) (at level 70, no associativity) : type_scope.
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
  apply H0. apply H. assumption.
  apply H. apply H0. assumption.
Qed.

(* We are particularly interested in a specific, constrained subclass of context-relations: *Computable unification predicates*.

These are (computable, infinite) trees of Boolean operations on equality constraints between subtrees of a context. *)

Inductive Location :=
  | l_root : Location
  | l_left : Location -> Location
  | l_right : Location -> Location
  .

Inductive SubtreeAt C (CT: Context C) : Location -> C -> C -> Prop :=
  | sal_root c : SubtreeAt _ l_root c c
  | sal_left l ab a b c : IsBranch ab a b -> SubtreeAt _ l a c -> SubtreeAt _ (l_left l) ab c
  | sal_right l ab a b c : IsBranch ab a b -> SubtreeAt _ l b c -> SubtreeAt _ (l_right l) ab c
  .

Inductive CsUnify (l m : Location) C (CT: Context C) (c : C) : Prop :=
  | cs_unify x : SubtreeAt _ l c x -> SubtreeAt _ m c x -> CsUnify l m _ c
  .

(* First, we define an expansive definition of unification predicates using `CoInductive`. Coq guarantees that any *global* instance of this type is computable, but the programs aren't reified in Coq, so we can't prove *in Coq* that every instance of this type is implemented by a program. Nevertheless, this is the simplest way to define it, so maybe it helps make the proofs more understandable. *)

CoInductive UnificationPredicate :=
  | up_unify : Location -> Location -> UnificationPredicate
  | up_or : UnificationPredicate -> UnificationPredicate -> UnificationPredicate
  | up_and : UnificationPredicate -> UnificationPredicate -> UnificationPredicate
  .

CoInductive CtxObeysUP C (CT: Context C) (c : C) : UnificationPredicate -> Prop :=
  | cou_unify l m : CsUnify l m _ c -> CtxObeysUP _ c (up_unify l m)
  | cou_or_left R S : (CtxObeysUP _ c R) -> CtxObeysUP _ c (up_or R S)
  | cou_or_right R S : (CtxObeysUP _ c S) -> CtxObeysUP _ c (up_or R S)
  | cou_and R S : (CtxObeysUP _ c R) -> (CtxObeysUP _ c S) -> CtxObeysUP _ c (up_and R S)
  .

Definition CsUP (up : UnificationPredicate) : ContextSet := λ C (CT: Context C) (c : C), CtxObeysUP _ c up.
Instance up_as_cs : AsCS UnificationPredicate := {
    as_cs := CsUP
  }.
Coercion CsUP : UnificationPredicate >-> ContextSet.

(* One notable ContextSet is the *smallest unification predicate*: The set that requires every possible equality constraint. This is equivalent to saying that any member of the set must be equal to its own left and right children. We name this "Monism", after the philosophical perspective that only one object exists. (Technically, there may be other members of the context type that are distinct; but anything *visible to the predicate* must be the same.) *)
Definition CsMonism : ContextSet := λ _ _ c, IsBranch c c c.

Lemma monism_element_everywhere l C (CT: Context C) (c : C) : CsMonism _ c -> SubtreeAt _ l c c.
  intros; cbn.
  induction l; [constructor|..].
  all: econstructor; [apply H|assumption].
Qed.

Lemma monism_unifies_all l m : CsMonism ⊆ CsUnify l m.
  unfold CsSubset; intros; cbn.
  exists c; apply monism_element_everywhere; assumption.
Qed.
  
Lemma monism_in_all_ups (up : UnificationPredicate) : CsMonism ⊆ (as_cs up).
  unfold CsSubset; intros; cbn.
  revert up; cofix Q; destruct up.

  apply cou_unify; apply monism_unifies_all; assumption.
  apply cou_or_left; apply Q.
  apply cou_and; apply Q.
Qed.

(* Next, we define an explicit type of computable unification predicates – CUPs for short – which is reified. Using these constructors, any computable unification predicate can be represented as an *explicitly finite* CUP. And since these don't have any fields of any other types, they will be particularly suitable for representing in an *untyped* core calculus, where everything is a CUP. *)
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
Declare Scope cup_scope.
Bind Scope cup_scope with CUP.

Class AsCUP T := {
    as_cup : T -> CUP
  }.
Instance cup_as_cup : AsCUP CUP := {
    as_cup := id
  }.

Notation "a '∧' b" := (cup_and a b) (at level 80, right associativity) : cup_scope.
Notation "a '∨' b" := (cup_or a b) (at level 85, right associativity) : cup_scope.

Inductive CsChildrenEqual C (CT: Context C) : C -> Prop :=
  | cs_children_equal cc c : IsBranch cc c c -> CsChildrenEqual _ cc
  .

Inductive CsPulldownLLIn (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_pulldownLL_in abc ab ac a b c : IsBranch abc ab c -> IsBranch ab a b -> IsBranch ac a c -> S _ _ ac -> CsPulldownLLIn S _ abc
  .

Inductive CsPulldownLRIn (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_pulldownLR_in abc ab bc a b c : IsBranch abc ab c -> IsBranch ab a b -> IsBranch bc b c -> S _ _ bc -> CsPulldownLRIn S _ abc
  .

Inductive CsRightObeys (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_right_obeys ab a b : IsBranch ab a b -> S _ _ b -> CsRightObeys S _ ab
  .

Inductive CsLeftOf (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_left_of ab a b : IsBranch ab a b -> S _ _ ab -> CsLeftOf S _ a
  .

Inductive CsOr (R S : ContextSet) C (CT: Context C) (c : C) : Prop :=
  | cs_or_left : R _ _ c -> CsOr R S _ c
  | cs_or_right : S _ _ c -> CsOr R S _ c
  .

Inductive CsAnd (R S : ContextSet) C (CT: Context C) (c : C) : Prop :=
  | cs_and : R _ _ c -> S _ _ c -> CsAnd R S _ c
  .

CoInductive CsIterate (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_iterate ab a b : IsBranch ab a b -> S _ _ ab -> CsIterate S _ b -> CsIterate S _ ab
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
Coercion CsCUP : CUP >-> ContextSet.

Definition ascup_ascs T {tcup : AsCUP T} : AsCS T := {|
    as_cs := λ t, as_cs (as_cup t)
  |}.
Hint Extern 2 (AsCS _) => simple apply ascup_ascs : typeclass_instances.

Hint Extern 5 => progress change (?as_cs (cup_children_equal)) with CsChildrenEqual in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_pulldownLL_in ?fup)) with (CsPulldownLLIn (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_pulldownLR_in ?fup)) with (CsPulldownLRIn (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_right_obeys ?fup)) with (CsRightObeys (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_left_of ?fup)) with (CsLeftOf (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_or ?a ?b)) with (CsOr (as_cs a) (as_cs b)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (cup_and ?a ?b)) with (CsAnd (as_cs a) (as_cs b)) in *; shelve : simplify.

Ltac dontforget term :=
  lazymatch term with
  | (_ _) => lazymatch goal with
    | _ : _ = term |- _ => idtac
    | _ : term = _ |- _ => idtac
    | _ => remember term
    end
  | _ => idtac 
  end.

Hint Extern 5 => progress match goal with
  | H : ?c ∈ CsChildrenEqual |- _ => dontforget c; destruct H
  | H : ?c ∈ CsPulldownLLIn _ |- _ => dontforget c; destruct H
  | H : ?c ∈ CsPulldownLRIn _ |- _ => dontforget c; destruct H
  | H : ?c ∈ CsRightObeys _ |- _ => dontforget c; destruct H
  | H : ?c ∈ CsLeftOf _ |- _ => dontforget c; destruct H
  | H : ?c ∈ CsAnd _ _ |- _ => dontforget c; destruct H
  end : simplify.

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

Lemma cups_respect_branch_meaning (cup : CUP) C (CT: Context C) (a b : C) : CEquiv a b -> a ∈ cup -> b ∈ cup.
  intros.
  induction cup.

(****************************************************
                Finitude or something
****************************************************)

(* And a more restrictive type containing only the *finite* constructors: *)
Inductive FUP :=
  | fup_children_equal
  | fup_pulldownLL_in (_:FUP)
  | fup_pulldownLR_in (_:FUP)
  | fup_right_obeys (_:FUP)
  | fup_left_of (_:FUP)
  | fup_or (_ _:FUP)
  | fup_and (_ _:FUP)
  .
Declare Scope fup_scope.
Bind Scope fup_scope with FUP.
Notation "a '∧' b" := (fup_and a b) (at level 80, right associativity) : fup_scope.
Notation "a '∨' b" := (fup_or a b) (at level 85, right associativity) : fup_scope.

Fixpoint CupFup (fup : FUP) : CUP :=
  match fup with
  | fup_children_equal => cup_children_equal
  | fup_pulldownLL_in a => cup_pulldownLL_in (CupFup a)
  | fup_pulldownLR_in a => cup_pulldownLR_in (CupFup a)
  | fup_right_obeys a => cup_right_obeys (CupFup a)
  | fup_left_of a => cup_left_of (CupFup a)
  | fup_or a b => cup_or (CupFup a) (CupFup b)
  | fup_and a b => cup_and (CupFup a) (CupFup b)
  end.
Instance fup_as_cup : AsCUP FUP := {
    as_cup := CupFup
  }.
Hint Extern 5 => progress change (?as_cs (fup_children_equal)) with CsChildrenEqual in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_pulldownLL_in ?fup)) with (CsPulldownLLIn (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_pulldownLR_in ?fup)) with (CsPulldownLRIn (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_right_obeys ?fup)) with (CsRightObeys (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_left_of ?fup)) with (CsLeftOf (as_cs fup)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_or ?a ?b)) with (CsOr (as_cs a) (as_cs b)) in *; shelve : simplify.
Hint Extern 5 => progress change (?as_cs (fup_and ?a ?b)) with (CsAnd (as_cs a) (as_cs b)) in *; shelve : simplify.

Coercion CsFUP (fup : FUP) : ContextSet := CsCUP (CupFup fup).
Coercion CupFup : FUP >-> CUP.

Inductive FiniteTree T :=
  | ft_leaf (_:T)
  | ft_branch (_ _ : FiniteTree T)
  .
(* Arguments ft_branch {T}. *)
(* Declare Scope ft_scope.
Bind Scope ft_scope with FiniteTree. *)
Notation "( a , b )" := (ft_branch a b).

Instance ct_ft T : Context (FiniteTree T) := {
    ct_node_links := λ ft, match ft with
    | ft_leaf s => nl_leaf
    | ft_branch a b => nl_branch a b
    end
  }.
Definition ft_branch_is_branch T (ab a b : FiniteTree T) : IsBranch (a, b) a b := ltac:(constructor).
Hint Immediate ft_branch_is_branch : simplify.
Lemma ft_only_branch T (ab a b : FiniteTree T) : IsBranch ab a b -> ab = (a, b).
  unfold IsBranch; remember (ct_node_links ab).
  destruct 1; destruct ab.
  discriminate.
  injection Heqn as <- <-.
  reflexivity.
Qed.
Hint Extern 5 => progress match goal with
  | H : @IsBranch _ (ct_ft _) _ _ _ |- _ => apply ft_only_branch in H
  end; shelve : simplify.

Inductive FtBranchEmbeddedStuff T ab (ca cb : CompletedContext (FiniteTree T)) : Prop :=
  | ft_branch_embedded (a b : FiniteTree T) :
    ca = inl a ->
    cb = inl b ->
    ab = (a, b) ->
    FtBranchEmbeddedStuff ab ca cb.
Lemma extended_ft_branch T (ab : FiniteTree T) a b : IsBranch (inl ab) a b -> FtBranchEmbeddedStuff ab a b.
  unfold IsBranch; remember (ct_node_links (inl ab)).
  destruct 1; destruct ab as [uh | a0 b0].
  discriminate.
  injection Heqn as -> ->.
  econstructor; reflexivity.
Qed.
Hint Extern 5 => progress match goal with
  | H : @IsBranch _ _ (inl _) _ _ |- _ => destruct (extended_ft_branch H); clear H
  end; shelve : simplify.

Lemma ft_children_equal T (c : FiniteTree T) : CsChildrenEqual _ (c, c).
  econstructor. constructor.
Qed.
Hint Extern 1 (CsChildrenEqual _ (_, _)) => solve [apply ft_children_equal] : simplify.
Hint Extern 1 ((_, _) ∈ CsChildrenEqual) => solve [apply ft_children_equal] : simplify.
Lemma ft_children_equal_equal T (a b : FiniteTree T) : a = b -> CsChildrenEqual _ (a, b).
  intros <-.
  apply ft_children_equal.
Qed.
Hint Extern 2 (CsChildrenEqual _ (_, _)) => progress apply ft_children_equal_equal; shelve : simplify.
Hint Extern 1 ((_, _) ∈ CsChildrenEqual) => progress apply ft_children_equal_equal; shelve : simplify.

Inductive CsBranch (R S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_branch ab a b :
      IsBranch ab a b ->
      R _ _ a ->
      S _ _ b ->
      CsBranch R S _ ab.

Fixpoint CsFt S {scs : AsCS S} ft := match ft with
  | ft_leaf s => as_cs s
  | ft_branch a b => CsBranch (CsFt a) (CsFt b)
  end.

Instance ft_as_cs S {scs : AsCS S} : AsCS (FiniteTree S) := {
    as_cs := @CsFt _ _
  }.
(* Coercion CsFt : FiniteTree >-> ContextSet. *)
(* Coercion FtCs S {scs: AsCS S} (ft : FiniteTree S) := as_cs ft. *)
(* Print Graph. *)

Inductive CsLeftObeys (S : ContextSet) C (CT: Context C) : C -> Prop :=
  | cs_left_obeys ab a b : IsBranch ab a b -> S _ _ a -> CsLeftObeys S _ ab
  .
Definition cup_left_obeys (a : CUP) : CUP :=
  (cup_left_of (cup_right_obeys a ∧ (cup_pulldownLL_in cup_children_equal))).
Definition cup_branch (a b : CUP) : CUP :=
  (cup_left_obeys a) ∧ (cup_right_obeys b).
Fixpoint CupFt S {scup : AsCUP S} ft := match ft with
  | ft_leaf s => as_cup s
  | ft_branch a b => cup_branch (CupFt a) (CupFt b)
  end.

Instance ft_as_cup T {tcup : AsCUP T} : AsCUP (FiniteTree T) := {
    as_cup := @CupFt _ _
  }.

(* Definition finite_member_which_contains T (container : CUP) (member : FiniteTree T) (is_member : member ⋵ container) : FUP.
  induction container.
  exact fup_children_equal.
  destruct is_member. *)

Lemma finite_member_is_member_of_finite_subset T
  (container : CUP) (member : FiniteTree T) (is_member : (inl member) ⋵ container)
  : ∃ fcontainer : FUP, (fcontainer ⊑ container) ∧ (inl member ⋵ fcontainer).
  revert member is_member.
  (* Set Typeclasses Debug. *)
  induction container; intros.
  exists fup_children_equal; split; simplify; try intro; simplify.
  {
    simplify.
    (* TODO reduce duplicate code ID 3457u842h *)
    destruct (IHcontainer _ H2) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer.
    exists (fup_pulldownLL_in fc).
    split.
    {
      intro; simplify.
      econstructor; try eassumption.
      (* TODO: auto-apply member/subset stuff *)
      apply fc_in_cont; assumption.
    }
    {
      econstructor; simplify.
    }
  }
  {
    (* TODO reduce duplicate code ID 3457u842h *)
    simplify.
    destruct (IHcontainer _ H2) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer.
    exists (fup_pulldownLR_in fc).
    split.
    {
      intro; simplify.
      econstructor; try eassumption.
      (* TODO: auto-apply member/subset stuff *)
      apply fc_in_cont; assumption.
    }
    {
      econstructor; simplify.
    }
  }
  {
    (* TODO reduce duplicate code ID 3457u842h *)
    simplify.
    destruct (IHcontainer _ H0) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer.
    exists (fup_right_obeys fc).
    split.
    {
      intro; simplify.
      econstructor; try eassumption.
      (* TODO: auto-apply member/subset stuff *)
      apply fc_in_cont; assumption.
    }
    {
      econstructor; simplify.
    }
  }
  {
    (* TODO reduce duplicate code ID 3457u842h *)
    simplify.
    destruct (IHcontainer _ H0) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer.
    exists (fup_left_of fc).
    split.
    {
      intro; simplify.
      econstructor; try eassumption.
      (* TODO: auto-apply member/subset stuff *)
      apply fc_in_cont; assumption.
    }
    {
      econstructor; simplify.
    }
  }
  {
    (* TODO reduce duplicate code ID 3457u842h *)
    simplify.
    destruct is_member.
    {
      destruct (IHcontainer1 _ H) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer1.
      exists fc.
      split.
      { 
        intro; simplify. apply cs_or_left.
        apply fc_in_cont; assumption.
      }
      assumption.
    }
    {
      destruct (IHcontainer2 _ H) as (fc, (fc_in_cont, m_in_fc)); clear IHcontainer2.
      exists fc.
      split.
      {
        intro; simplify. apply cs_or_right.
        apply fc_in_cont; assumption.
      }
      assumption.
    }
  }
  {
    (* TODO reduce duplicate code ID 3457u842h *)
    simplify.
    destruct (IHcontainer1 _ H) as (fc1, (fc1_in_cont, m_in_fc1)); clear IHcontainer1.
    destruct (IHcontainer2 _ H0) as (fc2, (fc2_in_cont, m_in_fc2)); clear IHcontainer2.
    exists (fup_and fc1 fc2).
    split.
    {
      intro; simplify.
      econstructor; try eassumption.
      (* TODO: auto-apply member/subset stuff *)
      apply fc1_in_cont; assumption.
      apply fc2_in_cont; assumption.
    }
    {
      econstructor; simplify.
    }
  }
  {
    induction member.
    
  }

  Set Typeclasses Debug.
  destruct is_member.
    simplify.
  Set Printing Implicit.
  apply ft_only_branch in H.
  match goal with
  | H : @IsBranch _ (ct_ft _) _ _ _ |- _ => apply ft_only_branch in H
  end.
  remember abc.
  remember c.
  remember ab. destruct H.
  simplify.
  destruct (IHcontainer is_member). exists (fup_pulldownLL_in _); split; simplify.



Lemma cup_containing_cup_ft_members_also_has_them_as_subsets T {tcup : AsCUP T} (container : CUP) (member : FiniteTree T) :
  (member ⋵ container) -> member ⊆ container.
  repeat intro.
  induction container.
  induction ft; cbn in *.