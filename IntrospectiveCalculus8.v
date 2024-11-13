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
Set Typeclasses Iterative Deepening.
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
Ltac simplify := autouse_shelving_db 20 ident:(simplify); trivial.

(* One notable simplification step is to rewrite equality hypotheses when one side is just another hypothesis. *)
Hint Extern 6 => progress match goal with
  | H : _ |- _ => match goal with
    | eq : H = _ |- _ => rewrite eq in *; clear eq
    | eq : _ = H |- _ => rewrite <- eq in *; clear eq
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
    cc_ct : Context C
  ; cc_complete : ∀ E (ES : Extension C E), ∃ EE : Embedding C E, EmbeddingAgrees EE
  }.

(****************************************************
            Example of complete context
****************************************************)

(* Most of our theorems are of the form "for all complete context types...", and don't actually require us to *construct* a complete context type. But let's at least demonstrate that it's possible. *)

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
  apply H0. apply H. assumption.
  apply H. apply H0. assumption.
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
  
Instance up_as_cs : AsCS UnificationPredicate := {
    as_cs := λ up _ _ c, CtxObeysUP _ c up
  }.

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