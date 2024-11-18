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

(****************************************************
                   Tree structure
****************************************************)

Inductive Location :=
  | l_root : Location
  | l_left : Location -> Location
  | l_right : Location -> Location
  .

Fixpoint l_extend (l : Location) (extension : Location) := match l with 
  | l_root => extension
  | l_left l => l_left (l_extend l extension)
  | l_right l => l_right (l_extend l extension)
  end.

Definition l_left_child := l_extend (l_left l_root).
Definition l_right_child := l_extend (l_right l_root).

(****************************************************
                   Unifications
****************************************************)

Definition LRelation :=
  Location -> Location -> Prop.

Definition LRTransitive (R : LRelation) := ∀ a b c, R a b -> R b c -> R a c.

Class Unifications (U : LRelation) : Prop := {
      uv_means_you_can_rewrite : ∀ l m,
        U l m <-> (
          ∀ n, (U n l -> U n m) ∧ (U l n -> U m n)
        )
    ; uv_respects_subtrees : ∀ l m,
        U l m <->
        (U (l_left_child l) (l_left_child m) ∧
        U (l_right_child l) (l_right_child m))
  }.

Class Derives A B := {
    derives : A -> B -> Prop
  }.
Notation "P '⊢' Q" := (derives P Q) (at level 70, no associativity)
  : type_scope.
Definition equiv A B {_dab : Derives A B} {_dba : Derives B A} (a:A) (b:B) := derives a b ∧ derives b a.
Notation "P '⊣⊢' Q" := (equiv P Q) (at level 70, no associativity)
  : type_scope.

Definition UNaiveSubset (A B : LRelation) :=
  ∀ l m, A l m -> B l m.
  
Instance d_u : Derives LRelation LRelation := {
    derives := UNaiveSubset
  }.

Definition MinimumUnificationsContaining (R : LRelation) : LRelation
  := λ l m, ∀ U, R ⊢ U -> Unifications U -> U l m.

(* Instance MUC_U R : Unifications (MinimumUnificationsContaining R).
  unfold MinimumUnificationsContaining; constructor; intuition idtac.
  {
    pose (H0 _ H1 H2) as unl.
    pose (H _ H1 H2) as ulm.
    destruct H2.
    apply (uv_means_you_can_rewrite0 l m); assumption.
  }
  {
    pose (H0 _ H1 H2) as uml.
    pose (H _ H1 H2) as uln.
    destruct H2.
    apply (uv_means_you_can_rewrite0 l m); assumption.
  }
  {
    destruct (H l).
    apply H3.
    }
Qed. *)


Definition USet := LRelation -> Prop.


Class USValid US := {
    usv_members_valid : ∀ U, US U -> Unifications U
  ; usv_contains_subsets: ∀ U1 U2,
      UNaiveSubset U1 U2 -> US U1 -> US U2
  }.
  
Definition USNaiveSuperset (A B : USet) :=
  ∀ u, B u -> A u.

Instance d_us : Derives USet USet := {
    derives := USNaiveSuperset
  }.


(****************************************************
                Reified unifications
****************************************************)

Inductive RUS :=
  | rus_unify_children
  | rus_pullL (_:RUS)
  | rus_pushR (_:RUS)
  | rus_pushLL (_:RUS)
  | rus_pushLR (_:RUS)
  | rus_union (_ _:RUS)
  | rus_require_both (_ _:RUS)
  | rus_iterate (base step:RUS)
  .
Declare Scope rus_scope.
Bind Scope rus_scope with RUS.


Inductive LeftToRight : LRelation :=
  | u_children_equal : LeftToRight (l_left l_root) (l_right l_root).
Definition UUnifyChildren := MinimumUnificationsContaining LeftToRight.

Inductive USSingleton (U : LRelation) : USet :=
  | us_singleton V : U ⊢ V -> USSingleton U V.

Definition USUnifyChildren := USSingleton UUnifyChildren.

(* Inductive URightObeys (U : LRelation) : LRelation :=
  | u_right_obeys l m : U l m -> URightObeys U (l_right l) (l_right m).

Inductive ULeftOf (U : LRelation) : LRelation :=
  | u_left_of l m : U (l_left l) (l_left m) -> ULeftOf U l m. *)
(* Definition LocationCorrespondence := Location -> Location -> Prop. *)
Inductive UChangeLocations (R : LRelation) (U : LRelation) : LRelation :=
  | u_change_locations_in l1 l2 m1 m2 :
    R l1 l2 -> R m1 m2 -> U l1 m1 ->
      UChangeLocations R U l2 m2.

Inductive PushLL : LRelation :=
  | pushll_left l : PushLL (l_left l) (l_left (l_left l))
  | pushll_right l : PushLL (l_right l) (l_right l).

Inductive PushLR : LRelation :=
  | pushlr_left l : PushLR (l_left l) (l_left (l_right l))
  | pushlr_right l : PushLR (l_right l) (l_right l).

Inductive PushR : LRelation := pushr l : PushR l (l_right l).
Inductive PullL : LRelation := pulll l : PullL (l_left l) l.

(* Inductive UMapLocations (map : Location -> Location) (U : LRelation) : LRelation :=
  | u_pulldownLLin l m : U l m -> UMapLocations map U (map l) (map m). *)

Definition UPullL := UChangeLocations PullL.
Definition UPushR := UChangeLocations PushR.
Definition UPushLL := UChangeLocations PushLL.
Definition UPushLR := UChangeLocations PushLR.

Inductive USApplyInAllCases (map : LRelation -> LRelation) (US : USet) : USet :=
  us_apply_in_all_cases u : US u -> USApplyInAllCases map US (map u).
Definition USPullL := USApplyInAllCases UPullL.
Definition USPushR := USApplyInAllCases UPushR.
Definition USPushLL := USApplyInAllCases UPushLL.
Definition USPushLR := USApplyInAllCases UPushLR.

Definition USUnion (A B : USet) : USet := λ u, A u ∨ B u.
(* Definition USRequireBoth (A B : USet) : USet := λ u, A u ∨ B u. *)
Inductive USRequireBoth (A B : USet) : USet :=
  | us_require_both a b c :
      A a -> B b -> (a ⊢ c) -> (b ⊢ c) ->
      LRTransitive c -> USRequireBoth A B c.

Inductive USIterate (Base Step : USet) : USet :=
  (* | usi_base Base :
      Base B -> USIterate Base Step B *)
  (* | usi_base : (USIterate Base Step) ⊢ Base *)
  | usi_base :
      USNaiveSuperset (USIterate Base Step) Base
  (* | usi_iterate :
      USNaiveSuperset (USIterate Base Step)
        (λ Tail, USRequireBoth Step (USPushR Tail)) *)
  (* | usi_iterate Tail S Combined :
      Step S -> USIterate Base Step Tail ->
      (S ⊢ Combined) -> (UPushR Tail ⊢ Combined) ->
      USIterate Base Step Combined *)
  | usi_iterate :
      USNaiveSuperset (USIterate Base Step) 
        (USRequireBoth Step (USPushR (USIterate Base Step)))
  .

Fixpoint UsRus rus := match rus with
  | rus_unify_children => USUnifyChildren
  | rus_pullL a => USPullL (UsRus a)
  | rus_pushR a => USPushR (UsRus a)
  | rus_pushLL a => USPushLL (UsRus a)
  | rus_pushLR a => USPushLR (UsRus a)
  | rus_union a b => USUnion (UsRus a) (UsRus b)
  | rus_require_both a b => USRequireBoth (UsRus a) (UsRus b)
  | rus_iterate base step => USIterate (UsRus base) (UsRus step)
  end.

  
(****************************************************
                Finitude or something
****************************************************)

Inductive FiniteTree T :=
  | ft_leaf (_:T)
  | ft_branch (_ _ : FiniteTree T)
  .

Inductive FtEqualities : FiniteTree T -> LRelation :=
  λ l m, 