Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Classes.SetoidDec.
Require Import Lists.SetoidList.
Require Import Nat.

Notation "[ e ]" := (exist _ e _).
(* Notation "[ e / f ]" := (exist _ e f). *)

Reserved Notation "a ∈ c" (at level 60, no associativity).
Reserved Notation "a ∉ c" (at level 60, no associativity).
Reserved Notation "a ∈? c" (at level 60, no associativity).

    
(*   note : for the moment , I'm deliberately doing proofs step-by-step , for my own learning, before trying to automate them
     *)
      
Lemma decide_left : ∀ (A B : Prop) (R : Type) (decision : {A} + {B}) (nb: ¬B) (r : R) (fa : A → R) (fb : B → R), r = match decision with left a => fa a | right b => fb b end → {a | r = fa a}.
  (* destruct decision.
  intros; exact (exist _ a H).
  intros; contradiction.
  Show Proof. *)
  intuition.
  exists a; assumption.
  (* exact (exist _ a H). *)
  Show Proof.
  Print sumbool_ind.
Qed.
Lemma decide_right : ∀ (A B : Prop) (R : Type) (decision : {A} + {B}) (na: ¬A) (r : R) (fa : A → R) (fb : B → R), r = match decision with left a => fa a | right b => fb b end → { b | r = fb b }.
  intuition.
  exists b; assumption.
Qed.

Lemma NoDupA_head : ∀ (A : Type) (eqA : A -> A -> Prop) (x : A) (l : list A), NoDupA eqA (x::l) → ¬ InA eqA x l.
  intuition.
  (* apply H in (NoDupA_cons (x:=x) (l:=l)) .
  destruct H. *)
  inversion H.
  contradiction.
Qed.

Lemma NoDupA_tail : ∀ (A : Type) (eqA : A -> A -> Prop) (x : A) (l : list A), NoDupA eqA (x::l) → NoDupA eqA l.
  intuition.
  inversion H.
  assumption.
Qed.

Lemma InA_tail : ∀ (A : Type) (eqA : A -> A -> Prop) (a x : A) (l : list A), InA eqA a (x::l) → (¬ eqA a x) → InA eqA a l.
  intuition.
  inversion H.
  contradiction.
  assumption.
Qed.

Lemma contrapositive : ∀ A B : Prop, (A → B) → ¬ B → ¬ A.
  tauto.
Qed.

Definition sig_apply (A: Type) (P: A → Prop) : ∀ (s : sig P) (R: Type), (∀ (a: A) (p : P a), (s = exist _ a p) → R) → R :=
  λ s _, match s with exist a p => λ f, f a p eq_refl end.

Class Container (A : Type) (So : Setoid A) (C : Type) := {
  contains : A → C → Prop ;
  contains_dec : ∀ (a : A)(c : C), {contains a c} + {¬contains a c} ;
  contains_respectsEquiv : ∀ a b c, a == b → contains a c → contains b c ;
  }.
  
Notation "a ∈ c" := (contains a c) (at level 60, no associativity) : type_scope.
Notation "a ∉ c" := (¬contains a c) (at level 60, no associativity) : type_scope.
Notation "a ∈? c" := (contains_dec a c) (at level 60, no associativity) : type_scope.

Section UniqueContainerInterface.
  Variable A : Type.
  Context (So : Setoid A).
  Variable C : Type.
  Context (CC : Container So C).
  
  (* Definition insertResult (a:A) (c:C) : Type := {c' | (a ∈ c') ∧ (∀ (b:A) (_:b =/= a), (b ∈ c') ↔ (b ∈ c))}.
  Definition removeResult (a:A) (c:C) : Type := {c' | (a ∉ c') ∧ (∀ (b:A) (_:b =/= a), (b ∈ c') ↔ (b ∈ c))}. *)
  
  Class UniqueContainer := {
    empty : C ;
    insert : ∀ [a:A] [c:C], a ∉ c → C;
    remove : ∀ [a:A] [c:C], a ∈ c → C;
    
    insert_works : ∀ [a:A] [c:C] (nc: a ∉ c), a ∈ (insert nc);
    remove_works : ∀ [a:A] [c:C] (yc: a ∈ c), a ∉ (remove yc);
    
    empty_containsNothing : ∀ a, a ∉ empty;
    insert_noSideEffects : ∀ [a:A] [c:C] (nc: a ∉ c),
      ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (insert nc));
    remove_noSideEffects : ∀ [a:A] [c:C] (yc: a ∈ c),
      ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (remove yc));
    }.
    
  Context {UC : UniqueContainer}.
    
  Definition tryInsert (a:A) (c:C) : (C * (a ∉ c))%type + {a ∈ c} := 
    match a ∈? c with
      | left yc => inright yc
      | right nc => inleft (insert nc, nc) 
    end.
    
  Definition tryRemove (a:A) (c:C) : (C * (a ∈ c))%type + {a ∉ c} := 
    match a ∈? c with
      | left yc => inleft (remove yc, yc) 
      | right nc => inright nc
    end.
  
  
  Remark tryInsert_left : ∀ (a:A) (c:C) (c' : C) (nc: a ∉ c), inleft (c', nc) = (tryInsert a c) → c' = insert nc.
    unfold tryInsert.
    intros.
    apply decide_right in H.
    inversion H.
    Set Keep Proof Equalities.
    injection H0.
    intuition.
    rewrite H1; assumption.
    assumption.
  Qed.
  
  
  Lemma insert_noSideEffects_proj1 : ∀ (a : A) (c : C) (nc : a ∉ c) (b : A), b =/= a → b ∈ c → b ∈ insert nc.
    intros; apply (proj1 (insert_noSideEffects nc H)); assumption.
  Qed.
  
  Lemma insert_noSideEffects_proj2 : ∀ (a : A) (c : C) (nc : a ∉ c) (b : A), b =/= a → b ∈ insert nc → b ∈ c.
    intros; apply (proj2 (insert_noSideEffects nc H)); assumption.
  Qed.
  
  Lemma remove_noSideEffects_proj1 : ∀ (a : A) (c : C) (yc : a ∈ c) (b : A), b =/= a → b ∈ c → b ∈ remove yc.
    intros; apply (proj1 (remove_noSideEffects yc H)); assumption.
  Qed.
  
  Lemma remove_noSideEffects_proj2 : ∀ (a : A) (c : C) (yc : a ∈ c) (b : A), b =/= a → b ∈ remove yc → b ∈ c.
    intros; apply (proj2 (remove_noSideEffects yc H)); assumption.
  Qed.
End UniqueContainerInterface.

Section UniqueList.
  Variable A : Type.
  Context {So : Setoid A}.
  Context {ED : EqDec So}.
  
  Local Definition eq : A → A → Prop := SetoidClass.equiv.
  
  Lemma neq_sym : ∀ (a b : A), a =/= b → b =/= a.
    intuition.
  Qed.
  Lemma eq_sym : ∀ (a b : A), a == b → b == a.
    intuition.
  Qed.
  
  Definition UniqueList : Type := sig (NoDupA eq).
  (* #[local] Definition C : Type := UniqueList. *)
  Notation "'C'" := UniqueList.
  
  Hint Extern 1 => match goal with
    | [c : C |- _] => destruct c
    | [e : context[_ ∈ _] |- _] => simpl in e
    | [e : context[_ ∉ _] |- _] => simpl in e
  end : unique_list.
  (* Hint Extern 5 => match goal with
    | [H : _ ∈ _ |- _] => inversion_clear H
    (* | [H : _ ∉ _ |- _] => inversion_clear H
    | [H : _ ∈ _ → False |- _] => inversion_clear H *)
  end : unique_list. *)
  Lemma InA_nil' (a : A) : ¬ InA eq a nil.
    exact (proj1 (InA_nil eq a)).
  Qed.
  Hint Immediate InA_nil' : unique_list.
  Hint Extern 1 (_ ∈ _) => simpl : unique_list.
  Hint Extern 1 (_ ∉ _) => simpl : unique_list.
    
  Lemma InA_cons_nequiv (a x : A) (xs : list A) : a =/= x → InA eq a (x :: xs) → InA eq a xs.
    intros anx H; inversion H; auto with exfalso crelations.
  Qed.
  Hint Resolve InA_cons_nequiv : unique_list.
  Lemma InA_eqA' : ∀ (l : list A) (x y : A), eq x y → InA eq x l → InA eq y l.
    exact (InA_eqA setoid_equiv).
  Qed.
  Hint Resolve InA_eqA' : unique_list.
  
  Lemma InA_same_head : ∀ (a x : A) (xs ys : list A), (InA eq a xs → InA eq a ys) → InA eq a (x::xs) → InA eq a (x::ys).
    intros a x xs ys tail_map H; inversion H; auto.
  Qed.
  Hint Resolve InA_same_head : unique_list.
  (* Hint Extern 1 (InA eq ?b ?xs) => match goal with
    | [H : b ∈ [?x :: xs] |- _] => apply InA_cons_neq
    (* | [H : _ ∉ _ |- _] => inversion_clear H
    | [H : _ ∈ _ → False |- _] => inversion_clear H *)
  end : unique_list. *)
  
  Instance UniqueList_Container : Container So UniqueList := {
    contains := λ a c, InA eq a (proj1_sig c) ;
    contains_dec := λ a c, InA_dec equiv_dec a (proj1_sig c) ;
    contains_respectsEquiv := λ a b c e, InA_eqA setoid_equiv (l:=proj1_sig c) e
    }.
    
  Definition UniqueList_empty : C := exist _ nil (NoDupA_nil eq).
  
  Lemma UniqueList_empty_containsNothing : ∀ a, a ∉ UniqueList_empty.
    auto with unique_list.
  Qed.
  Definition UniqueList_insert : ∀ (a:A) (c:C), a ∉ c → C.
    refine (λ a c nc, [a :: proj1_sig c]).
    auto with unique_list.
  Defined.
  
  Lemma UniqueList_insert_works : ∀ (a:A) (c:C) (nc: a ∉ c), a ∈ (UniqueList_insert nc).
    auto with crelations unique_list.
  Qed.
  
  Lemma UniqueList_insert_noSideEffects : ∀ (a:A) (c:C) (nc: a ∉ c),
    ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (UniqueList_insert nc)).
    intuition eauto with unique_list.
  Qed.
  
  Definition RemoveResult (a:A) (c:C) : Type := {c' | (a ∉ c') ∧ (∀ b:A, b =/= a → (b ∈ c) ↔ (b ∈ c'))}.
  
  Definition UniqueList_remove_head : ∀ (a x : A) (xs : list A) (nd : ¬ InA eq x xs) (nds : NoDupA eq xs), eq a x → RemoveResult a (exist _ (x :: xs) (NoDupA_cons nd nds)).
    refine (λ a x xs nd nds aex, [exist _ xs nds]).
    Hint Resolve nequiv_equiv_trans : unique_list.
    intuition eauto with unique_list.
  Defined.
  
  Definition UniqueList_remove_tail : ∀ (a x : A) (xs : list A) (nd : ¬ InA eq x xs) (nds : NoDupA eq xs), a =/= x → RemoveResult a (exist _ xs nds) → RemoveResult a (exist _ (x :: xs) (NoDupA_cons nd nds)).
    refine (λ a x xs nd nds anx tail', [[x :: proj1_sig (proj1_sig tail')]]).
    Unshelve.
    Hint Immediate neq_sym : unique_list.
    all: destruct tail' as (c', proofs); destruct c' as (xs', nds'); destruct proofs as (aNotInC, noSideEffects); pose (λ b bna, proj1 (noSideEffects b bna)); pose (λ b bna, proj2 (noSideEffects b bna)); simpl in *; intuition (eauto with unique_list).
  Defined.
  
  Definition UniqueList_remove_aux : ∀ (a:A) (l: list A) (nd : NoDupA eq l), a ∈ (exist _ l nd) → RemoveResult a (exist _ l nd).
    refine (λ a, fix remove l := match l with
        | nil => λ nd aInL, match _ in False with end
        | x::xs => λ nd aInL, match equiv_dec a x with
          | left aex => UniqueList_remove_head a (NoDupA_head nd) (NoDupA_tail nd) aex
          | right anx => let tail' := remove xs (NoDupA_tail nd) (InA_tail aInL anx) in UniqueList_remove_tail (NoDupA_head nd) anx tail'
          end
        end).
    exact (proj1 (InA_nil eq a) aInL).
  Defined.
  
  Definition UniqueList_remove : ∀ (a:A) (c:C), a ∈ c → C :=
    λ a c aInC, proj1_sig (UniqueList_remove_aux (nd:=proj2_sig c) aInC).
  
  Lemma UniqueList_remove_works : ∀ (a:A) (c:C) (yc: a ∈ c), a ∉ (UniqueList_remove yc).
    intros a c yc H.
    exact (proj1 (proj2_sig (UniqueList_remove_aux (nd:=proj2_sig c) yc) ) H).
  Qed.
  
  Lemma UniqueList_remove_noSideEffects : ∀ (a:A) (c:C) (yc: a ∈ c),
    ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (UniqueList_remove yc)).
    intros a c yc.
    exact (proj2 (proj2_sig (UniqueList_remove_aux (nd:=proj2_sig c) yc) )).
  Qed.
    
    
  Instance UniqueList_UniqueContainer : UniqueContainer UniqueList_Container := {
      empty := UniqueList_empty ;
      insert := UniqueList_insert ;
      remove := UniqueList_remove ;
      
      insert_works := UniqueList_insert_works ;
      remove_works := UniqueList_remove_works ;
      
      empty_containsNothing := UniqueList_empty_containsNothing;
      insert_noSideEffects := UniqueList_insert_noSideEffects;
      remove_noSideEffects := UniqueList_remove_noSideEffects;
    }.
  
End UniqueList.

Hint Immediate UniqueList_Container : typeclass_instances.
Hint Immediate UniqueList_UniqueContainer : typeclass_instances.

Section Hashable.
  Variable A : Type.
  Context (So : Setoid A).
  
  Class Hashable := {
    hashOf : A → nat ;
    hashOf_respectsEquiv : ∀ a b, a == b → hashOf a = hashOf b
    }.
End Hashable.


Section SetoidMap.
  Variable A B : Type.
  Variable M : B → A.
  Context {So : Setoid A}.
  Context {ED : EqDec So}.
  
  Definition SetoidMap_equiv : relation B := λ x y, SetoidClass.equiv (M x) (M y).

  Instance SetoidMap_setoid_equiv : Equivalence SetoidMap_equiv.
    constructor.
    exact (λ x, reflexivity (M x)).
    exact (λ x y, symmetry (x:=M x) (y:=M y)).
    exact (λ x y z, transitivity (x:=M x) (y:=M y) (z:=M z)).
  Defined.
  
  Instance SetoidMap_Setoid : Setoid B := {
    equiv := SetoidMap_equiv;
    setoid_equiv := SetoidMap_setoid_equiv
    }.
   
  Instance SetoidMap_EqDec : EqDec SetoidMap_Setoid := {
    equiv_dec := λ x y, equiv_dec (M x) (M y);
    }.
End SetoidMap.
Hint Immediate SetoidMap_Setoid : typeclass_instances.
Hint Immediate SetoidMap_EqDec : typeclass_instances.

Require Import Vector.

Lemma vector_nth_replace : ∀ (A : Type) (n : nat) (p : Fin.t n) (v : Vector.t A n) (a : A),
  nth (replace v p a) p = a.
  induction p; intros; rewrite 2 (eta v); simpl; auto.
Qed.


Lemma vector_nth_replace_different : ∀ (A : Type) (n : nat) (p q : Fin.t n) (v : Vector.t A n) (a : A), p ≠ q → nth (replace v p a) q = nth v q.
  refine(fix f {A} {n} (p : Fin.t n) {struct p} :=
    match p in Fin.t pn return ∀ (q : Fin.t pn) (v : Vector.t A pn) (a : A), p ≠ q → nth (replace v p a) q = nth v q with
    | Fin.F1 p'n => _
    | Fin.FS p'n p' => let fp' := @f A p'n p' in _
    end).
  
  clear p n.
  refine (λ q : Fin.t (S p'n), match q in Fin.t (S q'n) return ∀ (v : Vector.t A (S q'n)) (a : A), (Fin.F1 (n:=q'n)) ≠ q → nth (replace v (Fin.F1 (n:=q'n)) a) q = nth v q with
      | Fin.F1 q'n => λ v pnq, _
      | Fin.FS q'n q' => _
      end).
      
  contradiction.
  intros; rewrite 2 (eta v); simpl; reflexivity.
      
  (* clear p n. *)
  refine (λ q : Fin.t (S p'n), match q in Fin.t (S q'n) return ∀ (p'' : Fin.t q'n) (fp''
 : ∀ (q : Fin.t q'n) (v : t A q'n) (a : A),
     p'' ≠ q → nth (replace v p'' a) q = nth v q) (v : Vector.t A (S q'n)) (a : A), (Fin.FS (n:=q'n) p'') ≠ q → nth (replace v (Fin.FS p'') a) q = nth v q with
      | Fin.F1 q'n => λ p'' fp'' v a pnq, _
      | Fin.FS q'n q' => λ p'' fp'' v a pnq, _
      end p' fp'); rewrite 2 (eta v); simpl.
  reflexivity.
  apply fp''; congruence.
Qed.

Section FixedSizeHashSet.
  Variable A : Type.
  (* Variable Bucket : ∀ (A : Type) (So : Setoid A) (ED : EqDec So) → {c | UniqueContainer (So:=So) (CC:=c)}. *)
  Context {So : Setoid A}.
  Context {ED : EqDec So}.
  Context {Dig : Hashable So}.
  Variable maxDigest : nat.
  
  Definition Bucket : Type := UniqueList (So :=So).
  Definition numBuckets : nat := S maxDigest.
  Definition Digest : Set := Fin.t numBuckets.
  Definition digestOf (a : A) : Digest := Fin.of_nat_lt (PeanoNat.Nat.mod_upper_bound (hashOf a) numBuckets (PeanoNat.Nat.neq_succ_0 maxDigest)).
  Lemma digestOf_respectsEquiv : ∀ a b, a == b → digestOf a = digestOf b.
    intros; cbv [digestOf]; rewrite (hashOf_respectsEquiv a b H); reflexivity.
  Qed.
  
  (* At first I wrote {bs : Vector.t Bucket numBuckets | ∀ n a , a ∈ nth bs n → digestOf a = n}, but we don't actually need the condition - by the definition of `contains`, the elements only *count* if they're in the correct bucket. *)
  Definition FixedSizeHashSet : Type := Vector.t Bucket numBuckets.
  Notation "'C'" := FixedSizeHashSet.
  
  Definition FixedSizeHashSet_contains := λ a (c : C), a ∈ nth c (digestOf a).
   
  Lemma FixedSizeHashSet_contains_nth (a : A) (c : C) : FixedSizeHashSet_contains a c = a ∈ nth c (digestOf a).
    reflexivity.
  Qed.
  Lemma FixedSizeHashSet_contains_respectsEquiv : ∀ a b c, a == b → FixedSizeHashSet_contains a c → FixedSizeHashSet_contains b c.
    intros a b c aeb.
    pose (contains_respectsEquiv a b (nth c (digestOf a)) aeb).
    repeat rewrite FixedSizeHashSet_contains_nth.
    rewrite <- (digestOf_respectsEquiv a b aeb).
    assumption.
  Qed.
  
  Instance FixedSizeHashSet_Container : Container So FixedSizeHashSet := {
    contains := λ a c, a ∈ nth c (digestOf a) ;
    contains_dec := λ a c, a ∈? (nth c (digestOf a)) ;
    contains_respectsEquiv := FixedSizeHashSet_contains_respectsEquiv ;
    }.
   
  (* Lemma FixedSizeHashSet_contains_nth (a : A) (c : C) : a ∈ c = a ∈ nth c (digestOf a).
    reflexivity.
  Qed. *)
  
  Ltac simplify := 
    repeat progress (intuition idtac; repeat match goal with
      | [H : C |- _] => destruct H
      | [H : {_ | _} |- _] => destruct H
      (* | [bna : ?b =/= ?a |- _] => match goal with
        | [H : digestOf b = digestOf a |- _] => fail 1
        | [H : digestOf b ≠ digestOf a |- _] => fail 1
        | _ => destruct (Fin.eq_dec (digestOf b) (digestOf a))
      end *)
      (* | [H : nth (replace _ ?d _) ?n |- _] => split on d?=n *)
    end; autorewrite with hashset in *; cbv [proj1_sig] in *).
  
  Ltac automatic := 
    simplify ; eauto with hashset exfalso.
    
  Hint Rewrite FixedSizeHashSet_contains_nth : hashset.
  Hint Rewrite Vector.const_nth : hashset.
  Lemma UniqueList_empty_containsNothing' :
∀ (A : Type) (So : Setoid A) (ED : EqDec So) (a : A), a ∈ UniqueList_empty (A:=A) → False.
    exact UniqueList_empty_containsNothing.
  Qed.
  Hint Resolve UniqueList_empty_containsNothing' : hashset.
  
  Definition FixedSizeHashSet_empty : C := Vector.const (UniqueList_empty (So:=So)) numBuckets.
  
  Lemma FixedSizeHashSet_empty_nth n : nth FixedSizeHashSet_empty n = UniqueList_empty (So:=So).
    cbv [FixedSizeHashSet_empty]; automatic.
  Qed.
  
  Lemma FixedSizeHashSet_empty_containsNothing : ∀ a, a ∉ FixedSizeHashSet_empty.
    cbv [FixedSizeHashSet_empty]; automatic.
  Qed. 
  
  Hint Rewrite vector_nth_replace : hashset.
  (* Note: we can't `Hint Rewrite vector_nth_replace_different` because it'll infinite loop by generating d ≠ n goals even when there is no way to resolve them *)
  
  Ltac split_sameOrDifferentElement := 
    match goal with
    | [a : A, b : A |- _] => destruct (equiv_dec b a) as [bea|bna]; try rewrite (digestOf_respectsEquiv b a bea)
    end.
  
  Ltac split_sameOrDifferentBucket := 
    match goal with
    | [a : A, b : A |- _] => destruct (Fin.eq_dec (digestOf b) (digestOf a))
    end.
  Hint Immediate eq_sym : hashset.
  Hint Immediate neq_sym : hashset.
  
  Definition FixedSizeHashSet_insert : ∀ (a:A) (c:C), a ∉ c → C.
    refine (λ a c nc,
      let d := digestOf a in
      let anb : a ∉ nth c d := _ in
      replace c d (insert anb)); automatic.
  Defined.
  
  Lemma FixedSizeHashSet_insert_works : ∀ (a:A) (c:C) (nc: a ∉ c), a ∈ (FixedSizeHashSet_insert nc).
    cbv [FixedSizeHashSet_insert].
    simplify.
    apply insert_works.
  Qed.
  
  Lemma FixedSizeHashSet_insert_noSideEffects : ∀ (a:A) (c:C) (nc: a ∉ c),
    ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (FixedSizeHashSet_insert nc)).
    cbv [FixedSizeHashSet_insert].
    intros; split_sameOrDifferentBucket.
    (* " different element in same bucket " case *)
    Hint Rewrite vector_nth_replace : hashset.
    match goal with
    | [bna : ?b =/= ?a, dbeda : digestOf ?b = digestOf ?a |- _] => pose (UniqueList_insert_noSideEffects nc bna); simplify; rewrite dbeda in *; automatic
    end.
    (* " different bucket " case *)
    simplify; rewrite vector_nth_replace_different in *; automatic.
  Qed.
  
  Definition FixedSizeHashSet_remove : ∀ (a:A) (c:C), a ∈ c → C.
    refine (λ a c nc,
      let d := digestOf a in
      let aeb : a ∈ nth c d := _ in
      replace c d (remove aeb)); automatic.
  Defined.
  
  Lemma FixedSizeHashSet_remove_works : ∀ (a:A) (c:C) (yc: a ∈ c), a ∉ (FixedSizeHashSet_remove yc).
    cbv [FixedSizeHashSet_remove].
    simplify.
    simple eapply remove_works.
    exact H.
  Qed.
  
  Lemma FixedSizeHashSet_remove_noSideEffects : ∀ (a:A) (c:C) (yc: a ∈ c),
    ∀ (b:A), b =/= a → (b ∈ c) ↔ (b ∈ (FixedSizeHashSet_remove yc)).
    cbv [FixedSizeHashSet_remove].
    intros; split_sameOrDifferentBucket.
    (* " different element in same bucket " case *)
    Hint Rewrite vector_nth_replace : hashset.
    match goal with
    | [bna : ?b =/= ?a, dbeda : digestOf ?b = digestOf ?a |- _] => pose (UniqueList_remove_noSideEffects yc bna); simplify; rewrite dbeda in *; automatic
    end.
    (* " different bucket " case *)
    simplify; rewrite vector_nth_replace_different in *; automatic.
  Qed.
    
    
  Instance FixedSizeHashSet_UniqueContainer : UniqueContainer FixedSizeHashSet_Container := {
      empty := FixedSizeHashSet_empty ;
      insert := FixedSizeHashSet_insert ;
      remove := FixedSizeHashSet_remove ;
      
      insert_works := FixedSizeHashSet_insert_works ;
      remove_works := FixedSizeHashSet_remove_works ;
      
      empty_containsNothing := FixedSizeHashSet_empty_containsNothing;
      insert_noSideEffects := FixedSizeHashSet_insert_noSideEffects;
      remove_noSideEffects := FixedSizeHashSet_remove_noSideEffects;
    }.
  
End FixedSizeHashSet.

Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Import ListNotations.
Import C.Notations.
    Require Import String.
    Require Import Ascii.
Definition StringSetoid : Setoid LString.t := eq_setoid LString.t.
Definition StringSet := @FixedSizeHashSet LString.t StringSetoid 16.
Instance LString_Hashable : Hashable StringSetoid := {
    hashOf := λ s, Datatypes.length s ;
    hashOf_respectsEquiv := f_equal (@Datatypes.length Ascii.ascii) ;
  }.
Definition StringSet_Container := @FixedSizeHashSet_Container LString.t.
Definition StringSet_UniqueContainer := @FixedSizeHashSet_UniqueContainer LString.t StringSetoid (list_eq_dec ascii_dec) LString_Hashable 16.
    
Fixpoint loop (i : nat) : StringSet -> C.t System.effect unit :=
  λ set,
  match i with
  | O => ret tt
  | (S i') =>
    do! System.log (LString.s "Enter a value to insert :") in
    let! newopt := System.read_line in
    match newopt with
      | None => do! System.log (LString.s "read_line returned None.") in loop i' set
      | Some new =>
        match tryInsert (UC:=StringSet_UniqueContainer) new set with
        | inleft (new_set, _) => do! System.log (LString.s "Inserted `" ++ new ++ LString.s "`.") in loop i' new_set
        | inright _ => do! System.log (LString.s "`" ++ new ++ LString.s "` was already in the set!") in loop i' set
        end
      end
  end.
Definition main' (argv : list LString.t) : C.t System.effect unit :=
  loop 100 (@FixedSizeHashSet_empty LString.t StringSetoid 16).

Definition main := Extraction.launch main'.
Extraction "UniqueContainersTest" main.

(* From Coq Require Extraction.
Recursive Extraction FixedSizeHashSet_insert.
Extraction "test.ml" FixedSizeHashSet_insert. *)

