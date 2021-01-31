(* Some attempts to build an effect system for my code generation *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Notation "x × y" := (prod x y) (at level 60, right associativity) : type_scope.
Require Import List.
Import EqNotations.
Require Import Coq.Program.Equality.

Definition Step State : Type := State → State → Prop.
Definition Partition P A B
  (SP : Step P) (SA : Step A) (SB : Step B)
  (MA : P → A) (MB : P → B)
  (p : P) : Prop :=
  ∀ n, SP p n →
    (SA (MA p) (MA n) ∧ MB p = MB n) 
    ∨
    (SB (MB p) (MB n) ∧ MA p = MA n).
    
Definition Isolate P C
  (SP : Step P) (SC : Step C)
  (M : P → C)
  (p : P) : Prop :=
  ∀ n, SP p n → SC (M p) (M n).

(* Inductive History A (SA : Step A) : list A → Prop :=
| HistoryInitial : ∀ initial , History SA (initial :: nil)
| HistoryStep : ∀ x y l, SA x y → History SA (x :: l) → History SA (y :: x :: l). *)

Inductive History A (SA : Step A) (initial : A) : ∀ final : A, Prop :=
| HistoryInitial : History SA initial initial
| HistoryStep : ∀ x y, SA x y → History SA initial x → History SA initial y.

(* Inductive IsolateHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) : list P → Prop :=
| IsolateHistoryInitial : ∀ initial , IsolateHistory SP SC M (initial :: nil)
| IsolateHistoryStep : ∀ x y l, SP x y → SC (M x) (M y) → IsolateHistory SP SC M (x :: l) → IsolateHistory SP SC M (y :: x :: l). *)

Inductive IsolateHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) : ∀ final : P, Prop :=
| IsolateHistoryInitial : IsolateHistory SP SC M initial initial
| IsolateHistoryStep : ∀ x y, SP x y → SC (M x) (M y) → IsolateHistory SP SC M initial x → IsolateHistory SP SC M initial y.

Lemma parentHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) (final : P) : IsolateHistory SP SC M initial final → History SP initial final.
  intros; induction H.
  constructor.
  apply (HistoryStep _ H); assumption.
Qed.

Lemma childHistory P C
  (SP : Step P) (SC : Step C)
  (M : P → C) (initial : P) (final : P) : IsolateHistory SP SC M initial final → History SC (M initial) (M final).
  intros; induction H.
  constructor.
  apply (HistoryStep _ H0); assumption.
Qed.

(* Definition NonNullStep A (SA : Step A) : Step A := λ x y, SA x y ∧ x ≠ y. *)
Lemma RemoveNullSteps A (SA : Step A) (NonNullSA : Step A) (null_dec : ∀ x y : A, SA x y → NonNullSA x y ∨ x = y) i f : History SA i f → History NonNullSA i f.
  intros; induction H.
  constructor.
  destruct (null_dec x y H).
  exact (HistoryStep y H1 IHHistory).
  rewrite <- H1; assumption.
Qed.

Lemma NullStepsIrrelevant A (SA : Step A) (NonNullSA : Step A) (null_dec : ∀ x y : A, SA x y → NonNullSA x y ∨ x = y) (R : A → Prop) i : (∀ f, History NonNullSA i f → R f) → (∀ f, History SA i f → R f).
  intros; exact (H f (RemoveNullSteps NonNullSA null_dec H0)).
Qed.





Definition MemoryValue := nat.
Definition Address := nat.
Definition ThreadId := nat.

(* ThreadClaimed doesn't refer to explicit ownership, but to what's implied *must* be the ownership given that a thread did a nonatomic operation at the address and it wasn't known to be forbidden at the time. This doesn't account for shared read access yet (just because I don't need it yet).

After a thread does a nonatomic operation, other threads can't mess with it until the first thread does an SeqCst operation AND the second thread does a SeqCst operation. So, to know what threads would be allowed to start doing nonatomic operations, we have to remember *which* threads have done SeqCst operations since the original SeqCst. *)
Inductive AddressState := 
| ThreadClaimed : ThreadId → MemoryValue → AddressState
| Released : (ThreadId → Prop) → MemoryValue → AddressState
(* | Forbidden : AddressState *)
.

Definition ThreadCanNonAtomicAccess id state : Prop := match state with
| ThreadClaimed id2 _ => id = id2
| Released allowed _ => allowed id
(* | Forbidden => False *)
end.

Definition ThreadCanAtomicAccess id state : Prop := match state with
| ThreadClaimed id2 _ => id = id2
| Released allowed _ => True
(* | Forbidden => False *)
end.

Definition AddressValue state : MemoryValue := match state with
| ThreadClaimed _ value => value
| Released _ value => value
(* | Forbidden => 0 *)
end.

Definition AddressAfterSeqCst id value state : AddressState := match state with
| ThreadClaimed _ _ => Released (eq id) value
| Released allowed _ => Released (λ id2, allowed id2 ∨ id = id2) value
end.

Inductive PrimitiveOps : Type → Type :=
| NonAtomicRead : Address → PrimitiveOps nat
| NonAtomicWrite : Address → MemoryValue → PrimitiveOps unit
| CompareAndSwapSeqCst : Address → MemoryValue → MemoryValue → PrimitiveOps bool
| StoreSeqCst : Address → MemoryValue → PrimitiveOps unit
| Join : ThreadId → PrimitiveOps unit
| Spawn : ThreadControlFlow → PrimitiveOps ThreadId
with ThreadControlFlow := 
| Return : ∀ ReturnType : Type, ReturnType → ThreadControlFlow
| PrimitiveThen : ∀ po, PrimitiveOps po → (po → ThreadControlFlow) → ThreadControlFlow
| PrimitiveLoop : ∀ po, PrimitiveOps po → (po → option ThreadControlFlow) → ThreadControlFlow.

Definition Memory := (Address → AddressState).

Record ConcreteState := mkState
  { stateMemory : Memory
  ; stateThreads : list (ThreadId × ThreadControlFlow)
  }.
Locate eq_dec.
(* Definition NonThreadRelatedPrimitiveStep po (id : ThreadId) (oldMemory : Memory) (primitive : PrimitiveOps po) (newMemory : Memory) (newControlFlow : ThreadControlFlow) : Prop :=
match primitive with
| NonAtomicRead address => ThreadCanNonAtomicAccess id (memory address) ∧ ∃ continuation , newControlFlow = PrimitiveThen (NonAtomicRead address) continuation ∧ 
| NonAtomicWrite address value : Address → MemoryValue → PrimitiveOps unit
| CompareAndSwapSeqCst : Address → MemoryValue → MemoryValue → PrimitiveOps bool
| StoreSeqCst : Address → MemoryValue → PrimitiveOps unit
| _ : False
end

→ ThreadControlFlow → Memory →  ThreadControlFlow → Prop :=
| NonAtomicReadValid : ∀ memory address continuation, ThreadCanNonAtomicAccess id (memory address) → NonSpawnPrimitiveStep id memory (PrimitiveThen (NonAtomicRead address) continuation) (continuation (AddressValue (memory address)))
| NonAtomicReadInvalid : ∀ memory address continuation whatever, ¬ ThreadCanNonAtomicAccess id (memory address) → NonSpawnPrimitiveStep id memory (PrimitiveThen (NonAtomicRead address) continuation) whatever.
Inductive NonSpawnPrimitiveStep (id : ThreadId) : Memory → ThreadControlFlow → Memory →  ThreadControlFlow → Prop :=
| NonAtomicReadValid : ∀ memory address continuation, ThreadCanNonAtomicAccess id (memory address) → NonSpawnPrimitiveStep id memory (PrimitiveThen (NonAtomicRead address) continuation) (continuation (AddressValue (memory address)))
| NonAtomicReadInvalid : ∀ memory address continuation whatever, ¬ ThreadCanNonAtomicAccess id (memory address) → NonSpawnPrimitiveStep id memory (PrimitiveThen (NonAtomicRead address) continuation) whatever. *)

Require Import Arith.PeanoNat.
Import Nat.
Definition setAddress address memory newState : Memory :=
  (λ address2, if eq_dec address address2 then newState else memory address2).
  
Inductive Selection A : list A → Type :=
| selectHead : ∀ x l, Selection (x :: l)
| selectNext : ∀ x l, Selection l → Selection (x :: l).

Fixpoint selectedValue A (l : list A) (s : Selection l) : A := match s with
| selectHead x l => x
| selectNext x l sl => selectedValue sl
end.

Fixpoint replaceSelected A (l : list A) (s : Selection l) (new : A) : list A := match s with
| selectHead x l => new :: l
| selectNext x l sl => x :: replaceSelected sl new
end.

Definition PrimitiveThenStep (prev next : ConcreteState) (thread : Selection (stateThreads prev)) po (p : PrimitiveOps po) (cont : po → ThreadControlFlow) : Prop :=
  let memory := stateMemory prev in let (id , control) := selectedValue thread in
    match p in PrimitiveOps po return (po → ThreadControlFlow) → Prop with
      | NonAtomicRead address => λ cont, let value := AddressValue (memory address) in
        ¬ ThreadCanNonAtomicAccess id (memory address) ∨ next = mkState
          (setAddress address memory (ThreadClaimed id value))
          (replaceSelected thread (id, cont value))
      | NonAtomicWrite address value => λ cont, 
        ¬ ThreadCanNonAtomicAccess id (memory address) ∨ next = mkState
          (setAddress address memory (ThreadClaimed id value))
          (replaceSelected thread (id, cont tt))
      | StoreSeqCst address value => λ cont,
        ¬ ThreadCanAtomicAccess id (memory address) ∨ next = mkState
          (setAddress address memory (AddressAfterSeqCst id value (memory address)))
          (replaceSelected thread (id, cont tt))
      | CompareAndSwapSeqCst address old new => λ cont, let value := AddressValue (memory address) in
        ¬ ThreadCanAtomicAccess id (memory address) ∨ next = 
            if eq_dec old value then
              mkState
                (setAddress address memory (AddressAfterSeqCst id new (memory address)))
                (replaceSelected thread (id, cont true))
            else
              mkState memory (replaceSelected thread (id, cont false))
      | _ => λ cont, False
      end cont.

Definition ConcreteStep : Step ConcreteState :=
  λ prev next, prev = next ∨ let memory := stateMemory prev in ∃ thread : Selection (stateThreads prev), let (id , control) := selectedValue thread in match control with
    | Return _ _ => False
    | PrimitiveThen _ p cont => PrimitiveThenStep prev next thread p cont
    | PrimitiveLoop _ p cont => PrimitiveThenStep prev next thread p (λ output, match cont output with Some a => a | None => control end)
    end.





Definition increment (address : Address) : ThreadControlFlow :=
  PrimitiveThen (NonAtomicRead address) (λ n, PrimitiveThen (NonAtomicWrite address (S n)) (λ _ : unit, Return tt)).

Definition lock (address : Address) : ThreadControlFlow :=
  PrimitiveLoop (CompareAndSwapSeqCst address 0 1) (λ worked : bool, if worked then Some (Return tt) else None).

Definition unlock (address : Address) : ThreadControlFlow :=
  PrimitiveThen (StoreSeqCst address 0) (λ _ : unit, Return tt).

Fixpoint sequenceThreadControlFlow (f g : ThreadControlFlow) : ThreadControlFlow := match f with
| Return _ t => g
| PrimitiveThen _ p continuation => PrimitiveThen p (λ po, sequenceThreadControlFlow (continuation po) g)
| PrimitiveLoop _ p continuationPicker => PrimitiveLoop p (λ po, option_map (λ continuation, sequenceThreadControlFlow continuation g) (continuationPicker po))
end.
Notation "x ; y" := (sequenceThreadControlFlow x y) (at level 94, left associativity).

Definition incrementLockContents (address : Address) : ThreadControlFlow :=
  lock address ; increment (S address) ; unlock address.

Definition incrementTwiceConcurrentlyTestcase (address : Address) : ThreadControlFlow :=
  PrimitiveThen (NonAtomicWrite address 0) (λ _,
    PrimitiveThen (NonAtomicWrite (S address) 0) (λ _,
      PrimitiveThen (Spawn (incrementLockContents address)) (λ handle,
        incrementLockContents address ; PrimitiveThen (Join handle) (λ _, Return tt) 
  ))).

Lemma incrementBehavior (address : Address) (initial final : ConcreteState) (history : History ConcreteStep initial final) :
  stateThreads initial = (0 , increment address) :: nil →
  ThreadCanNonAtomicAccess 0 (stateMemory initial address) →
    final = initial ∨
    (stateThreads final = (0 , PrimitiveThen (NonAtomicWrite address (S (AddressValue (stateMemory initial address)))) (λ _ : unit, Return tt)) :: nil ∧ stateMemory final = 
      setAddress address (stateMemory initial) (ThreadClaimed 0 (AddressValue (stateMemory initial address)))
    ) ∨
    (stateThreads final = (0 , Return tt) :: nil ∧ stateMemory final =
      setAddress address (setAddress address (stateMemory initial) (ThreadClaimed 0 (AddressValue (stateMemory initial address)))) (ThreadClaimed 0 (S (AddressValue (stateMemory initial address))))
    ).
    
  intuition idtac.
  dependent induction history.
  left; reflexivity.
  
  destruct initial; destruct x; destruct y; simpl in *.
  rewrite H0 in *; clear H0 stateThreads0.
  intuition idtac; simpl in *.
  
  inversion H0; rewrite H3 in *; rewrite H4 in *.
  destruct H.
  left; symmetry; assumption.
  right; left. destruct H. simpl in *. dependent destruction x; simpl in *. unfold PrimitiveThenStep in H; simpl in H.
  destruct H. contradiction.
  congruence.
  
  
  admit. admit.
  
  
  destruct H. intuition idtac. simpl in *. inversion H. specialize (H3 address2). rewrite (H3 H2). rewrite H4. reflexivity.
  
  destruct H. intuition idtac. simpl in *. inversion x. revert dependent x; intro; destruct x. 
  
  
  dependent induction history.

Lemma incrementNoSideEffects (address : Address) (initial final : ConcreteState) (history : History ConcreteStep initial final) : stateThreads initial = (0 , increment address) :: nil → ThreadCanNonAtomicAccess 0 (stateMemory initial address) → ∀ address2, address ≠ address2 → stateMemory initial address2 = stateMemory final address2.
  intuition idtac.
  dependent induction history.
  reflexivity.
  
  destruct initial; destruct x; destruct y; simpl in *.
  rewrite H0 in *; clear H0 stateThreads0.
  
  destruct H. intuition idtac. simpl in *. inversion H. specialize (H3 address2). rewrite (H3 H2). rewrite H4. reflexivity.
  
  destruct H. intuition idtac. simpl in *. inversion x. revert dependent x; intro; destruct x. 
  
  
  dependent induction history.


Lemma incrementIncrements (address : Address) (initial final : ConcreteState) (history : History initial final) : stateThreads initial = (0 , increment address) :: nil → ThreadCanNonAtomicAccess 0 (stateMemory initial address) → 

