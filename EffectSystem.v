(* Some attempts to build an effect system for my code generation *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Notation "x × y" := (prod x y) (at level 60, right associativity) : type_scope.
Require Import List.

Inductive Effectful Primitive (primitiveType : Primitive → Type) returnType : Type :=
| Return : returnType → Effectful primitiveType returnType
| PrimitiveThen : ∀ p, ((primitiveType p) → Effectful primitiveType returnType) → Effectful primitiveType returnType.

Fixpoint bind T U Primitive (primitiveType : Primitive → Type)
  (operation : Effectful primitiveType T) 
  (continuation : (T → Effectful primitiveType U))
  : Effectful primitiveType U := match operation with
| Return t => continuation t
| PrimitiveThen p cont1 => PrimitiveThen p (λ pOutput, (bind (cont1 pOutput) continuation))
end.

(* A very simple effect, for prototyping purposes: A single cell of memory *)
Inductive MemoryOps T : Type :=
| Read : MemoryOps T
| Write : T → MemoryOps T.

Definition MemoryOpsType T (op : MemoryOps T) : Type := match op with
| Read => T
| Write _ => unit
end.

Definition writeSThenRead (n : nat) : Effectful (@MemoryOpsType nat) nat :=
  PrimitiveThen (Write (S n)) (λ _, PrimitiveThen (Read nat) (λ r, Return _ r)).

(*

At this point, we want to make some sort of guarantee like, "if there is a write and then a read, the value of the read is guaranteed to be equal to the argument of the most recent write".

We COULD express this as a timeless condition on the possible outcome histories – i.e. define the possible outcomes as the type "list of Primitive and their outputs" and write down a predicate that excludes some of them as impossible. But this is more powerful than necessary: it allows predicates where the choice of which primitive to invoke makes the outcome impossible. Really we should be assuming that given any prefix of the outcome history, the program COULD invoke any primitive as the next operation – and it's only the outputs that make the outcome impossible. Some choices can lead to UB, but that's actually the *opposite* extreme from this type of impossibility. A primitive invocation's type is always inhabited, even if the only inhabitant is "UB".

The simple fix would be to express it as a predicate on the prefixes of outcome history, with an explicit restriction preventing it from removing all inhabitants. Then an outcome history is possible iff all of its prefixes satisfy the predicate. (And if it matters, the predicate is allowed to assume that all sub-prefixes already meet the predicate.)

Another thing we could do is create a structure describing the *state* of the effect, and a function from (state, primitive, primitive output) to (option state). (With the requirement that at least one possible output yields Some.) This is isomorphic to the above (if it's defined by state and you have a history, you can infer the state; and if it's defined by history, you can make a state that contains the whole history). It also more clearly expresses the way effect state would typically have bounded size.

A third way would be to allow multiple possible state transitions that produce the same value. This would mean you can't infer the state from the history. This is still isomorphic to the others (this model can clearly represent the other two; and the other two can make an explicit representation of the superposition of possible states if needed).

A fourth way would be to require the effects to be deterministic, so that the state transition function is (state, primitive) to (state, primitive output). This is simpler to work with for deterministic effects. For nondeterministic effects, what you have to do is encode all possible behaviors in the state (for example, the state of a random number generator could be a nat index and a (nat -> random number) function defining what it will yield), and proofs are done by having a proof for all possible starting states, rather than a proof for all possible outputs at each primitive. This approach is, again, isomorphic to the others. This approach is ALMOST isomorphic to the others, but not quite: it's actually more powerful, because the others require decidable equality to replicate this, while on the other hand, this approach can replicate all the others by having the state include a nat->choice function (like the RNG example). However, for synchronization primitives, expressing it as a choice function feels pretty nonintuitive. The other upside of this approach is that you can implement "run to completion, given this starting state" as an actual function rather than just making "legal complete run" a predicate on operation histories.

I'm going to go with the last way, because it seems like it will be the most convenient: programmers think in terms of state, and we frequently want to prove that a procedure leaves the world in a particular state, which is more intuitive than proving that its effect-history conforms to the more complex conditions that would leave it in that state.

*)

Definition StateTransitions Primitive (primitiveType : Primitive → Type) State : Type := State → ∀ p, State × (primitiveType p).

Definition MemoryOpsStateTransitions T : StateTransitions (@MemoryOpsType T) T :=
  λ state p, match p with
  | Read => (state , state)
  | Write t => (t , tt)
  end.
  
Definition run Primitive returnType State
  (primitiveType : Primitive → Type)
  (transitions : StateTransitions primitiveType State) : 
  Effectful primitiveType returnType → State → State × returnType :=
  fix run operation := match operation with
    | Return t => λ state, (state , t)
    | PrimitiveThen p continuation => λ state, match transitions state p with
      | (nextState , output) => run (continuation output) nextState
      end
    end.

Theorem writeSThenRead_readsS : ∀ n startingState, fst (run (@MemoryOpsStateTransitions nat) (writeSThenRead n) startingState) = S n.
  reflexivity.
Qed.

Lemma runThen : ∀ Primitive T State
  (primitiveType : Primitive → Type)
  (transitions : StateTransitions primitiveType State)
  (p : Primitive)
  (continuation : (primitiveType p) → Effectful primitiveType T)
  (state : State),
  run transitions (PrimitiveThen p continuation) state =
  match transitions state p with
    (nextState , output) => run transitions (continuation output) nextState
  end.
  reflexivity.
Qed.
 

Theorem runBind_bindRun : ∀ Primitive T U State
  (primitiveType : Primitive → Type)
  (transitions : StateTransitions primitiveType State)
  (operation : Effectful primitiveType T)
  (continuation : T → Effectful primitiveType U)
  (state : State),
  run transitions (bind operation continuation) state = match run transitions operation state with
    (nextState , t) => run transitions (continuation t) nextState
  end.
  
  (* Apologies for this proof being a bit of a mess *)
  intros Primitive T U State primitiveType transitions.
  refine(fix proof operation := match operation with
  | Return t => _
  | PrimitiveThen p cont1 => _
  end).
  reflexivity.
  intros.
  rewrite runThen.
  pose (transitions state p) as afterFirst.
  specialize (proof (cont1 (snd afterFirst)) continuation (fst afterFirst)).
  unfold bind.
  simpl.
  fold bind.
  destruct (transitions state p).
  exact proof.
Qed.
  
(*

But the next bit might not quite work with this model. Let's consider.

If we were designing an effect system for a safe language, we might want a typical function to take multiple effects – for example, a different effect for each &mut in its arguments. To do that, maybe the next thing to do would be to make a system of product types on the types of Primitives and StateTransitions, so that you could pass subsets of your effects into callees.

But that's not what we're doing. This is the effect system for a model of an *unsafe* language – so the assumption is that there's a universal collection of primitive effects, and any code might attempt to use any effect, even if it's not allowed.

In that system, functions want to consume *guarantees* about which effects their allowed to do and what their outcomes would be. The state transitions are just a way of expressing a particular guarantee.

So maybe, instead of passing collections of *effects*, we pass collections of *permissions*, which are predicates on the primitives. Except, of course, what you have permission to do can also be a function of the state, so the full form of permissions is simply "state, but the outcome of some primitives is defined as UB". If you want to benefit from the guarantees of a callee, the guarantees need to be based on the assumption of a *supertype* of your guarantees. Here, a supertype is a modified state machine where all of the original possible outcomes are still possible, but there may be some additional outcomes that are also possible (which means any outcome can be changed to "always UB", because UB is something like "anything is possible").

This clearly seems to favor the "predicate on outcomes" approaches. Just in case, though, is it possible to do this through the "deterministic state transitions" approach? With the deterministic approach, we express guarantees through the "for all possible starting states…" instead of "for all possible outcomes at each step". So, if we want to say that for a particular (a b : StateTransitions, supertype a b), we wouldn't be able to compare states at all because the state types are different, and the determinism means that a particular state from one type is either identical or distinct. So `supertype a b` would be to say, for all possible states in `b`, there's a state in `a` that gives the same behavior for all possible sequences of primitives. As an example, if `b` describes memory with 2 locations that obey write-read consistency, and `a` describes the same memory but only the first location behaves consistently, then `a` includes a way to specify ANY behavior on the second location, so in particular, you COULD select a behavior that is consistent.

The guarantee we want to relay from callee to caller is initially expressed as a proposition about the callee's state (here, the `a` state), but it needs to be transformable into a proposition about the caller's state (here, the `b` state). Thus, one way or another, we need a mapping between the states, not just a guarantee that SOME state exists that has the same behavior. In particular, I think we need the following guarantee: for a given starting state b0, predicates B1 and A1, and Effectful e, we can produce at least one mapped-starting-state a0 that behaves identically to b0, where if e under a-transitions took state a0 to a state matching predicate A1, then e under b-transitions would take b0 to a state matching predicate B1. (And in this model, "UB" is just shorthand for "you can produce a state that fills in any possible sequence of outcomes after this" - so if there's an a0 that matches b0 until it hits UB, then there's an a0 that matches b0 indefinitely, but on the flip side, if you reached UB, the callee wouldn't be able to prove anything about what state it ends up in.)

Wait, let's approach this from a different angle. I intend for this system to support mutexes. So, let us consider the following situation:
– function Main constructs a Mutex in owned memory, then spawns 2 threads running function Locker.
– function Locker locks the Mutex, calls Operation on the contained data, then unlocks it.
– function Operation operates on the contained data as owned data; it must not be aware that the data is inside a Mutex.

Let us first consider the call from Locker to Operation. Locker initially receives a memory effect that is guaranteed to be in an "unlocked Mutex" state. In this state,
– accessing the interior in any way yields UB
– performing the lock sequence may yield a confirmation which only happens if the effect is now in a "locked Mutex" state.
Having received the confirmation, the memory effect is guaranteed to be in a "locked Mutex" state.
– accessing the interior behaves as owned data, UNLESS
– if you perform the unlock sequence, it switches back to an "unlocked Mutex" state.

Naturally, a "locked Mutex" state is distinct from an "owned data" state, because of the possibility of unlocking it. But we can characterize it as a subtype of "owned data" – if we relax the guarantees by making the unlock sequence be UB, then it is now indistinguishable from owned data. So this state mapping allows Locker to call Operation.

Now, let's consider the calls from Main to Locker. Main STARTS with owned memory and must convert it in the other direction, making it into an unlocked Mutex. Again, this must be done by *relaxing* guarantees. Here, Main begins by doing some atomic setup operations (which are permitted in owned data), then declares that interacting with the data in a non-Mutex way is now UB. This is straightforward so far – the real question is what guarantees you need in order to spawn multiple threads.

I suppose what we need is for the caller's effects to simultaneously simulate the state of both effects passed to the callees. Let's first consider it in the simpler case where all operations are in a total order. So if the caller is proven to be in some range M of possible states, and we want to call two threads that demand states in T0 and T1, then for every m : M, we must find t0 : T0 and t1 : T1 such that for any sequences of primitives e0 and e1, any *interleaving* of e0 and e1 will witness t0 and m giving the same outputs for the e0 primitives, and t1 and m giving the same outputs for the e1 primitives.

As the simplest example: you pass disjoint memory regions into two threads as owned data; for each thread, accessing the other thread's memory is UB... oh, here we need to get a bit stricter. As written, UB in one thread isn't automatically UB in the other, so if e0 messes with e1's memory but e1 is legit, we cannot produce a t1 that matches m. So we need to give UB a special status: the above should say "for any sequences of primitives e0 and e1 *that do not produce UB in t0 and t1*" - or actually, - "for any *Effectfuls* e0 and e1 that can never produce UB from states in T0 and T1" (because we bind e0 and e1 before the interleaving, and whether a sequence hits UB could depend on the choice of interleaving). With that guarantee, we can prove that each thread doesn't access the other thread's data, so the conversion is straightforward.

Let's proceed to the Mutex example. Now our e0 and e1 may lock the mutex, which I suppose must be represented in T0/T1 as try-lock loops, since our current definitions don't guarantee that the thread won't wake up before the lock is available. So, thinking about how to produce t0 and t1: The states in T0 and T1 must include the information about what data you will find inside the Mutex after each time you successfully lock it. If we fix the data first, then choose an interleaving afterwards, the interleaving could change what data e0 could witness. That's no good! We need to change the order of the rule:

"If the caller is proven to be in some range M of possible states, and we want to call two threads whose behaviors are Effectfuls e0 and e1 that demand states in T0 and T1 and never produce UB, then for any m : M and any interleaving of e0 and e1, we must find t0 : T0 and t1 : T1 such that t0 and m give the same outputs for the e0 primitives, and t1 and m give the same outputs for the e1 primitives."

Now, the interleaving is predetermined before we choose t0 and t1. From the perspective of the caller, we can simply check what order the successful locks happen, and construct t0 and t1 to feed in the same information as m would. (Note that the "No UB" guarantee is once again necessary for this construction.)

So, the states can be *constructed*. Now, how do we *retrieve* the guarantees provided by the callee? First, let's consider the simple case with disjoint owned data. Here, the callees can guarantee that they leave the data in a certain state, which is to say that they provide a proof about the ending state of running e0 with T0-transitions on t0. First, I think my retrieveability proof concept above was too general: what I would like to do is require a caller-callee state mapping f that respects all primitive operations, i.e. for all s p, callee_transitions(f(s), p) = f(caller_transitions(s, p)). Thus, if we have a proof about the result state of a callee, it's an unbroken chain of primitive transitions, so we can apply the "respects" rule repeatedly to receive a proof about the result state in the caller. But how does this apply to interleaved callees? Here the chain is broken: as soon as e0 does one operation and e1 does another, the above doesn't provide any implication from the resulting state after the e0 operation to the resulting state in the caller. Intuitively, we also need the guarantee that e1 operations "don't change the e0 part of the caller state"... but with the current definitions, the e0 states ARE dependent on the interleaving (because they encode what WOULD happen in the case of UB). We could special-case UB again, but I don't know if that's the right approach. Later, we are going to have legitimate cases where one state affects the other – let's jump forward to considering one of those.

To consider the Mutex case, let's start with the modest guarantee that the Mutex an integer, which begins at 0, and Operation increments the integer exactly once. Thus, we should be able to prove that at the end of Main, the integer is now 2. If we want to express this as a condition on *result states* of the Lockers, then we have a complication. In the naive approach, the state used by Locker would only contain the information Locker could observe – so as soon as it unlocks the Mutex, the state contains no knowledge of what was left there, because it could be arbitrarily changed before the next time it was unlocked. So the state must contain additional information about the history of what operations it did.

At this point, it feels burdensome to that I will have to define a state type to use to express conditions about the history. I will now make another attempt to do the definitions in terms of conditions on primitive-histories.

The intuitive purpose of the "deterministic state" approach was to be able to say "for all things that could happen…". Let's define "thing that could happen" directly, as a predicate on histories:

*)

Definition History Primitive (primitiveType : Primitive → Type) := list {p & primitiveType p}.
Definition HistoryPredicate Primitive (primitiveType : Primitive → Type) := (History primitiveType) → Prop.

Definition unpackSigT A (P : A → Type) R (s : sigT P) (f : ∀ a b, R) : R :=
  match s with existT a b => f a b end.

Definition memoryOpsHistoryPredicateWithState T : T → HistoryPredicate (@MemoryOpsType T) :=
  fix P state history := match history with
  | nil => True
  | x :: xs => unpackSigT x (λ a, match a return MemoryOpsType a → Prop with
    | Read => λ p, p = state ∧ P state xs
    | Write t => λ _, P t xs
  end) end.
Definition memoryOpsHistoryPredicateUnknownState T : HistoryPredicate (@MemoryOpsType T) :=
  λ history, match history with
  | nil => True
  | x :: xs => unpackSigT x (λ a, match a return MemoryOpsType a → Prop with
    | Read => λ p, memoryOpsHistoryPredicateWithState p xs
    | Write t => λ _, memoryOpsHistoryPredicateWithState t xs
  end) end.
  
Import EqNotations.
  
(* Definition BehaviorDefinitionsIsomorphic Primitive returnType State
  (primitiveType : Primitive → Type)
  (transitions : StateTransitions primitiveType State)
  (predicate : HistoryPredicate primitiveType) :  *)
  
  
(*
Whoops... this definition applies the predicate to all suffixes of the history,
when it should actually be applied to all prefixes.
I'm going to put off fixing this for now.
*)
Definition Run Primitive returnType
  (primitiveType : Primitive → Type)
  (predicate : HistoryPredicate primitiveType): 
  Effectful primitiveType returnType → History primitiveType → returnType → Prop :=
  fix Run operation history returnValue := predicate history ∧ match operation with
    | Return t => history = nil ∧ returnValue = t
    | PrimitiveThen p continuation => match history with
      | nil => False
      | x :: xs => unpackSigT x (λ p' output, ∃ (eq : p' = p), Run (continuation (rew eq in output)) xs returnValue)
      end
    end.

Theorem writeSThenRead_readsS' : ∀ n history returnValue, (Run (@memoryOpsHistoryPredicateUnknownState nat) (writeSThenRead n) history returnValue) → returnValue = S n.
  (* Unfortunately, now, the proof is more verbose than the `reflexivity` proof in the first approach.
  But it's straightforward; the only mess here is unpacking all the dependent types.
  Domain-specific tactics and lemmas could help with this. *)
  intros n history returnValue run.
  simpl in run; destruct run as [wholeHistoryValid run'].
  destruct history as [|hist0 historyTail].
  contradiction.
  destruct hist0 as [p0 po0]; destruct historyTail as [|hist1 historyTail].
  exfalso; exact (proj2 (ex_proj2 run')).
  destruct hist1 as [p1 po1]; destruct historyTail as [|hist2 historyTail]; unfold unpackSigT in run'; destruct run' as [p0isWriteSn x]; destruct x as [_ x]; destruct x as [p1isRead x]; destruct x as [_ x]; destruct x as [finalHistoryIsNil returnCorrect].
  2: discriminate.
  revert dependent po0; rewrite p0isWriteSn.
  revert dependent po1; rewrite p1isRead.
  simpl in *.
  intuition idtac.
  congruence.
Qed.


(*

Trying to apply the above definitions to the proposed Mutex case runs into several problems.

The Run type is now powerful enough to handle nondeterministic effects, but *Effectful* itself is lacking. It's not trivial to express a function that spawns threads as an Effectful, because Effectfuls are deterministic, and the interleaving is not. Perhaps we could make a nondeterminism effect for deciding which thread to advance next, but I'm not confident that that's a good approach. Perhaps Effectful itself should be allowed to be nondeterministic. But before resolving that problem, let's also consider the second problem:

*Locker* can't be expressed as an Effectful either, because it has an unbounded try-lock loop, and Effectful doesn't account for non-termination.

To account for nontermination, we want to express Effectful as a step function, where, after receiving the output of a primitive, it may return any Effectful, including itself. But of course, a function can't return itself. So instead, we need to have a second type to represent the control flow state, and then have a function from control flow state to either a Return or a PrimitiveThen (but this time PrimitiveThen wraps a function that returns another *state*, rather than returning Effectful).

But should these be allowed to be nondeterministic? Or must they require a nondeterminism effect to perform the interleaving?

Since this isn't obvious even by itself, let's glance forward to the consideration of how to represent general multithreading, not just interleaving. In that case, there's no longer a "what happens next" – but that's tolerable if we merely generalize our "history" type so that instead of being a list, it's an arbitrary collection with a happens-before relation. Predicates can still be defined on such histories. But where does that leave Effectful? I suppose that that means each step of an Effectful can specify one *or more* "next" operations that must exist. Wait, there's a problem: if you specify that two identical next operations must exist, what's to stop the same operation from fulfilling both requirements? One could arbitrarily construct distinct control flow states for them, but that seems fragile. And on the other hand, they have to merge eventually (when you join both threads).

It also feels potentially misguided to not have an explicit representation of threads. After all, to join a thread, you are claiming your next primitive will happen-after the return of that thread, but this claim isn't necessarily aware of the specific return operation in question; it follows that to express the claim, you must be able to refer to a thread. So, then, is "spawning a thread" a primitive that takes an Effectful and returns a join handle? And a History is a list of thread histories, which are lists, and the HistoryPredicate required by Main requires that every Spawn primitive returns a distinct ID, and whenever a Spawn primitive exists, there is a thread with the same ID, and a valid Run of that thread. And Join takes an ID and must happen-after every primitive in that thread.



*)


(*

Oops... we had a circular reference issue in these definitions...:

*)

(*
Inductive ControlFlowChoice Primitive (primitiveType : Primitive → Type) ReturnType State :=
| ControlFlowReturn : ReturnType → ControlFlowChoice primitiveType ReturnType State
| ControlFlowPrimitive : ∀ p, (primitiveType p → State) → ControlFlowChoice primitiveType ReturnType State.
Definition ControlFlow Primitive (primitiveType : Primitive → Type) ReturnType State : Type := State → ControlFlowChoice primitiveType ReturnType State.

(* Note that this is strictly more powerful than Effectful, as we can illustrate with a conversion: *)
Definition EffectfulToControlFlow Primitive (primitiveType : Primitive → Type) ReturnType
  : ControlFlow primitiveType ReturnType (Effectful primitiveType ReturnType) := 
  λ operation, match operation with
  | Return t => ControlFlowReturn _ _ t
  | PrimitiveThen p continuation => ControlFlowPrimitive _ _ p continuation
  end.

(* This time, let's have multiple memory locations, indexed by `nat`.*)
Inductive ThreadedOps : Type :=
| NonAtomicRead : nat → ThreadedOps
| NonAtomicWrite : nat → nat → ThreadedOps
| Spawn : ∀ ControlFlowState controlFlowState, ControlFlow ThreadedOpsType unit ControlFlowState → ThreadedOps
| Join : nat → ThreadedOps.
Definition ThreadedOpsType (op : ThreadedOps) : Type := match op with
| NonAtomicRead _ => nat
| _ => unit
end.

Definition incrementEffectful (address : nat) : Effectful ThreadedOpsType unit :=
  PrimitiveThen (Write (S n)) (λ _, PrimitiveThen (Read nat) (λ r, Return _ r)).

Definition increment (address : nat) := EffectfulToControlFlow (incrementEffectful address).

*)

(*

To avoid the circular reference, this time, let's require that the same ControlFlowState type will be used across all threads. That way, we can postpone defining the ControlFlow for it: One ControlFlow defines the behavior of all ControlFlowStates.

It follows that the ControlFlowState type must account for multiple return types, and if we need to know that a function returns a specific type, we give that as a proof. Or we could require a `Type → Type` instead of just a `Type` for the ControlFlowState... the latter has the arguable advantage that it inherently forbids functions that don't always return the same type; the former has the arguable advantage that if a function never terminates, you can present the "F returns T" proof for multiple return types. I'm going to go with the former and see if I run into any problems.

The Primitive type can't even take the ControlFlowState as a parameter because ControlFlow types also have to take the Primitive type as a parameter, so you'd still have circular reference problems. Instead, we just let you pass any type as the thread function, and say it's UB if you pass the wrong type.

While I'm refactoring things, I think it makes more sense if I make Primitive an indexed type instead of having a separate function to say what type it is.

*)

Inductive ControlFlowChoice :=
| ControlFlowReturn : ∀ ReturnType : Type, ReturnType → ControlFlowChoice
| ControlFlowPrimitive : ∀ p po State, p → (po → State) → ControlFlowChoice.
Definition ControlFlow State : Type := State → ControlFlowChoice.

(* This time, let's have multiple memory locations, indexed by `nat`.*)
Inductive NonSpawnOps : Type → Type :=
| NonAtomicRead : nat → NonSpawnOps nat
| NonAtomicWrite : nat → nat → NonSpawnOps unit
| CompareAndSwapSeqCst : nat → nat → nat → NonSpawnOps bool
| StoreSeqCst : nat → nat → NonSpawnOps unit
| Join : nat → NonSpawnOps unit.
Definition ThreadId := nat.
Inductive ThreadedOps : Type → Type :=
| NonSpawn : ∀ t, NonSpawnOps t → ThreadedOps t
| Spawn : ∀ ControlFlowState, ControlFlowState → ThreadedOps ThreadId.

Inductive Loopable :=
| LoopableReturn : ∀ ReturnType : Type, ReturnType → Loopable
| LoopableNonSpawn : ∀ po, NonSpawnOps po → (po → Loopable) → Loopable
| LoopableLoop : ∀ po, NonSpawnOps po → (po → option Loopable) → Loopable
| LoopableSpawn : Loopable → (ThreadId → Loopable) → Loopable.

Definition LoopableControlFlow : ControlFlow Loopable := 
  λ operation, match operation with
  | LoopableReturn _ t => ControlFlowReturn t
  | LoopableNonSpawn _ p continuation => ControlFlowPrimitive (NonSpawn p) continuation
  | LoopableLoop _ p continuationPicker => ControlFlowPrimitive (NonSpawn p) (λ output, match continuationPicker output with
    | Some c => c
    | None => operation
    end)
  | LoopableSpawn spawned continuation => ControlFlowPrimitive (Spawn spawned) continuation
  end.

Definition increment (address : nat) : Loopable :=
  LoopableNonSpawn (NonAtomicRead address) (λ n, LoopableNonSpawn (NonAtomicWrite address (S n)) (λ _ : unit, LoopableReturn tt)).

Definition lock (address : nat) : Loopable :=
  LoopableLoop (CompareAndSwapSeqCst address 0 1) (λ worked : bool, if worked then Some (LoopableReturn tt) else None).

Definition unlock (address : nat) : Loopable :=
  LoopableNonSpawn (StoreSeqCst address 0) (λ _ : unit, LoopableReturn tt).

Fixpoint sequenceLoopable (f g : Loopable) : Loopable := match f with
| LoopableReturn _ t => g
| LoopableNonSpawn _ p continuation => LoopableNonSpawn p (λ po, sequenceLoopable (continuation po) g)
| LoopableLoop _ p continuationPicker => LoopableLoop p (λ po, option_map (λ continuation, sequenceLoopable continuation g) (continuationPicker po))
| LoopableSpawn spawned continuation => LoopableSpawn spawned (λ po, sequenceLoopable (continuation po) g)
end.
Notation "x ; y" := (sequenceLoopable x y) (at level 94, left associativity).

Definition incrementLockContents (address : nat) : Loopable :=
  lock address ; increment (S address) ; unlock address.

Definition incrementTwiceConcurrentlyTestcase (address : nat) : Loopable :=
  LoopableNonSpawn (NonAtomicWrite address 0) (λ _,
    LoopableNonSpawn (NonAtomicWrite (S address) 0) (λ _,
      LoopableSpawn (incrementLockContents address) (λ handle,
        incrementLockContents address ; LoopableNonSpawn (Join handle) (λ _, LoopableReturn tt) 
  ))).
