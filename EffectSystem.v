(* Some attempts to build an effect system for my code generation *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Notation "x × y" := (prod x y) (at level 60, right associativity) : type_scope.

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

"If the caller is proven to be in some range M of possible states, and we want to call two threads whose behaviors are Effectfuls e0 and e1 that demand states in T0 and T1, then for any m : M and any interleaving of e0 and e1, we must find t0 : T0 and t1 : T1 such that t0 and m give the same outputs for the e0 primitives, and t1 and m give the same outputs for the e1 primitives."

Now, the interleaving is predetermined before we choose t0 and t1. From the perspective of the caller, we can simply check what order the successful locks happen, and construct t0 and t1 to feed in the same information as m would.

So, the states can be *constructed*. Now, how do we *retrieve* the guarantees provided by the callee? As an example, let's start with the modest guarantee that the Mutex an integer, which begins at 0, and Operation increments the integer exactly once. Thus, we should be able to prove that at the end of Main, the integer is now 2.

*)


