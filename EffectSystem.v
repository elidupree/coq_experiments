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
  
