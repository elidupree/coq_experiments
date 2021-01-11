(* Some attempts to build an effect system for my code generation *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.

Inductive Effectful Primitive (primitiveType : Primitive → Type) returnType : Type :=
| Return : returnType → Effectful primitiveType returnType
| PrimitiveThen : ∀ p, ((primitiveType p) → Effectful primitiveType returnType) → Effectful primitiveType returnType.

Fixpoint Bind T U Primitive (primitiveType : Primitive → Type)
  (operation : Effectful primitiveType T) 
  (continuation : (T → Effectful primitiveType U))
  : Effectful primitiveType U := match operation with
| Return t => continuation t
| PrimitiveThen p cont1 => PrimitiveThen p (λ pOutput, (Bind (cont1 pOutput) continuation))
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

I'm going to go with the second way, because it seems like it will be the most convenient: programmers think in terms of state, and we frequently want to prove that a procedure leaves the world in a particular state, which is more intuitive than proving that its effect-history conforms to the more complex conditions that would leave it in that state.

*)

Definition StateTransitions Primitive (primitiveType : Primitive → Type) State : Type := State → ∀ p, (primitiveType p) → option State.
Definition StateTransitionsInhabited Primitive (primitiveType : Primitive → Type) State (transitions : StateTransitions primitiveType State) : Type := ∀ state p, ∃ (output : primitiveType p) next, transitions state p output = Some next.

Definition MemoryOpsStateTransitions T (eq_dec : ∀ t u : T, {t = u} + {t ≠ u}) : StateTransitions (@MemoryOpsType T) T :=
  λ state p, match p with
  | Read => λ output, if eq_dec output state then Some state else None
  | Write t => λ _, Some t
  end.
  
Lemma MemoryOpsStateTransitionsInhabited T (eq_dec : ∀ t u : T, {t = u} + {t ≠ u}) : StateTransitionsInhabited (MemoryOpsStateTransitions eq_dec).
  unfold StateTransitionsInhabited.
  intuition idtac.
  destruct p.
  exists state; exists state.
  simpl.
  destruct eq_dec; trivial.
  contradict f; reflexivity.
  exists tt; exists t; reflexivity.
Qed.
  

Inductive PossibleOutcome Primitive (primitiveType : Primitive → Type) : ∀ R, Effectful primitiveType R → list {p : Primitive & primitiveType p} → R → Type :=
| ReturnOutcome : ∀ T (t: T), PossibleOutcome (Return primitiveType t) nil t
| PrimitiveOutcome : ∀ p po, PossibleOutcome (Primitive primitiveType p) (existT _ p po :: nil) po
| BindOutcome : ∀ T U
  (operation : Effectful primitiveType T)
  (continuation : (T → Effectful primitiveType U))
  opList contList (opRet : T) (contRet : U),
    PossibleOutcome operation opList opRet →
    PossibleOutcome (continuation opRet) contList contRet →
    PossibleOutcome (Bind operation continuation) (opList ++ contList) contRet.


Theorem writeSThenRead_readsS : ∀ n, writeSThenRead n

Definition unwrap_or T (default : T) (o : option T) : T := match o with
| None => default
| Some t => t
end.

Definition lastWrite T U (e : Effectful (@MemoryOpsType T) U) (startingValue : U) : option T := match e with
| Return _ _ => None
| Primitive p => match p with
  | Read => None
  | Write t => Some t
  end
| Bind _ _ a b => unwrap_or ()
end.

Definition readWriteReduce T U (e : Effectful (@MemoryOpsType T) U) (startingValue : option T) : Effectful (@MemoryOpsType T) U := match e with
| Return _ _ => e
| Primitive p => match p with
  | Read => Return (@MemoryOpsType T) startingValue
  | Write _ => e
  end
| Bind _ _ a b => match readWriteReduce a startingValue with
  | Return _ t => e
  | Primitive _ => e
  | Bind _ _ a b => e
  end
end.


Parameter read : ∀ T, Address T → Effectful T,
Parameter write : ∀ T, Address T → T → Effectful RustUnitType,
  coherence : ∀ T (t : T) (addr : Address T) → Bind (write addr t) (λ _, read addr) 
  
