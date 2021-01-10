Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.

Inductive Effectful primitives (primitiveType : primitives → Type) : Type → Type :=
| Primitive : ∀ p, Effectful primitiveType (primitiveType p)
| Return : ∀ T (t: T), Effectful primitiveType T
| Bind : ∀ T U, Effectful primitiveType T → (T → Effectful primitiveType U) → Effectful primitiveType U.

Inductive MemoryOps T : Type :=
| Read : MemoryOps T
| Write : T → MemoryOps T.

Definition MemoryOpsType T (op : MemoryOps T) : Type := match op with
| Read => T
| Write _ => unit
end.

(* At this point, we want to make some sort of guarantee like, "if there is a write and then a read, the value of the read is guaranteed to be equal to the argument of the most recent write".

We COULD express this as a timeless condition on the possible outcome histories – i.e. define the possible outcomes as the type "list of primitives and their outputs" and write down a predicate that excludes some of them as impossible. But this is more powerful than necessary: it allows predicates where the choice of which primitive to invoke makes the outcome impossible. Really we should be assuming that given any prefix of the outcome history, the program COULD invoke any primitive as the next operation – and it's only the outputs that make the outcome impossible. Some choices can lead to UB, but that's actually the *opposite* extreme from this type of impossibility. A primitive invocation's type is always inhabited, even if the only inhabitant is "UB".

The simple fix would be to express it as a predicate on the prefixes of outcome history, with an explicit restriction preventing it from removing all inhabitants. Then an outcome history is possible iff all of its prefixes satisfy the predicate. (And if it matters, the predicate is allowed to assume that all sub-prefixes already meet the predicate.) *)

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
  
