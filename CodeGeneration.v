(* A bunch of disorganized notes about models for Rust code *)


Search "Total".


Inductive Memory

Inductive RustType : Set :=

Inductive Fn : Set :=
| 

Inductive Arguments : (argumentTypes : list RustType) → Set
| NoArguments : Arguments Nil
| ArgumentsCons : ∀ x xs, Value x → Arguments xs → Arguments (x :: xs)

Definition StorageLocation := String.

Inductive Statement : Set :=
| Call : ∀ (argumentTypes : list RustType) (resultType : RustType), Fn argumentTypes resultType → Arguments argumentTypes → StorageLocation → RustExpr
| 

Definition step : ExecutionState → ExecutionState
Definition steps : nat -> ExecutionState → ExecutionState

Memory := ∀ address 


opsFromHere : list MemoryOperation

∃ (opHappens : Operation → Prop), ∃ (happensBefore : Operation → Operation → Prop), PartialOrder happensBefore

Memory := MemoryOperation → Prop
OpWroteVisibleValue := ∀ (memory : Memory) (value : Value) (operation : MemoryOperation), memory operation ∧ OpWroteValue operation value ∧ HappensBefore operation ????)

AddressHoldsValue := ∀ (address : Address) (memory : Memory) (value : Value), (∃ (operation : MemoryOperation), OpWroteVisibleValue memory value operation) ∧ ∀ (operation : MemoryOperation), memory operation → OpWroteValue address operation ?? → ∃ (laterOperation : MemoryOperation), OpWroteVisibleValue memory value laterOperation


Definition valid : Type := ∀ (code : Code) (inputs : StartingInputs code) 


Definition stateReachable code : Type := ∀ (code : Code) (ExecutionState code), Prop 
Definition valid code : Type :=
  ∀ (state : ExecutionState code), stateReachable state → stateReachable (step state)
  ∀ (state : ExecutionState code), stateReachable state → (stepNoUniversallyInvalidOperations state)
  
Definition 
  ∀ (state : ExecutionState code), stateReachable state → (stepNoSpecificallyInvalidOperations state)
  ∀ (state : ExecutionState code), stateReachable state → stateCompleted state → (postconditions)
  ∀ (state : ExecutionState code), 

Parameter copy_nonoverlapping : Fn 
Axiom copy_nonoverlapping_something : copy_nonoverlapping

Definition swap : ∀ (T: RustType), Fn (PtrMut T :: PtrMut T :: Nil) Unit := 
  Code (
    Call copy_nonoverlapping (first , temporary) Ignore ::
    Call copy (second , first) Ignore ::
    Call copy_nonoverlapping (temporary , second) Ignore ::
    Nil)

Definition swap_validExecutionStates
  No lines completed, no guarantees
  first-line completed, temporary contains the same value as first
  second line completed, first contains original value of second, temporary contains original value of first
  All lines completed, first contains original value of second, second contains original value of first

Theorem swap_something : ∀ (initialMemory : Memory) (firstArgumentAddress secondArgumentAddress : Address) (noOverlap firstArgumentAddress secondArgumentAddress) 

Theorem swap_something : ∀ (state: ExecutionState) (nextState: ExecutionState) (swapStateValid state) (∀ address, address is one of the arguments → , (swapStateValid (state)

Theorem swap_something : ∀ (memoryBeforeStep : Memory) (nextState: ExecutionState) (swapStateValid state) (∀ address, address is one of the arguments → , (swapStateValid (state)
(* 
pub unsafe fn swap<T>(x: *mut T, y: *mut T) {
    // Give ourselves some scratch space to work with.
    // We do not have to worry about drops: `MaybeUninit` does nothing when dropped.
    let mut tmp = MaybeUninit::<T>::uninit();

    // Perform the swap
    // SAFETY: the caller must guarantee that `x` and `y` are
    // valid for writes and properly aligned. `tmp` cannot be
    // overlapping either `x` or `y` because `tmp` was just allocated
    // on the stack as a separate allocated object.
    unsafe {
        copy_nonoverlapping(x, tmp.as_mut_ptr(), 1);
        copy(y, x, 1); // `x` and `y` may overlap
        copy_nonoverlapping(tmp.as_ptr(), y, 1);
    }
} *)



(* Parameter modificationOrder (l : Location) : ∀ a b av bv, writesValue a l av → writesValue b l bv → Prop.
Parameter modificationOrderTrans (l : Location)  *)

(* Axiom writeWriteCoherence :  *)

(* Axiom. *)

Parameter MemoryOperation.
Parameter Location. (* basically "pointer with size" *)
Parameter Value.
Parameter Fn.

Parameter happensBefore : MemoryOperation → MemoryOperation → Prop.
Parameter overlaps : Location → Location → Prop.

Parameter observesLocation : MemoryOperation → Location → Prop.
Parameter writesValue : MemoryOperation → Location → Value → Prop.

Axiom happensBefore_decidable : ∀ a b, happensBefore a b ∨ ¬ happensBefore a b.
Axiom happensBefore_transitive : Transitive happensBefore.

(* note : this is slightly more permissive than the "visible sequence of side-effects" rule described at https://en.cppreference.com/w/cpp/atomic/memory_order, so I don't have to account for modification order *)
Definition CanObserve : MemoryOperation → Location → Value → Prop :=
  λ b l v, ∃ a,
    writesValue a l v ∧
    ¬ happensBefore b a ∧
    ¬ ∃ x v2 l2,
      overlaps l l2 ∧
      writesValue x l2 v2 ∧
      happensBefore a x ∧
      happensBefore x b.



Parameter copy_nonoverlapping : Location → Location → Fn.
Axiom copy_nonoverlapping_works : ∀ src dst (c : CompletedFunctionCall (copy_nonoverlapping src dst)), ¬ overlaps src dst → NothingInterferes → ∀ v, CanObserve (endOf c) dst v → CanObserve (startOf c) src v.
Axiom copy_nonoverlapping_noSideEffects : ∀ src dst (c : PartialFunctionCall (copy_nonoverlapping src dst)), ¬ overlaps src dst → NothingInterferes → ∀ o l v, operationIsPartOfCall o c → writesValue o l v → l = dst.
Axiom copy_nonoverlapping_noSideObservations : ∀ src dst (c : PartialFunctionCall (copy_nonoverlapping src dst)), ¬ overlaps src dst → NothingInterferes → ∀ o l, operationIsPartOfCall o c → observesLocation o l → l = src.








Parameter RustType.
Parameter RustValue : RustType → Set.

Parameter MemoryWrite.

Parameter Fn : list RustType → RustType → Set.

Parameter RustUnitType : RustType.
Parameter RustUnitValue : RustValue RustUnitType.
Parameter PtrMut : RustType → RustType.

Inductive SideEffect : Set :=
| MemoryWrite : ∀ T, Address → RustValue T → SideEffect.


Inductive Arguments : (argumentTypes : list RustType) → Set
| NoArguments : Arguments Nil
| ArgumentsCons : ∀ x xs, RustValue x → Arguments xs → Arguments (x :: xs)

Record Invocation : ∀ argumentTypes returnType, Fn argumentTypes returnType → Set := mkInvocation {
  invocationArguments : Arguments argumentTypes ;
  invocationSideEffects : list SideEffect ;
  }
  

Parameter copy_nonoverlapping T : Fn (PtrMut T :: PtrMut T :: Nil) RustUnitType.
Axiom copy_nonoverlapping_behavior : ∀ (invocation : Invocation copy_nonoverlapping) (value : RustValue T) (addressHoldsValueBefore invocation (nthArgument 0 invocation) value), SideEffects invocation = MemoryWrite (nthArgument 1 invocation) value :: Nil.

Definition swap : ∀ (T: RustType), Fn (PtrMut T :: PtrMut T :: Nil) RustUnitType := 
  Code (
    Call copy_nonoverlapping (first , temporary) Ignore ::
    Call copy (second , first) Ignore ::
    Call copy_nonoverlapping (temporary , second) Ignore ::
    Nil)


Theorem swap_behavior : ∀ (invocation : Invocation swap) (first second : RustValue T),
  (addressHoldsValueBefore invocation (nthArgument 0 invocation) first) →
  (addressHoldsValueBefore invocation (nthArgument 1 invocation) second) →
  SideEffects invocation =
    MemoryWrite (nthArgument 0 invocation) second :: 
    MemoryWrite (nthArgument 1 invocation) first :: Nil.
  
  copy_nonoverlapping_behavior
  
  
  
Inductive MemoryGuarantee : Set :=
| HoldsValue : Address → RustValue → MemoryGuarantee


Record Effects := mkEffects {
  stepsLeft : nat,
  memory : Memory,
  }

Definition Computation := Effects → Effects

Bind (f g : Computation) := f (g x)

Inductive FnResult returnType : Set :=
| Returned : RustValue returnType → Effects → FnResult
| HasntTerminated : Effects → FnResult
| UB : FnResult


Definition Fn argumentTypes returnType := Arguments argumentTypes → Effects → FnResult returnType


Parameter copy_nonoverlapping T : Fn (PtrMut T :: PtrMut T :: Nil) RustUnitType.
Axiom copy_nonoverlapping_behavior : ∀ arguments effects
  (srcAccess : HasNonatomicReadAccess effects (targetOf arguments [0]))
  (dstAccess : HasUniqueMutableAccess effects (targetOf arguments [1])),
  ¬ overlaps (targetOf arguments [0]) (targetOf arguments [1]) → stepsLeft effects > 0 → ∃ resultEffects
    (resultSrcAccess : HasNonatomicReadAccess resultEffects (targetOf arguments [0]))
    (resultDstAccess : HasUniqueMutableAccess resultEffects (targetOf arguments [1])),
      S (stepsLeft resultEffects) = stepsLeft effects ∧
      copy_nonoverlapping arguments effects = Returned RustUnitValue resultEffects ∧
      (readResult resultEffects resultDstAccess = readResult arguments srcAccess)
    

Definition isolate : Effects → EffectsUser → Effects


 Write :  
Axiom copy_nonoverlapping_behavior : ∀ (invocation : Invocation copy_nonoverlapping) (value : RustValue T) (addressHoldsValueBefore invocation (nthArgument 0 invocation) value), SideEffects invocation = MemoryWrite (nthArgument 1 invocation) value :: Nil.



Effectful returnType : Set


Inductive Effectful primitives returnType : Set :=
| Primitive : primitives → Effectful primitives returnType
| Bind : ∀ T, Effectful primitives T → (T → Effectful primitives returnType) → Effectful primitives returnType

Parameter callBehavior argumentTypes returnType : Fn argumentTypes returnType → Arguments argumentTypes → Effectful returnType

Axiom call_copy_nonoverlapping : callBehavior copy_nonoverlapping = 

Bind a b : Effectful a → (a → Effectful b) → Effectful b
Return a : Effectful a

UniqueMemoryOps : {
  read : ∀ T, Address T → Effectful T,
  write : ∀ T, Address T → T → Effectful RustUnitType,
  coherence : ∀ T (t : T) (addr : Address T) → Bind (write addr t) (λ _, read addr) 
}

