
(* Logic *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' t ']'").


Definition ChurchNatural := ∀(P : Prop) ,(P → P) → P →P.
Definition churchZero : ChurchNatural := λ _ _ p , p.
Definition churchSuccessor : ChurchNatural → ChurchNatural := λ predecessor P f p ,f (predecessor P f p).

Definition Existential :=λ(T : Prop)(P :T → Prop), ∀ (C : Prop),(∀(t : T),P t→ C) → C.
Definition ExistentialConstructor :=λ(T : Prop)(P :T → Prop)(t : T) (p : P t)(C : Prop)(consumer :(∀(t : T),P t→ C) ), consumer t p.



Definition GenericNaturalIsInductive := λ(Natural : Prop)(zero : Natural)(successor : Natural → Natural)(n : Natural),∀ (P : Natural →Prop) (zeroCase :P zero)(successorCase :∀ (m : Natural) ,P m →P (successor m)),P n.

Definition ChurchNaturalIsInductive := GenericNaturalIsInductive ChurchNatural churchZero churchSuccessor.
 (* λ(n : ChurchNatural),∀ (P : ChurchNatural →Prop) (zeroCase :P churchZero)(successorCase :∀ (m : ChurchNatural) ,P m →P (churchSuccessor m)),P n. *)
Definition churchZeroIsInductive : ChurchNaturalIsInductive churchZero:= (λ _ zeroCase _, zeroCase).
Definition churchSuccessorIsInductive : ∀(n : ChurchNatural), ChurchNaturalIsInductive n →ChurchNaturalIsInductive (churchSuccessor n):= λ n nIsInductive, (λ P zeroCase successorCase, successorCase n (nIsInductive P zeroCase successorCase)).

Definition InductiveNatural := Existential ChurchNatural ChurchNaturalIsInductive.
Definition InductiveNaturalConstructor := ExistentialConstructor ChurchNatural ChurchNaturalIsInductive.
Definition inductiveZero : InductiveNatural := InductiveNaturalConstructor churchZero churchZeroIsInductive.
Definition inductiveSuccessor : InductiveNatural →InductiveNatural := λ predecessor ,
  predecessor InductiveNatural (λ churchPredecessor churchPredecessorIsInductive,
      InductiveNaturalConstructor (churchSuccessor churchPredecessor) (churchSuccessorIsInductive churchPredecessor churchPredecessorIsInductive)
  ).

(* Definition InductiveNaturalIsInductive := λ(n : InductiveNatural),∀ (P : InductiveNatural →Prop) (zeroCase :P inductiveZero)(successorCase :∀ (m : InductiveNatural) ,P m →P (inductiveSuccessor m)),P n.
Definition inductiveZeroIsInductive : InductiveNaturalIsInductive inductiveZero := λ P inductiveZeroCase inductiveSuccessorCase, inductiveZeroCase.
Definition inductiveSuccessorIsInductive : ∀(n : InductiveNatural), InductiveNaturalIsInductive n →InductiveNaturalIsInductive (inductiveSuccessor n):= λ n nIsInductive, (λ P zeroCase successorCase, successorCase n (nIsInductive P zeroCase successorCase)).
Definition EveryInductiveNaturalIsInductive : ∀ n, InductiveNaturalIsInductive n := λ n P inductiveZeroCase inductiveSuccessorCase,
 n (InductiveNaturalIsInductive n) (λ churchN churchNIsInductive,
   churchNIsInductive
     (λ churchM, Existential (ChurchNaturalIsInductive churchM) (λ churchMIsInductive, InductiveNaturalIsInductive (InductiveNaturalConstructor churchM churchMIsInductive)))
     (ExistentialConstructor _ _ churchZeroIsInductive inductiveZeroIsInductive)
     (λ churchPredecessor bothPredecessorAreInductive,
         bothPredecessorAreInductive _ (λ churchPredecessorIsInductive inductivePredecessorIsInductive,
           (ExistentialConstructor _ _ (churchSuccessorIsInductive churchPredecessor churchPredecessorIsInductive) (inductiveSuccessorIsInductive (InductiveNaturalConstructor  churchPredecessor  churchPredecessorIsInductive) inductivePredecessorIsInductive))
       
       )
     
     )
     (*we now have the ∃ churchNIsInductive inductiveNIsInductive; unpack it *)
     (InductiveNaturalIsInductive n)
     (λ churchNIsInductive inductiveNIsInductive,
       inductiveNIsInductive
     )
     
 ). *)
 
 Definition ChurchTerm := ∀ (P : Prop),
   ∀ (PropReduce : P) ,
   ∀ (TypeReduce : P) ,
   ∀ (PopReduce : P → P) ,
   ∀ (LambdaReduce : P → P → P) ,
   ∀ (ForAllReduce : P → P → P) ,
   ∀ (ApplyReduce : P → P → P) ,
   P.
Definition churchProp : ChurchTerm := λ p pr t po l f a , pr.
Definition churchApply : ChurchTerm → ChurchTerm → ChurchTerm := λ m n p pr t po l f a , a (m p pr t po l f a) (n p pr t po l f a) .

Definition InductiveTerm := λ (t : ChurchTerm) , ∀ (P : ChurchTerm → Prop) ,
   ∀ (PropReduce : P churchProp) ,
   ∀ (TypeReduce : P) ,
   ∀ (PopReduce : P) ,
   ∀ (LambdaReduce : P) ,
   ∀ (ForAllReduce : P) ,
   ∀ (ApplyReduce : ∀(m n : ChurchTerm), P (churchApply m n)) ,
   P.
  













