
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
 
 
 
Definition ChurchNaturalT := ∀(P : Type) ,(P → P) → P →P.
Definition ChurchNaturalTLower : ChurchNaturalT → ChurchNatural := λ n, n ChurchNatural churchSuccessor churchZero.
Definition churchZeroT : ChurchNaturalT := λ _ _ p , p.
Definition churchSuccessorT : ChurchNaturalT → ChurchNaturalT := λ predecessor P f p ,f (predecessor P f p).
Eval cbv in ChurchNaturalTLower.
Definition GenericNaturalIsInductiveT := λ(Natural : Type)(zero : Natural)(successor : Natural → Natural)(n : Natural),∀ (P : Natural →Type) (zeroCase :P zero)(successorCase :∀ (m : Natural) ,P m →P (successor m)),P n.

Definition ChurchNaturalIsInductiveT := GenericNaturalIsInductiveT ChurchNaturalT churchZeroT churchSuccessorT.
 (* λ(n : ChurchNatural),∀ (P : ChurchNatural →Prop) (zeroCase :P churchZero)(successorCase :∀ (m : ChurchNatural) ,P m →P (churchSuccessor m)),P n. *)
Definition churchZeroIsInductiveT : ChurchNaturalIsInductiveT churchZeroT:= (λ _ zeroCase _, zeroCase).
Definition churchSuccessorIsInductiveT : ∀(n : ChurchNaturalT), ChurchNaturalIsInductiveT n →ChurchNaturalIsInductiveT (churchSuccessorT n):= λ n nIsInductive, (λ P zeroCase successorCase, successorCase n (nIsInductive P zeroCase successorCase)).

Definition ExistentialT :=λ(T : Type)(P :T → Type), ∀ (C : Type),(∀(t : T),P t→ C) → C.
Definition ExistentialConstructorT :=λ(T : Type)(P :T → Type)(t : T) (p : P t)(C : Type)(consumer :(∀(t : T),P t→ C) ), consumer t p.

Definition nargs : ∀ (n : ChurchNaturalT), Type := λ n, n Prop (λ (thingy : Prop) , (∀ (A : True), thingy)) True.
Eval cbv in (nargs churchZeroT).
Definition nargs_val : ∀ (n : ChurchNaturalT), ChurchNaturalIsInductiveT n → nargs n := λ n nIsInductive,
  nIsInductive nargs I (λ m (thingy : nargs m) , (λ (A : True), thingy)).

Eval cbv in (nargs (λ(P : Type) r p, r (r (r (r (r p)))))).
Eval cbv in (nargs_val 
  (churchSuccessorT (churchSuccessorT churchZeroT))
  (churchSuccessorIsInductiveT (churchSuccessorT churchZeroT) (churchSuccessorIsInductiveT churchZeroT churchZeroIsInductiveT))
).
Eval cbv in nargs.
 
 Definition Term : Type := ∀ (P : Type),
   ∀ (PropReduce : P) ,
   ∀ (TypeReduce : P) ,
   ∀ (VarReduce : P) ,
   ∀ (PopReduce : P → P) ,
   ∀ (LambdaReduce : P → P → P) ,
   ∀ (ForAllReduce : P → P → P) ,
   ∀ (ApplyReduce : P → P → P) ,
   P.
Definition prop : Term := λ p pr t v po l f a , pr.
Definition type : Term := λ p pr t v po l f a , t.
Definition var : Term := λ p pr t v po l f a , v.
Definition pop : Term → Term := λ m p pr t v po l f a , po (m p pr t v po l f a).
Definition lambda : Term → Term → Term := λ m n p pr t v po l f a , l (m p pr t v po l f a) (n p pr t v po l f a) .
Definition forAll : Term → Term → Term := λ m n p pr t v po l f a , f (m p pr t v po l f a) (n p pr t v po l f a) .
Definition apply : Term → Term → Term := λ m n p pr t v po l f a , a (m p pr t v po l f a) (n p pr t v po l f a) .

Definition TermIsInductive : Term → Prop := λ (t : Term) , ∀ (P : Term → Prop) ,
   ∀ (PropReduce : P prop) ,
   ∀ (TypeReduce : P type) ,
   ∀ (VarReduce : P var) ,
   ∀ (PopReduce : ∀(m : Term) , P m → P (pop m)) ,
   ∀ (LambdaReduce : ∀(m n : Term), P m → P n → P (lambda m n)) ,
   ∀ (ForAllReduce : ∀(m n : Term), P m → P n → P (forAll m n)) ,
   ∀ (ApplyReduce : ∀(m n : Term), P m → P n → P (apply m n)) ,
   P t.
   
Definition propIsInductive : TermIsInductive prop := λ p pr t v po l f a , pr.
Definition typeIsInductive : TermIsInductive type := λ p pr t v po l f a , t.
Definition varIsInductive : TermIsInductive var := λ p pr t v po l f a , v.
Definition popIsInductive : ∀(m : Term),
  TermIsInductive m → TermIsInductive (pop m) := 
  λ m mi p pr t v po l f a , po m (mi p pr t v po l f a).
Definition lambdaIsInductive : ∀(m n : Term),
  TermIsInductive m → TermIsInductive n → TermIsInductive (lambda m n) := 
  λ m n mi ni p pr t v po l f a , l m n (mi p pr t v po l f a) (ni p pr t v po l f a).
Definition forAllIsInductive : ∀(m n : Term),
  TermIsInductive m → TermIsInductive n → TermIsInductive (forAll m n) := 
  λ m n mi ni p pr t v po l f a , f m n (mi p pr t v po l f a) (ni p pr t v po l f a).
Definition applyIsInductive : ∀(m n : Term),
  TermIsInductive m → TermIsInductive n → TermIsInductive (apply m n) := 
  λ m n mi ni p pr t v po l f a , a m n (mi p pr t v po l f a) (ni p pr t v po l f a).

Definition Context : Prop := ∀ (P : Prop),
   ∀ (NilReduce : P) ,
   ∀ (ConsReduce : Term → P → P) ,
   P.

Definition emptyContext : Context := λ _ n _, n.
Definition consContext : Term → Context → Context := λ h t p n c, c h (t p n c).
   
 Definition TypeJudgmentT : Context → Term → Prop := λ context valueTerm typeTerm ,
   ∀ (∀ (PropReduce : P emptyContext prop type → Type) ,
   ∀ (∀ (TypeReduce : P) ,
   ∀ (∀ (PopReduce : P → P) ,
   ∀ (∀ (LambdaReduce : P → P → P) ,
   ∀ (∀ (ForAllReduce : P → P → P) ,
   ∀ (∀ (ApplyReduce : P → P → P) ,
   → Type.

Definition TypeJudgmentTIsInductive : ∀(c:Context)(t:Term), TypeJudgmentT c t → Type := λ (t : Term) , ∀ (P : Term → Type) ,
   ∀ (PropReduce : P prop) ,
   ∀ (VarReduce : P var) ,
   ∀ (PopReduce : ∀(m : Term) , P m → P (pop m)) ,
   ∀ (ForAllReduce : ∀(m n : Term), P m → P n → P (forAll m n)) ,
   ∀ (ApplyReduce : ∀(m n : Term), P m → P n → P (apply m n)) ,
   P t.
   
Definition propJudgment : TypeJudgment emptyContext prop type := .

Definition interpretT : ∀(c:Context)(t:Term), TermIsInductive t → Judgment c t type → Type := λ context term judgment ,
  judgment
    
    (λ ??, Prop)
    
    (λ (A : Prop), A → type)
    (λ (A : Type), A → type).
    
    
    
    (λ (A : Prop), A → B)
    (λ (A : Type) (B : Type), A → B)
    (λ , ∀ (a : A), B)
    (λ , ∀ (a : A), type)
    (λ , ∀ (a : A), B)
    
    .
interpret : ∀(c:Context)(t:Term)(ty:Term), (ty != TermT) -> (Judgment c t ty) -> ∃(A:T),A


Definition nargs : ∀ (n : ChurchNatural), Prop := λ n, n Prop (∀ (thingy : Prop) , (∀ (A : True), thingy)) True. 


Definition Weird : ∀ (q : bool), match q with
| true => True
| false => ~ False
end := λ q , match q with
| true => I
| false => λ f, f
end.

Lemma Foo: True.
  refine (Weird true).
  refine (_ _).













