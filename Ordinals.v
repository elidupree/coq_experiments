Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.

(* Protect myself from accidental infinite loops during dev work *)
(* Set Typeclasses Iterative Deepening. *)
Set Typeclasses Depth 3.

Definition const [A B] (a:A) (b:B) := a.

Inductive Ordinal := oZ | ord_apply (level opIdx argument : Ordinal).
Notation "0" := oZ.

Notation "[ a b ]" := (ord_apply 0 a b) (at level 0).
(* Notation "l # a" := (ord_apply l a) (at level 0, format "l # a"). *)
Notation "[ @ l a b ]" := (ord_apply l a b) (at level 9, l at next level, a at next level, format "[ @ l  a  b ]").

  (* (A >L B) |- (@LAC = @LA(@LBC))
(L > M), (A >L B) |- (@LAC = @LA(@MCB)) *)
Inductive OrdLt : Ordinal -> Ordinal -> Ordinal -> Prop :=
  | ol_apply l a b : OrdLt l b [@l a b]
  | ol_trans l a b c : OrdLt l a b -> OrdLt l b c -> OrdLt l a c
  | ol_eq_left l a b c : OrdEq a b -> OrdLt l a c -> OrdLt l b c
  | ol_eq_right l a b c : OrdEq a b -> OrdLt l c a -> OrdLt l c b
  (* | ol_monotonic l a b c : OrdLt l a b -> OrdLt l [@l c a] [@l c b] *)
  (* | ol_eat_smaller_op l a b c d : OrdLt l a b -> OrdLt  *)
with OrdEq : Ordinal -> Ordinal -> Prop :=
  | oe_refl a : OrdEq a a
  | oe_eat_smaller_op l a b c : OrdLt l a b -> OrdEq [@l b c] [@l b [@l a c]]
  | oe_eat_smaller_arg l m a b c : OrdLt 0 l m -> OrdLt l a b -> OrdEq [@m b c] [@m b [@l c a]]
  .
Notation "a <0 b" := (OrdLt 0 a b) (at level 70, no associativity, b at next level) : type_scope.
Notation "a <[ l ] b" := (OrdLt l a b) (at level 70, no associativity, b at next level, format "a  <[ l ]  b") : type_scope.

Class Ordered A := { ordered_lt : A -> A -> Prop }.
Notation "a < b" := (ordered_lt a b) (at level 70, no associativity) : type_scope.

Instance nat_order : Ordered nat := { ordered_lt := lt }.
Instance ord_order : Ordered Ordinal := { ordered_lt := OrdLt 0 }.

Definition IsOrderEmbedding [A B] [_la : Ordered A] [_lb : Ordered B] (m : A -> B) := ∀ a0 a1, a0 < a1 -> m a0 < m a1.

Definition oS := ord_apply 0 0.
Definition oNat : nat -> Ordinal := nat_rect (const Ordinal) 0 (const oS).
Print oNat.

Lemma oNat_embeds : IsOrderEmbedding oNat.
  intro; intros.
  induction H; [constructor|].
  apply ol_trans with (oNat m).
  assumption.
  constructor.
Qed.

Lemma ol_zero_least l a : a <[l] 0 -> False.
  cbn.
  intro.
  dependent induction H.
  apply IHOrdLt2; reflexivity.
  apply IHOrdLt; reflexivity.
  dependent destruction H.
  apply IHOrdLt; reflexivity.
Qed.

Lemma olz_antisym a b : a <0 b -> b <0 a -> False.
  cbn.
  intros aLb bLa.
  dependent induction aLb.
  (* dependent destruction bLa. *)
  dependent induction b.
  (* induction b. *)
  exact (ol_zero_least bLa).
  dependent induction bLa.
  rewrite <- x in IHb3.
  discriminate.




Lemma ol_irrefl l a b : OrdEq a b -> a <[l] b -> False.
  intros aEb aLb. 
Qed.
  

Lemma ol_dec : 
Qed.

Lemma well_founded_ol : well_founded (OrdLt 0).
  constructor; intros.
  induction a.

  discriminate.
Qed.

Inductive TotalOrdering := less | equiv | greater.

(* ignoring >0 level for now... *)
(* Fixpoint canonicalize ignoreOpsBelow x : Ordinal :=
  match x with
  | 0 => 0
  | [@level opidx arg] => 

  . *)
(* ignoring >0 level for now... *)
Fixpoint ord_cmp aRelevantPrefix a bRelevantPrefix b {struct a} : TotalOrdering :=
  match (a, b) with
  | (0, 0) => equiv
  | (0, _) => less
  | (_, 0) => greater
  | ([@a_level a_opidx a_arg], [@b_level b_opidx b_arg]) =>
        (* TODO: update ignoreOpsBelow to the greatest of aRelevantPrefix, bRelevantPrefix;
        if we're looking at A(BC) <?> D(EF) then either B<A _or_ B<D means we can ignore it (the former changes nothing at all, the latter can be ignored because you can convert to A(BC) <?> D(B(EF)) which is the same as AC <?> D(EF))) 
        TODO: verify that last sameness claim formally *)
        let ignoreOpsBelow := aRelevantPrefix in
    

    match ord_cmp 0 a_opidx 0 ignoreOpsBelow with
    | less => ord_cmp aRelevantPrefix a_arg bRelevantPrefix [@b_level b_opidx b_arg]
    | _ => match ord_cmp 0 b_opidx 0 ignoreOpsBelow with
      | less => ord_cmp aRelevantPrefix a bRelevantPrefix b_arg
      | _ => 
        (* we have A(BC) <?> D(EF) with B,D > A,E *)
        match ord_cmp a_opidx a_arg b_opidx b_arg with
          (* if either came out bigger then that means one of them had an op bigger than anything we've seen, so it wins *)
        | less => less
        | greater => greater
        | equiv => match ord_cmp 0 a_opidx 0 b_opidx with
          | less => less
          | greater => greater
          | equiv => ord_cmp 0 aRelevantPrefix 0 bRelevantPrefix
          end
        end
      end
    end
  end.

Fixpoint ord_cmp l a b : TotalOrdering :=
  match (a, b) with
  | (0, 0) => equiv
  | (0, _) => less
  | (_, 0) => greater
  | ([@a_level a_opidx a_arg], [@b_level b_opidx b_arg]) =>
    (* ignoring >0 level for now... *)
    match ord_cmp 0 a_opidx b_opidx with
    | less => (* can convert AB <?> CD to AB <?> C(AD) and thence B <?> D *)
      match ord_cmp 0 a_arg b_arg with
      | less => less | greater => greater => 
  end.