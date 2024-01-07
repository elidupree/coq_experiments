Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_pred_imp
  | atom_and
  | atom_quote.

Inductive Formula :=
  | formula_atom : Atom -> Formula
  | formula_apply: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (formula_apply .. (formula_apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := formula_atom atom_const.
Definition fuse := formula_atom atom_fuse.
Definition pred_imp := formula_atom atom_pred_imp.
Definition f_and := formula_atom atom_and.
Definition f_quote := formula_atom atom_quote.
Definition f_id := [fuse const const].
Definition f_pair a b := [fuse [fuse f_id a] b].
Definition fp_fst := [fuse f_id const].
Definition fp_snd := [fuse f_id [const f_id]].

Definition Ruleset := Formula -> Formula -> Prop.

Fixpoint quote_formula f :=
  match f with
    | formula_atom _ => [f_quote f]
    | formula_apply a b => [f_quote (quote_formula a) (quote_formula b)]
    end.

Inductive UnfoldStep : Formula -> Formula -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c]
  (* | unfold_in_rhs a b c : UnfoldStep a b -> UnfoldStep [c a] [c b] *)
  | unfold_under_quote_0 a b : UnfoldStep a b ->
    UnfoldStep [f_quote a] [f_quote b]
  | unfold_under_quote_1 a b c : UnfoldStep a b ->
    UnfoldStep [f_quote c a] [f_quote c b].
  
Inductive UnfoldToQuotedFormula : Formula -> Formula -> Prop :=
  | unfold_quoted_done f : UnfoldToQuotedFormula (quote_formula f) f
  | unfold_step_then a b c : UnfoldStep a b -> UnfoldToQuotedFormula b c -> UnfoldToQuotedFormula a c.

(* Quoted formula streams: *)
(* [f => h => h const (f f)] *)
Definition qfs_tail_fn := [fuse
    [const [fuse [fuse f_id [const [f_quote f_quote]]]]]
    [fuse [const const] [fuse f_id f_id]]
  ].
Definition qfs_tail := [qfs_tail_fn qfs_tail_fn].

Inductive IsQuotedFormulaStream : Formula -> Prop :=
  | isqfs_tail : IsQuotedFormulaStream qfs_tail
  | isqfs_cons head tail : IsQuotedFormulaStream tail ->
    IsQuotedFormulaStream (f_pair (quote_formula head) tail).

Inductive RulesProveInference Rules : Formula -> Formula -> Prop :=
  | proof_by_rule a b : Rules a b -> RulesProveInference Rules a b
  | proof_by_transitivity a b c :
    RulesProveInference Rules a b ->
    RulesProveInference Rules b c ->
    RulesProveInference Rules a c.

Definition meaning
    (Rules : Ruleset)
    (UnknownMeanings : Formula -> Prop)
  : Formula -> Prop
  :=
    fix meaning (f : Formula) :=
      match f with
        (* [and a b] *)
        | formula_apply (formula_apply (formula_atom atom_and) a) b
          => meaning a /\ meaning b
        (* [pred_imp a b] *)
        | formula_apply (formula_apply (formula_atom atom_pred_imp) a) b
          => (∀ x, IsQuotedFormulaStream x -> ∃ ap bp,
            UnfoldToQuotedFormula [a x] ap /\ UnfoldToQuotedFormula [b x] bp /\
            RulesProveInference Rules ap bp)
        | _ => UnknownMeanings f
        end.

Definition InferenceJustified a b : Prop :=
  ∀Rules UnknownMeanings,
    (meaning Rules UnknownMeanings a) ->
    (meaning Rules UnknownMeanings b).

Definition RulesetJustified Rules : Prop :=
  ∀a b, Rules a b -> InferenceJustified a b.

Lemma provable_by_InferenceJustified_means_justified p c :
    RulesProveInference InferenceJustified p c
    ->
    InferenceJustified p c.
  intro.
  induction H; [assumption|clear H H0].
  unfold InferenceJustified in *.
  intros.
  specialize IHRulesProveInference1 with (Rules := Rules).
  specialize IHRulesProveInference1 with (UnknownMeanings := UnknownMeanings).
  specialize IHRulesProveInference2 with (Rules := Rules).
  specialize IHRulesProveInference2 with (UnknownMeanings := UnknownMeanings).
  exact (IHRulesProveInference2 (IHRulesProveInference1 H)).
Qed.

Lemma provable_by_justified_rules_means_justified R p c :
    RulesetJustified R ->
    RulesProveInference R p c ->
    InferenceJustified p c.
  unfold RulesetJustified in *.
  intros.
  induction H0.
  exact (H a b X).
  exact (provable_by_InferenceJustified_means_justified
    (proof_by_transitivity
      (proof_by_rule InferenceJustified a b IHRulesProveInference1)
      (proof_by_rule InferenceJustified b c IHRulesProveInference2)
    )).
Qed.

Lemma eq_justified : RulesetJustified eq.
  unfold RulesetJustified.
  unfold InferenceJustified.
  intros.
  subst b; assumption.
Qed.

Lemma provable_by_eq_means_eq p c :
  RulesProveInference eq p c -> p = c.
  intro.
  induction H; [assumption | ].
  subst b; assumption.
Qed.

  

Fixpoint fs_nth n := match n with
  | 0 => fp_fst
  | S p => [fuse [const (fs_nth p)] fp_snd]
  end.

Notation "@ n" := (fs_nth n) (at level 0).

Lemma stream_nth_quoted s n :
    IsQuotedFormulaStream s ->
    ∃ f, [(fs_nth n) s] = quote_formula f.
  intro.
  induction n.
  destruct H.
  induction n.
  admit.
  induction n.
Qed.

Definition f_true := [pred_imp @0 @0].
Definition f_false := [pred_imp [const f_true] @0].

Lemma false_unjustified :
  InferenceJustified f_true f_false -> False.
  unfold InferenceJustified; intro.

  (* use the very weak rules "eq",
    so it'll be easy to show that the rules don't prove what False says. *)
  specialize H with (Rules := eq).
  specialize H with (UnknownMeanings := λ _, True). (* doesn't matter *)
  cbn in H.

  (* Right now we basically have (meaning True -> meaning False),
     and we want to simplify this by _providing_ (meaning True).
     So we just say hey look, id x = id x. *)
  assert (∀ x : Formula,
    IsQuotedFormulaStream x
    → ∃ ap bp : Formula,
        UnfoldToQuotedFormula [(fp_fst) (x)] ap /\
        UnfoldToQuotedFormula [(fp_fst) (x)] bp /\
        RulesProveInference eq ap
        bp).
  intros; clear H.
  destruct (stream_nth_quoted 0 H0) as (q, qe).
  unfold fs_nth in qe.
  rewrite qe.
  apply ex_intro with q.
  apply ex_intro with q.

  split; [apply unfold_quoted_done|].
  split; [apply unfold_quoted_done|].
  apply proof_by_rule.
  reflexivity.

  assert (H := H H0); clear H0.

  (* Now, back to the main proving. *)
  specialize H with qfs_tail.
  destruct H as (ap, (bp, (ua, (ub, i)))); [apply isqfs_tail|].
  assert (j := provable_by_eq_means_eq i); clear i.
  subst bp.

  (* Now all we have to do is prove that [const true qfs_tail] and [@0 qfs_tail]
     can never unfold to the same thing.
     There are only finitely many possible unfoldings;
     this tells Coq to exhaust them. *)
  dependent destruction ua.
  dependent destruction ub.
  rewrite x0 in x; clear x0 f.
  dependent destruction x.
  dependent destruction c.
  dependent destruction x.
  dependent destruction x.
  dependent destruction H.
  dependent destruction ua.
  dependent destruction ub.
  rewrite x0 in x; clear x0 f.
  dependent destruction x.
  dependent destruction c.
  dependent destruction x.
  dependent destruction x.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
  (* repeat (dependent destruction ua || dependent destruction ub). *)
Qed.


Theorem justified_rulesets_are_consistent R :
    RulesetJustified R ->
    RulesProveInference R f_true f_false ->
    False.
  intros justified proved.
  exact (false_unjustified (provable_by_justified_rules_means_justified justified proved)).
Qed.


Notation "[ x & y ]" := [f_and x y] (at level 0, x at next level, y at next level).
Notation "[ x |= y ]" := [pred_imp x y] (at level 0, x at next level, y at next level).

Lemma and_sym_justified a b : InferenceJustified [a & b] [b & a].
  unfold InferenceJustified; intros; cbn in *.
  intuition.
Qed.

Lemma and_assoc1_justified a b c : InferenceJustified [a & [b & c]] [[a & b] & c].
  unfold InferenceJustified; intros; cbn in *.
  intuition.
Qed.

Lemma and_assoc2_justified a b c : InferenceJustified [[a & b] & c] [a & [b & c]].
  unfold InferenceJustified; intros; cbn in *.
  intuition.
Qed.
(* 
Lemma unfold_further :
  RulseProveInference a b *)

Lemma predimp_trans_justified a b c :
  InferenceJustified [[a |= b] & [b |= c]] [a |= c].
  unfold InferenceJustified; intros; cbn in *.
  intuition.
  specialize H0 with (x := x).
  specialize H1 with (x := x).
  destruct H0 as (ap0, (bp0, (ua0, (ub0, p0)))).
  destruct H1 as (ap1, (bp1, (ua1, (ub1, p1)))).

Qed.

Inductive IC : Ruleset :=
  | and_sym a b : IC [a & b] [b & a]
  | and_assoc1 a b c : IC [a & [b & c]] [[a & b] & c]
  | and_assoc2 a b c : IC [[a & b] & c] [a & [b & c]]
  | predimp_trans a b c : IC [[a |= b] & [b |= c]] [a |= c].


Definition rule_and_assoc a b := 



(* Theorem ic_is_consistent : (∀ i, RulesProve Justified (nil |- i)) -> False.
  intro.
  specialize H with (i := f_false).
  dependent induction H.

  (* "Can't be a premise, because there are none" *)
  unfold In in H; assumption.
  
  (* "How was the rule justified?" *)
  destruct H. *)



Parameter VariableIndex : Set.
Parameter VariableValues : Set.
Parameter get_variable_value: VariableValues-> VariableIndex ->Formula.

Inductive FormulaWithVariables :=
  | no_variables : Formula -> FormulaWithVariables
  | formula_variable : VariableIndex -> FormulaWithVariables
  | apply_with_variables:FormulaWithVariables -> FormulaWithVariables -> FormulaWithVariables.

Notation "v[ x y .. z ]" := (apply_with_variables .. (apply_with_variables x y) .. z)
 (at level 0, x at next level, y at next level).
Notation "n[ x ]" := (no_variables x)
 (at level 0, x at next level).

Fixpoint specialize_fwv f values :=
  match f with
    | no_variables f => f
    | formula_variable i => get_variable_value values i
    | apply_with_variables f x =>
        [(specialize_fwv f values) (specialize_fwv x values)]
    end.

Definition specialize_inf i values :=
  map_inf (λ p, specialize_fwv p values) i.

Inductive RuleSpecializes rule : Inference Formula -> Prop :=
  | rule_specializes values ps c :
    Forall2 (λ rule_p p, UnfoldToQuotedFormula (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    UnfoldToQuotedFormula (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).