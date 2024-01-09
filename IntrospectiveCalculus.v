Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_implies
  | atom_and
  | atom_all
  | atom_quote.

Inductive Formula :=
  | f_atm : Atom -> Formula
  | f_apl: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (f_apl .. (f_apl x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := f_atm atom_const.
Definition fuse := f_atm atom_fuse.
Definition f_implies := f_atm atom_implies.
Definition f_and := f_atm atom_and.
Definition f_all := f_atm atom_all.
Definition f_quote := f_atm atom_quote.
Definition f_id := [fuse const const].
Definition f_pair a b := [fuse [fuse f_id [const a]] [const b]].
Definition fp_fst := [fuse f_id [const const]].
Definition fp_snd := [fuse f_id [const f_id]].
Definition f_default := const.

Notation "[ x & y ]" := [f_and x y] (at level 0, x at next level, y at next level).
(* Notation "[ x &* y ]" := [fuse [fuse [const [f_quote [f_quote f_and]]] x] y] (at level 0, x at next level, y at next level). *)
Notation "[ x -> y ]" := [f_implies x y] (at level 0, x at next level, y at next level).

(* subset notation is used for rulesets (which are 2-way relations) *)
Notation "R ⊆2 S" := (∀ a b, R a b -> S a b) (at level 70).
Notation "R ⊇2 S" := (∀ a b, S a b -> R a b) (at level 70).
Notation "R ⊆ S" := (∀ a, R a -> S a) (at level 70).
Notation "R ⊇ S" := (∀ a, S a -> R a) (at level 70).
Notation "⋂ S" := (λ a, ∀ x, S x -> x a) (at level 70).
Notation "⋂2 S" := (λ a b, ∀ x, S x -> x a b) (at level 70).


Definition Ruleset := Formula -> Formula -> Prop.

Fixpoint quote_f f :=
  match f with
    | f_atm _ => [f_quote f]
    | f_apl a b => [f_quote (quote_f a) (quote_f b)]
    end.

Fixpoint unquote_formula f : option Formula :=
  match f with
    | f_apl (f_atm atom_quote) (f_atm a) =>
      Some (f_atm a)
    | f_apl (f_apl (f_atm atom_quote) a) b =>
      match (unquote_formula a,unquote_formula b) with
        | (Some a, Some b) => Some [a b]
        | _ => None
      end
    | _ => None
    end.

Lemma quote_unquote f : (unquote_formula (quote_f f)) = Some f.
  induction f; cbn.
  reflexivity.
  rewrite IHf1. rewrite IHf2. reflexivity.
Qed.

Fixpoint unfold_step f : option Formula :=
  match f with
    (* Atoms never unfold *)
    | f_atm _ => None
    (* Unfold in the LHS until you're done... *)
    | f_apl f x => match unfold_step f with
      | Some f => Some [f x]
      (* Then if you're done with the LHS, check its form... *)
      | None => match f with
        | f_apl (f_atm atom_const) a => Some a
        | f_apl (f_apl (f_atm atom_fuse) a) b => Some [[a x] [b x]]
        | (f_atm atom_quote) =>
          option_map (λ x, [f_quote x]) (unfold_step x)
        | f_apl (f_atm atom_quote) a =>
          option_map (λ x, [f_quote a x]) (unfold_step x)
        | _ => None
        end
      end
    end.
  
(* Fixpoint unfold_n steps f : Formula :=
  match steps with
    | 0 => f
    | S pred => match unfold_step f with
      | None => f
      | Some g => unfold_n pred g
      end
    end.
Fixpoint try_unfold_n steps f : option Formula :=
  match steps with
    | 0 => None
    | S pred => match unfold_step f with
      | None => Some f
      | Some g => try_unfold_n pred g
      end
    end.

Definition UnfoldsTo f g :=
  ∃ steps, try_unfold_n steps f = Some g.

Eval simpl in unfold_n 30 [fp_fst (f_pair f_quote f_and)].
Lemma pair_fst a b c : 
  UnfoldsTo a c ->
  UnfoldsTo [fp_fst (f_pair a b)] c.
  unfold UnfoldsTo. apply ex_intro with 20.
Qed. *)
  
Fixpoint try_unfold_to_quoted steps f : option Formula :=
  match steps with
    | 0 => None
    | S pred => match unfold_step f with
      | None => unquote_formula f
      | Some g => try_unfold_to_quoted pred g
      end
    end.

Definition UnfoldsToQuotedFormulaByFn f g :=
  ∃ steps, try_unfold_to_quoted steps f = Some g.

Inductive UnfoldStep : Formula -> Formula -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c]
  | unfold_in_rhs a b c : UnfoldStep a b -> UnfoldStep [c a] [c b].
  (* | unfold_under_quote_0 a b : UnfoldStep a b ->
    UnfoldStep [f_quote a] [f_quote b]
  | unfold_under_quote_1 a b c : UnfoldStep a b ->
    UnfoldStep [f_quote c a] [f_quote c b]. *)
  
(* Inductive UnfoldsToQuotedFormula : Formula -> Formula -> Prop :=
  | unfold_quoted_done f : UnfoldsToQuotedFormula (quote_f f) f
  | unfold_step_then a b c : UnfoldStep a b ->
    UnfoldsToQuotedFormula b c -> UnfoldsToQuotedFormula a c. *)

(* Quoted formula streams: *)
(* [f => h => h const (f f)] *)
Definition qfs_tail_fn := [fuse
    [const [fuse [fuse f_id [const [f_quote f_default]]]]]
    [fuse [const const] [fuse f_id f_id]]
  ].
Definition qfs_tail := [qfs_tail_fn qfs_tail_fn].
Definition qfs_cons head tail := f_pair (quote_f head) tail.
Inductive IsQuotedFormulaStream : Formula -> Prop :=
  | isqfs_tail : IsQuotedFormulaStream qfs_tail
  | isqfs_cons head tail : IsQuotedFormulaStream tail ->
    IsQuotedFormulaStream (qfs_cons head tail).


(* Definition ObeysIntrinsicMeanings TruthValues KnownJudgedInferences :=
  (∀ a b, KnownJudgedInferences a b ->
    TruthValues [(quote_f a) -> (quote_f b)]) /\
  (∀ a b, TruthValues [a & b] <-> TruthValues a /\ TruthValues b) /\
  (∀ a, TruthValues [f_all a] <->
    (∀ x, TruthValues [a (quote_f x)])) /\
  (∀ a b, UnfoldStep a b -> (TruthValues a <-> TruthValues b))
  . *)

(* Whether a formula is a true
   statement about a set of inferences. *)
Inductive TrueOf Infs : Formula -> Prop :=
  | t_implies a b :
      Infs a b ->
      TrueOf Infs [(quote_f a) -> (quote_f b)]
  | t_and a b :
      (TrueOf Infs a) -> (TrueOf Infs b) ->
      TrueOf Infs [a & b]
  | t_all a :
      (∀ x, TrueOf Infs [a (quote_f x)]) ->
      TrueOf Infs [f_all a]
  | t_unfold a b :
      UnfoldStep a b ->
      TrueOf Infs b -> TrueOf Infs a.

(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
Definition MetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  ∀ Infs,
    Infs ⊇2 KnownJudgedInferences ->
    (TrueOf Infs a -> TrueOf Infs b).

(* Definition MetaInferences KnownJudgedInferences (a b : Formula) :=
  ∀ TruthValues,
    (ObeysIntrinsicMeanings TruthValues KnownJudgedInferences) ->
    (TruthValues a -> TruthValues b). *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
Fixpoint KnownInferences n : Ruleset :=
  match n with
    | 0 => eq (* same as MetaInferences (λ _, False) *)
    | S pred => MetaInferences (KnownInferences pred)
    end.

Inductive RulesProveInference Rules : Formula -> Formula -> Prop :=
  | proof_by_rule a b : Rules a b -> RulesProveInference Rules a b
  | proof_by_transitivity a b c :
    RulesProveInference Rules a b ->
    RulesProveInference Rules b c ->
    RulesProveInference Rules a c.
Definition InferencesProvenBy Rules : Ruleset := RulesProveInference Rules.

(* Definition FormulaMeaning
    (Rules : Ruleset)
    (UnknownMeanings : Formula -> Prop)
  : Formula -> Prop
  :=
    fix FormulaMeaning (f : Formula) :=
      match f with
        (* [and a b] *)
        | f_apl (f_apl (f_atm atom_and) a) b
          => FormulaMeaning a /\ FormulaMeaning b
        (* [pred_imp a b] *)
        | f_apl (f_apl (f_atm atom_pred_imp) a) b
          => (∀ x,
            IsQuotedFormulaStream x -> ∃ ap bp,
              UnfoldsToQuotedFormula [a x] ap /\
              UnfoldsToQuotedFormula [b x] bp /\
              RulesProveInference Rules ap bp)
        | _ => UnknownMeanings f
        end. *)

(* Definition RulesetObeysInference Rules a b : Prop :=
  ∀UnknownMeanings,
    (FormulaMeaning Rules UnknownMeanings a) ->
    (FormulaMeaning Rules UnknownMeanings b).

Definition AllRulesetsObeyInference a b : Prop :=
  ∀Rules, RulesetObeysInference Rules a b. *)

(* Definition AllRulesetsObeyAllOf Rules : Prop :=
  ∀a b, Rules a b -> AllRulesetsObeyInference a b. *)

(* Definition InferencesTheseRulesetsObey These a b : Prop :=
  ∀Rules, These Rules -> RulesetObeysInference Rules a b. *)

(* Definition AllTheseRulesetsObeyAllOf These Rules : Prop :=
  ∀a b, Rules a b -> InferencesTheseRulesetsObey These a b. *)

(* Definition NoRules : Ruleset := λ _ _, False. *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that are possible
  in all rulesets that include the last *)
(* Fixpoint KnownRequiredInferences n : Ruleset :=
  match n with
    | 0 => eq
    | S pred => InferencesTheseRulesetsObey
      (λ Rules, (InferencesProvenBy Rules) ⊇2
        (KnownRequiredInferences pred))
    end. *)


Lemma MetaInferences_closed_under_transitivity K p c :
    RulesProveInference (MetaInferences K) p c
    ->
    (MetaInferences K) p c.
  intro.
  induction H; [assumption|clear H H0].
  unfold MetaInferences in *.
  intros.
  specialize IHRulesProveInference1 with (Infs := Infs).
  specialize IHRulesProveInference2 with (Infs := Infs).
  apply IHRulesProveInference2; [assumption|].
  apply IHRulesProveInference1; assumption.
Qed.

Lemma KnownInferences_closed_under_transitivity p c n :
    RulesProveInference (KnownInferences n) p c
    ->
    KnownInferences n p c.
    destruct n.
    intro. induction H. assumption. cbn in *. subst b. assumption.
    apply MetaInferences_closed_under_transitivity.
Qed.

Lemma proofs_monotonic_in_rules R1 R2 :
  (R1 ⊆2 R2) -> (InferencesProvenBy R1 ⊆2 InferencesProvenBy R2).
  intros. induction H.
  apply proof_by_rule. exact (X a b X0).
  apply proof_by_transitivity with b; assumption.
Qed.

Lemma provable_by_subset_of_KnownInferences_means_known n p c R :
    R ⊆2 KnownInferences n ->
    RulesProveInference R p c ->
    KnownInferences n p c.
  intros.
  exact (KnownInferences_closed_under_transitivity n
      (@proofs_monotonic_in_rules
        R (KnownInferences n) H p c H0)
    ).
Qed.

(* Lemma eq_justified These : AllTheseRulesetsObeyAllOf These eq.
  unfold AllTheseRulesetsObeyAllOf,
         InferencesTheseRulesetsObey,
         RulesetObeysInference.
  intros.
  subst b; assumption.
Qed. *)

Lemma provable_by_eq_means_eq p c :
  RulesProveInference eq p c -> p = c.
  intro.
  induction H; [assumption | ].
  subst b; assumption.
Qed.

Definition fs_pop_then handler :=
  [fuse [const handler] fp_snd].

Fixpoint fs_nth n := match n with
  | 0 => fp_fst
  | S p => fs_pop_then (fs_nth p)
  end.

Notation "@ n" := (fs_nth n) (at level 0).

(* Eval simpl in try_unfold_n 100 [fp_fst (f_pair f_quote f_quote)].
Eval simpl in unfold_step [@0 (qfs_cons const qfs_tail)].
Eval simpl in try_unfold_n 100 [@0 (qfs_cons const qfs_tail)]. *)

Lemma quoted_no_unfold f : unfold_step (quote_f f) = None.
  induction f; cbn.
  reflexivity.
  rewrite IHf1. rewrite IHf2. cbn. reflexivity.
Qed.

Lemma quoted_unfold_to_quoted a :
  try_unfold_to_quoted 1 (quote_f a) = Some a.
  induction a; cbn; [reflexivity|].
  rewrite (quoted_no_unfold a1).
  rewrite (quoted_no_unfold a2).
  rewrite (quote_unquote a1).
  rewrite (quote_unquote a2).
  cbn; reflexivity.
Qed.

Lemma ustep_fn_to_prop a b :
  (unfold_step a = Some (b)) -> UnfoldStep a b.
Qed.

Lemma utqf_fn_to_prop a b :
  UnfoldsToQuotedFormulaByFn a b -> UnfoldsToQuotedFormula a b.
  intro.
  destruct H.
  unfold UnfoldsToQuotedFormulaByFn.
  dependent induction x.
  cbn in H. dependent destruction H.
  cbn in H.
  destruct (unfold_step a).
  
  unfold try_unfold_to_quoted in H.
  unfold UnfoldsToQuotedFormula.
Qed.


  
Lemma pair_first_quoted_byfn a b :
  UnfoldsToQuotedFormulaByFn [fp_fst (f_pair (quote_f a) b)] a.
  unfold UnfoldsToQuotedFormulaByFn.
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.

  
Lemma pair_first_quoted a b :
  UnfoldsToQuotedFormula [fp_fst (f_pair (quote_f a) b)] a.
  
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_first :
  UnfoldsToQuotedFormulaByFn [fp_fst qfs_tail] f_default.
  unfold UnfoldsToQuotedFormulaByFn.
  apply ex_intro with 13.
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_tail handler hout:
    UnfoldsToQuotedFormula [handler qfs_tail] hout
    ->
    UnfoldsToQuotedFormula [(fs_pop_then handler) qfs_tail] hout.
  unfold UnfoldsToQuotedFormula.
  intro.
  destruct H as (steps, H).

  refine(
    fix ind h := match h with
  ).


  induction handler.
  contradict H. intro.
  unfold try_unfold_to_quoted in H. cbn in H.


  apply ex_intro with (10 + steps).
  rewrite <- H.
  unfold try_unfold_to_quoted; cbn.
  reflexivity.
  cbn.
  (* ; reflexivity. *)
Qed.


Lemma stream_nth_quoted s n :
    IsQuotedFormulaStream s ->
    ∃ f, UnfoldsToQuotedFormula [@n s] f.
  intro.
  unfold UnfoldsToQuotedFormula.
  induction n.
  (* zero case (@n = f_fst) *)
  destruct H.
  apply ex_intro with f_quote.
  apply ex_intro with 20.
  destruct H.
  cbn; reflexivity.

  apply ex_intro with f_quote. cbn. unfold quote_f. cbn.
  induction n.
  admit.
  induction n.
Qed.

Lemma unfold_unique a b c :
  UnfoldsToQuotedFormula a b ->
  UnfoldsToQuotedFormula a c ->
  b = c.
  intros.

Qed.

Definition f_true := [[f_quote f_default] -> [f_quote f_default]].
Definition f_false := [f_all [fuse [const f_all] f_implies]].

(* Lemma KnownRequiredInferences_increasing n :
  KnownRequiredInferences n ⊆2 KnownRequiredInferences (S n).
  intros.
  cbn. *)

Lemma True_known n :
  TrueOf (KnownInferences n) f_true.
  apply (t_implies (KnownInferences n) f_default f_default).
  destruct n; [reflexivity|].
  cbn. unfold MetaInferences. intros. assumption.
Qed.

Lemma false_never_known n :
  KnownInferences n f_true f_false -> False.
  induction n.
  intro. cbn in H. discriminate.

  intro.
  cbn in *. unfold MetaInferences in *.
  specialize H with (Infs := (KnownInferences n)).
  apply IHn; clear IHn.

  assert (TrueOf (KnownInferences n) f_false).
  apply H.
  intros; assumption.
  apply True_known.
  clear H.

  dependent destruction H0.
  specialize (H f_false). dependent destruction H; trivial.
  
  repeat (dependent destruction H || dependent destruction H0).
  dependent destruction H.

  apply (t_all (KnownInferences n) f_true f_false).
  
  (* pose (t_implies (KnownInferences n) f_true f_false). *)
  apply  in IHn.
  cbn in *.



  specialize H with (Rules := KnownRequiredInferences n).

  assert (InferencesProvenBy (KnownRequiredInferences n)
          ⊇2 KnownRequiredInferences n).
  intros. apply proof_by_rule; assumption.

  pose (H H0) as r. clearbody r. clear H H0.
  unfold RulesetObeysInference in r.
  specialize r with (UnknownMeanings := λ _, False).
  pose (r (True_required n (λ _, False))) as H. clearbody H. clear r.

  cbn in H.

  specialize H with (qfs_cons f_false qfs_tail).
  destruct H as (ap, (bp, (ua, (ub, i)))).
  apply isqfs_cons. apply isqfs_tail.
  
  (* TODO: coax Coq to understand this *)
  assert (ap = f_true) as apt. admit. rewrite apt in *. clear apt.
  assert (bp = f_false) as bpt. admit. rewrite bpt in *. clear bpt.
  
  exact (IHn (KnownRequiredInferences_closed_under_transitivity n i)).
Qed.

(* 
Lemma false_never_in_lower_bound_sequence n :
  LowerBoundSequence n f_true f_false -> False.
  induction n.
  unfold LowerBoundSequence, InferencesTheseRulesetsObey, RulesetObeysInference ; intros.
  cbn in H.
  (* use the very weak rules "eq",
    so it'll be easy to show that the rules don't prove what False says. *)
  (* specialize H with (Rules := eq). *)
  specialize (H eq X) with (UnknownMeanings := λ _, True). (* doesn't matter *)
  cbn in H.

  (* Right now we basically have (FormulaMeaning True -> FormulaMeaning False),
     and we want to simplify this by _providing_ (FormulaMeaning True).
     So we just say hey look, id x = id x. *)
  assert (∀ x : Formula,
    IsQuotedFormulaStream x
    → ∃ ap bp : Formula,
        UnfoldsToQuotedFormula [(fp_fst) (x)] ap /\
        UnfoldsToQuotedFormula [(fp_fst) (x)] bp /\
        RulesProveInference eq ap
        bp).
  intros; clear H.
  destruct (stream_nth_quoted 0 H0) as (q, qe).
  unfold fs_nth in qe.
  (* rewrite qe. *)
  apply ex_intro with q.
  apply ex_intro with q.

  split; [assumption|].
  split; [assumption|].
  (* split; [apply unfold_quoted_done|].
  split; [apply unfold_quoted_done|]. *)
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
Qed. *)


Theorem subsets_of_KnownInferences_are_consistent R n :
    R ⊆2 (KnownInferences n) ->
    RulesProveInference R f_true f_false ->
    False.
  intros justified proved.
  exact (false_never_known n (provable_by_subset_of_KnownInferences_means_known n justified proved)).
Qed.


Inductive ReifiedRule : Set :=
  .

Definition rule_external (rule : ReifiedRule) : Ruleset.
  admit. Admitted.

Definition rule_internal (rule : ReifiedRule) : Formula.
  admit. Admitted.

Definition and_sym : ReifiedRule.
  admit. Admitted.

Definition IC_reified_rules : list ReifiedRule :=
  and_sym ::
  nil.

Definition axioms rules : Formula :=
  fold_right
  (λ rule agg, [(rule_internal rule) & agg])
  f_true
  rules.

Definition IC_axioms : Formula :=
  axioms IC_reified_rules.

Definition IC_axioms_rule : Ruleset := (λ a b, b = IC_axioms).

Definition IC :=
  fold_right
  (λ rule agg a b, rule_external rule a b \/ agg a b)
  IC_axioms_rule
  IC_reified_rules.

Lemma and_sym_known : (rule_external and_sym ⊆2 KnownInferences 1).
Qed.

Lemma IC_external_rules_known :
  Forall
    (λ rule, (rule_external rule ⊆2 KnownInferences 1))
    IC_reified_rules.
  constructor; [apply and_sym_known|].
  trivial.
Qed.

Lemma internalize_rule_known rule :
  (rule_external rule ⊆2 KnownInferences 1) ->
  (KnownInferences 2 f_true (rule_internal rule)).
  
Qed.

Lemma IC_axioms_known :
  Forall
    (λ rule, (KnownInferences 2 f_true (rule_internal rule)))
    IC_reified_rules.
  apply Forall_impl with (λ rule, (rule_external rule ⊆2 KnownInferences 1)).
  apply internalize_rule_known.
  apply IC_external_rules_known.
Qed.

Lemma and_join t a b :
  KnownInferences 2 t a ->
  KnownInferences 2 t b ->
  KnownInferences 2 t [a & b].
  intros.
  unfold KnownInferences, MetaInferences in *.
  intros.
  apply t_and.
  apply H; trivial.
  apply H0; trivial.
Qed.


Lemma axioms_known a
  (rules : list ReifiedRule)
  (known : Forall
    (λ rule, (KnownInferences 2 a (rule_internal rule)))
    rules) : KnownInferences 2 a (axioms rules).
  
  induction rules as [|rule].
  cbn. unfold MetaInferences. intros. apply True_known. assumption.

  dependent destruction known.
  apply IHrules in known; clear IHrules.
  apply and_join; assumption.
Qed.

Lemma IC_axioms_rule_known :
  IC_axioms_rule ⊆2 KnownInferences 2.
  pose (axioms_known IC_axioms_known).

  intros. unfold IC_axioms_rule in H. rewrite H; clear H.
Qed.



Inductive Abstraction F :=
  | abstraction_const : F -> Abstraction F
  | abstraction_usage : Abstraction F
  | abstraction_apply :
      Abstraction F -> Abstraction F -> Abstraction F.



Notation "[ x => B ]" := (λ x, B)
  (at level 0, x at next level, y at next level).



(* ∀x, ∀y, [x & y] -> [y & x] *)
Definition and_sym_axiom := [[@0 &* @1] -> [@1 &* @0]].

Lemma and_sym_known a b : KnownInferences 1 [a & b] [b & a].
  unfold KnownInferences, MetaInferences.
  intros. cbn in *.
  dependent destruction H.
  apply t_and; assumption.
  (* repeat (dependent destruction H). *)
Qed.

Eval cbn in FormulaMeaning eq _ [_ & _].
Lemma and_sym_axiom_known : KnownRequiredInferences 2 f_true and_sym_axiom.
  unfold KnownRequiredInferences, InferencesTheseRulesetsObey,
    RulesetObeysInference.
  intros. cbn in *. intros.
  clear H0. (* we're not going to use the proof of True *)
  
Qed.

Lemma and_assoc1_required a b c : KnownRequiredInferences 1 [a & [b & c]] [[a & b] & c].
  unfold KnownRequiredInferences, InferencesTheseRulesetsObey, RulesetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.

Lemma and_assoc2_required a b c : KnownRequiredInferences 1 [[a & b] & c] [a & [b & c]].
  unfold KnownRequiredInferences, InferencesTheseRulesetsObey, RulesetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.
(* 
Lemma unfold_further :
  RulseProveInference a b *)

Lemma predimp_trans_required a b c :
  AllRulesetsObeyInference [[a |= b] & [b |= c]] [a |= c].
  unfold AllRulesetsObeyInference, RulesetObeysInference; intros; cbn in *.
  intuition idtac.
  specialize H0 with (x := x).
  specialize H1 with (x := x).
  destruct (H0 H) as (ap0, (bp0, (ua0, (ub0, p0)))).
  destruct (H1 H) as (bp1, (cp1, (ub1, (uc1, p1)))).
  clear H0 H1.
  apply ex_intro with ap0.
  apply ex_intro with cp1.
  split; [assumption|].
  split; [assumption|].
  rewrite (unfold_unique ub0 ub1) in *.
  apply proof_by_transitivity with bp1; assumption.
Qed.

Inductive IC : Ruleset :=
  | drop a b : IC [a & b] a
  | dup a b : IC [a & b] [[a & a] & b]
  | and_sym a b : IC [a & b] [b & a]
  | and_assoc1 a b c : IC [a & [b & c]] [[a & b] & c]
  | and_assoc2 a b c : IC [[a & b] & c] [a & [b & c]]
  | predimp_trans a b c t :
    IC [t &[[a -> b] & [b -> c]]]
       [t & [a -> c]]
  (* |  *)
  (* | axioms : IC f_true [and_sym_axiom & [some_other_axiom & more_axioms]] *)
  .

Lemma IC_known : IC ⊆2 KnownInferences 2.
  intros.
  destruct H.
  (* admit. admit. *)
  apply and_sym_known.
  apply and_assoc1_required.
  apply and_assoc2_required.
  apply predimp_trans_required.
Qed.

Theorem IC_is_consistent : ~(RulesProveInference IC f_true f_false).
  intro.
  pose 2 as n.
  exact (false_never_known n
    (provable_by_subset_of_KnownInferences_means_known n IC_known H)).
Qed.

Theorem IC_self_describing a b :
  RulesProveInference IC f_true [(quote_f a) -> (quote_f b)] ->
  RulesProveInference IC a b.
Qed.

Theorem IC_deduction a b :
  RulesProveInference IC a b ->
  RulesProveInference IC f_true [(quote_f a) -> (quote_f b)].
  intros.
  (* rule or transitivity? *)
  induction H.

  (* rule case: what rule? *)
  induction H.

  (* mostly just using axioms to fulfill rules: *)
  admit. admit. admit. admit.


  

  (* transitivity: *)
  admit.
Qed.

(* Theorem IC_deduction a b :
  TrueOf (InferencesProvenBy IC) a  *)

Lemma IC_proves_all_known n :
  KnownInferences n ⊆2 InferencesProvenBy IC.
  (* intros. *)

  induction n.

  admit.

  (* apply IHn; clear IHn. *)

  intros.
  unfold KnownInferences in H.
  unfold MetaInferences in H.

  (* pose (InferencesProvenBy IC) as Infs. *)
  assert (∀ Infs, (Infs ⊇2 InferencesProvenBy IC) -> )

  specialize (H Infs).
  pose (H IHn) as I. clearbody I. clear H.

  unfold KnownInferences, MetaInferences.
  

Qed.



Inductive FormulaMeaning2 PreviousMeanings : Formula -> Prop -> Prop :=
  | meaning_and a b A B :
    FormulaMeaning2 PreviousMeanings a A -> 
    FormulaMeaning2 PreviousMeanings b B -> 
    FormulaMeaning2 PreviousMeanings [a & b] (A /\ B)
  | meaning_implies a b :
    FormulaMeaning2 PreviousMeanings [a |= b]
      ((PreviousMeanings a) -> (PreviousMeanings b)).
    
  

Inductive FormulaTrue KnownInferences : Formula -> Prop :=
  | true_unfold a b :
    UnfoldStep a b ->
    FormulaTrue KnownInferences b -> 
    FormulaTrue KnownInferences a
  | true_and a b :
    FormulaTrue KnownInferences a -> 
    FormulaTrue KnownInferences b -> 
    FormulaTrue KnownInferences [a & b]
  (* | true_implies1 qa qb a :
    UnfoldsToQuotedFormula qa a ->
    (KnownInferences a -> False) ->
    FormulaTrue KnownInferences [qa |= qb]
  | true_implies2 qa qb b :
    UnfoldsToQuotedFormula qb b ->
    KnownInferences b ->
    FormulaTrue KnownInferences [qa |= qb] *)
  | true_implies a b :
    (KnownInferences a b) ->
    FormulaTrue KnownInferences
      [(quote_f a) |= (quote_f b)]
  | true_all f :
    (∀ x, FormulaTrue KnownInferences [f x])
    -> FormulaTrue KnownInferences [fuse f].

(* sets of sets of true formulas *)
(* a decreasing sequence (of sets-of-sets),
   with more formulas forced to be true each time *)
Fixpoint Sequence n (IsTrue : Formula -> Prop) := match n with
  | 0 => True
  | S pred => ∀ PreviouslyTrue,
    (Sequence pred) PreviouslyTrue ->
    ∀ f, FormulaTrue (PreviouslyTrue) f -> IsTrue f
  end.
(* or, increasing sequence (of sets of true formulas),
   with more formulas forced to be true each time *)
Definition InferencesBetween Truths (a b: Formula) := (Truths a -> Truths b).
Definition KnownInferences PreviousInferences (a b : Formula) :=
  ∀ Inferences Truths,
    (Inferences ⊇2 PreviousInferences) ->
    (InferencesBetween Truths ⊇2 PreviousInferences) ->
    (Truths ⊇ FormulaTrue Inferences) ->
    (Truths a -> Truths b).
    
Fixpoint KnownTrue n f := match n with
  | 0 => False
  | S pred => ∀ IsTrue,
    (∀ g, (KnownTrue pred) g -> IsTrue g) ->
    FormulaTrue IsTrue f
  end.
(* sets of meanings *)
Fixpoint SequenceM n Meanings := match n with
  | 0 => True
  | S pred => ∀ PreviousMeanings,
    (SequenceM pred) PreviousMeanings ->
    ∀ f M,
      FormulaMeaning2 PreviousMeanings f M ->
      Meanings f = M
  end.

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
    Forall2 (λ rule_p p, UnfoldsToQuotedFormula (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    UnfoldsToQuotedFormula (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).