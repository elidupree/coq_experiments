Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_pred_imp
  | atom_list_cons.

Inductive Formula :=
  | formula_atom : Atom -> Formula
  | formula_apply: Formula-> Formula-> Formula.

Notation "[ x y .. z ]" := (formula_apply .. (formula_apply x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const := formula_atom atom_const.
Definition fuse := formula_atom atom_fuse.
Definition pred_imp := formula_atom atom_pred_imp.
Definition f_cons := formula_atom atom_list_cons.
Definition f_nil := const.

Record Inference F := makeInf
  { inf_premises: list F
  ; inf_conclusion: F
  }.

Notation "ps |- c" := {| inf_premises := ps; inf_conclusion := c |} (at level 80).

Print inf_conclusion.
Definition map_inf A B (f : A -> B) i :=
  ((map f (inf_premises i)) |- f (inf_conclusion i)).
Definition zipmap_inf A B C (f : A -> B -> C) i :=
  ((map f (inf_premises i)) |- f (inf_conclusion i)).
Definition map_inf_to_coq_prop A (f : A -> Prop) i :=
  ((Forall f (inf_premises i)) -> f (inf_conclusion i)).

(* Definition InternalPredicateToBeRepresentedAsAFormula := Inference Formula. *)
Definition InternalPredicate := Formula.
Definition PropositionPreF := Inference InternalPredicate.
Definition InferenceBetweenPropositions := Inference PropositionPreF.
Definition Rule := InferenceBetweenPropositions -> Prop.

Fixpoint f_pred_list ps :=
  match ps with
    | nil => f_nil
    | cons x xs => [f_cons x (f_pred_list xs)]
    end.
  
Definition f_prop (p : PropositionPreF) : Formula :=
  [pred_imp (f_pred_list (inf_premises p)) (inf_conclusion p)].
    
Definition f_pred_inf_transform i : Formula :=
  [pred_imp (f_pred_list (inf_premises i)) (inf_conclusion i)].

Inductive Unfold : Formula -> Formula -> Prop :=
  | unfold_nothing f : Unfold f f
  | unfold_const f a b : Unfold f [const a] -> Unfold [f b] a
  | unfold_fuse f a b c : Unfold f [fuse a b] -> Unfold [f c] [[a c] [b c]]
  | unfold_pred_imp a b c d : Unfold a b -> Unfold c d -> Unfold [pred_imp a c] [pred_imp b d]
  | unfold_pred_and a b c d : Unfold a b -> Unfold c d -> Unfold [f_cons a c] [f_cons b d].

Definition UnfoldToProposition : Formula -> PropositionPreF -> Prop :=
  λ f i, Unfold f (f_prop i).
  
Inductive MappedList A B f : list A -> list B -> Prop :=
  | MappedList_nil : MappedList f nil nil
  | MappedList_cons a b atl btl :
    f a b -> MappedList f atl btl -> MappedList f (a::atl) (b::btl).
  

Inductive RulesProvePropInf Rules : InferenceBetweenPropositions -> Prop :=
  | proof_by_premise ps c : In c ps -> RulesProvePropInf Rules (ps |- c)
  | proof_by_rule specialized ps :
    Rules specialized ->
    map_inf_to_coq_prop (λ f, RulesProvePropInf Rules (ps |- f)) specialized.
    (* Forall (λ spec_premise, RulesProvePropInf Rules (ps |- spec_premise)) (inf_premises specialized) ->
    RulesProvePropInf Rules (ps |- (inf_conclusion specialized)). *)

Definition RulesProveFormulaInf Rules fi :=
  ∃ ps c, RulesProvePropInf Rules (ps |- c)
    /\ MappedList UnfoldToProposition (inf_premises fi) ps
    /\ UnfoldToProposition (inf_conclusion fi) c.
  
Definition RulesProveIntPredInf Rules (i : Inference InternalPredicate) :=
  ∀x, RulesProveFormulaInf Rules (map_inf (λ p, [p x]) i).

(* "if these rules prove all inferences on the left...
    then they prove the inference on the right" *)
Definition RulesTransformIntPredInfs Rules
  (pred_infs : Inference (Inference InternalPredicate)) : Prop :=
  map_inf_to_coq_prop
    (λ pred_inf, RulesProveIntPredInf Rules pred_inf)
    pred_infs.

Definition IntPredInfTransformJustified pred_infs : Prop :=
  ∀Rules, RulesTransformIntPredInfs Rules pred_infs.

(* Definition pred_inf_transform_to_inf
  (pred_infs : Inference (Inference InternalPredicate))
  : Inference PropositionPreF
  := map_inf f_prop pred_infs. *)

Inductive InferenceJustified : Inference PropositionPreF -> Prop :=
| inference_justified pred_infs :
  (IntPredInfTransformJustified pred_infs) ->
  InferenceJustified pred_infs.

Lemma forall_in A P l (x:A) : Forall P l -> In x l -> P x.
  (* specialize Forall_forall with (A := A), P:=P). *)
Admitted.

Theorem justified_rules_make_justified_proofs :
  ∀ i,
    RulesProvePropInf InferenceJustified i
    ->
    InferenceJustified i.
  
  intro; destruct i as (original_ps, original_c).

  (* basically "induction H.", it's just that Coq didn't manage to get the right IH *)
  refine ((fix ind ps1 c1 H : InferenceJustified (ps1 |- c1) :=
    match H in RulesProvePropInf _ i return InferenceJustified i with
    | proof_by_premise ps c cinp => _
    | proof_by_rule specialized ps sj mid_prems_proved => _
    end) original_ps original_c); clear original_ps original_c H ps1 c1.
  
  (* premise case *)
  constructor; unfold IntPredInfTransformJustified; intros.
  unfold RulesTransformIntPredInfs. unfold map_inf_to_coq_prop. intros.
  (* cbn in H. *)
  apply (forall_in _ H).
  assumption.
  
  (* rule case *)
  destruct specialized as (mid_prems, c).

  (* finish doing induction; this is basically just boilerplate *)
  refine (let indH : Forall (λ f, InferenceJustified (ps |- f)) mid_prems := (fix fl
      (mid_prems_part: list PropositionPreF)
      (mid_prems_proved_part: Forall (λ f : PropositionPreF,
          RulesProvePropInf
          InferenceJustified
          (ps |- f)) mid_prems_part)
      : Forall (λ f, InferenceJustified (ps |- f)) mid_prems_part
    := match mid_prems_proved_part as m in (Forall _ l) return (Forall (λ f, InferenceJustified (ps |- f)) l) with
      | Forall_nil => Forall_nil _
      | Forall_cons head tail head_proof tail_proof => _
         Forall_cons (ind ps head head_proof) (fl tail tail_proof)
      end) mid_prems mid_prems_proved in _).
  clearbody indH.
  clear ind mid_prems_proved.

  (* Now back to the real proof logic for the "rule" case *)
  (* destruct H. *)
  apply inference_justified.
  unfold IntPredInfTransformJustified in *; intros.
  (* specialize H with InferenceJustified.  *)
  unfold RulesTransformIntPredInfs in *.
  unfold map_inf_to_coq_prop in *; intros; cbn in *.
  (* unfold RulesProveIntPredInf in *. *)
  cbn in *.
  destruct pred_infs; cbn in *.
  intros.

  apply H.

  specialize H with H0.

  split 
  
  destruct H.

  
  
Lemma justified_to_any : 
Lemma justified_to_any : 
  ∀ metainf, 
    RulesProveDoublePredInf Justified metainf
    ->
    (∀Rules, RulesProveDoublePredInf Rules metainf).
  unfold RulesProveDoublePredInf in *.
  unfold map_inf_to_coq_prop in *.
  intros.
  specialize (H y).
  

Theorem justified_rules_make_justified_proofs :
  ∀ metainf,
    ((∀ y, (map_inf_to_coq_prop
      (λ i, RulesProvePredInf Justified (specialize_inf i y))
      metainf))
    ->
    Justified (map_inf f_pred_inf metainf)).
  intros.
  apply justified.
  unfold map_inf_to_coq_prop in *.
  intros.
  specialize (H y).
  cbn in H.

  induction H.
  constructor.


Definition f_id := [fuse const const].
Definition f_fst := [fuse f_id const].
Definition f_snd := [fuse f_id [const f_id]].
Definition f_false := [pred_imp f_fst f_snd].
Definition f_true := [pred_imp [pred_imp pred_imp] [pred_imp pred_imp]].

Theorem ic_is_consistent : (∀ i, RulesProve Justified (nil |- i)) -> False.
  intro.
  specialize H with (i := f_false).
  dependent induction H.

  (* "Can't be a premise, because there are none" *)
  unfold In in H; assumption.
  
  (* "How was the rule justified?" *)
  destruct H.

  destruct H0.

  cbv in H.


  
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
    Forall2 (λ rule_p p, Unfold (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    Unfold (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).