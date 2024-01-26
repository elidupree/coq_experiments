Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Coq.Program.Equality.

(* Parameter Ext : Set. *)
Inductive Atom :=
  | atom_const
  | atom_fuse
  | atom_implies
  | atom_and
  | atom_forall_valid_propositions
  | atom_forall_quoted_formulas
  | atom_quote
  (* | atom_extra : Ext -> Atom *)
  .

Inductive Formula {Ext} :=
  | f_atm : Atom -> Formula
  | f_ext : Ext -> Formula
  | f_apl : Formula -> Formula -> Formula.

Notation "[ x y .. z ]" := (f_apl .. (f_apl x y) .. z)
 (at level 0, x at next level, y at next level).

Definition const {Ext} := @f_atm Ext atom_const.
Definition fuse {Ext} := @f_atm Ext atom_fuse.
Definition f_implies {Ext} := @f_atm Ext atom_implies.
Definition f_and {Ext} := @f_atm Ext atom_and.
Definition f_forall_valid_propositions {Ext} := @f_atm Ext atom_forall_valid_propositions.
Definition f_forall_quoted_formulas {Ext} := @f_atm Ext atom_forall_quoted_formulas.
Definition f_quote {Ext} := @f_atm Ext atom_quote.
Definition f_id {Ext} : @Formula Ext := [fuse const const].
(* Definition f_extra e := f_atm (atom_extra e). *)
Definition f_pair [Ext] a b : @Formula Ext := [fuse [fuse f_id [const a]] [const b]].
Definition fp_fst {Ext} : @Formula Ext := [fuse f_id [const const]].
Definition fp_snd {Ext} : @Formula Ext := [fuse f_id [const f_id]].
Definition f_default {Ext} : @Formula Ext := const.

Notation "[ x & y ]" := [f_and x y] (at level 0, x at next level, y at next level).
(* Notation "[ x &* y ]" := [fuse [fuse [const [f_quote [f_quote f_and]]] x] y] (at level 0, x at next level, y at next level). *)
Notation "[ x -> y ]" := [f_implies x y] (at level 0, x at next level, y at next level).

(* subset notation is used for InfSets (which are 2-way relations) *)
Notation "R ⊆ S" := (∀ x, R x -> S x) (at level 70).
Notation "R ⊆2 S" := (∀ x y, R x y -> S x y) (at level 70).
Notation "R ⊇ S" := (∀ x, S x -> R x) (at level 70).
Notation "R ⊇2 S" := (∀ x y, S x y -> R x y) (at level 70).
Notation "R <->2 S" := (∀ x y, S x y <-> R x y) (at level 70).
Notation "R ∧1 S" := (λ x, R x ∧ S x) (at level 70).
Notation "R ∪ S" := (λ x, R x \/ S x) (at level 70).
Notation "R ∪2 S" := (λ x y, R x y \/ S x y) (at level 70).
(* Notation "⋃ S" := (λ x, ∃ T, S T /\ T x) (at level 70).
Notation "⋂ S" := (λ x, ∀ T, S T -> T x) (at level 70).
Notation "⋃2 S" := (λ x y, ∃ T, S T /\ T x y) (at level 70).
Notation "⋂2 S" := (λ x y, ∀ T, S T -> T x y) (at level 70). *)
(* Notation "⋀ S" := (λ x, ∀ T, (S T) x) (at level 70). *)
Notation "∅" := (λ x, False) (at level 70).
Notation "∅2" := (λ x y, False) (at level 70).
Definition Singleton A (a:A) := λ x, x = a.
Definition Singleton2 A B (a:A) (b:B) := λ x y, x = a /\ y = b.
(* Inductive Singleton2 A B (a:A) (b:B) : A -> B -> Prop :=
  | singleton2_cons x y : Singleton2 a b x y. *)

Definition StandardFormula := @Formula False.

Definition InfSet :=
  StandardFormula -> StandardFormula -> Prop.

Definition Rule := InfSet -> Prop.

Definition Meanings {Ext} :=
  (@Formula Ext) -> Rule -> Prop.

Inductive UnfoldStep [Ext] : (@Formula Ext) -> (@Formula Ext) -> Prop :=
  | unfold_const a b : UnfoldStep [const a b] a
  | unfold_fuse a b c : UnfoldStep [fuse a b c] [[a c] [b c]]
  | unfold_in_lhs a b c : UnfoldStep a b -> UnfoldStep [a c] [b c].
(* 
Definition QuotedJudgment qf := StandardFormula -> Prop *)

Inductive MeansQuoted [Ext]
    (* (Ext -> StandardFormula -> Prop) *)
    : (@Formula Ext) -> StandardFormula -> Prop :=
  | quoted_atom a : MeansQuoted [f_quote (f_atm a)] (f_atm a)
  | quoted_apply qa a qb b :
    MeansQuoted qa a -> MeansQuoted qb b ->
    MeansQuoted [f_quote qa qb] [a b]
  | quoted_unfold qa qb b :
      UnfoldStep qa qb ->
      MeansQuoted qb b ->
      MeansQuoted qa b.

Inductive MeansProp [Ext]
    (assumed_meanings : @Meanings Ext) : @Meanings Ext :=
  | mi_assumed a A :
      assumed_meanings a A ->
      MeansProp assumed_meanings a A
  | mi_implies qp p qc c :
      MeansQuoted qp p -> MeansQuoted qc c -> 
      MeansProp assumed_meanings [qp -> qc] (λ infs, infs p c)
  | mi_unfold a b B :
      UnfoldStep a b ->
      MeansProp assumed_meanings b B ->
      MeansProp assumed_meanings a B
  | mi_and a A b B :
      MeansProp assumed_meanings a A ->
      MeansProp assumed_meanings b B ->
      MeansProp assumed_meanings [a & b] (A ∧1 B)
  | mi_forall_valid_propositions f F :
    (∀ x X,
      MeansProp
        (assumed_meanings ∪2 (Singleton2 x X))
        [f x]
        (F X)
    ) ->
    MeansProp
      assumed_meanings
      [f_forall_valid_propositions f]
      (λ infs, ∀ X, (F X) infs)
  | mi_forall_quoted_formulas f F :
    (∀ x qx,
      MeansQuoted qx x -> 
      MeansProp assumed_meanings [f qx] (F x)
    ) -> 
    MeansProp
      assumed_meanings
      [f_forall_quoted_formulas f]
      (λ infs, ∀ x, (F x) infs).


(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
Definition MetaInferences
  KnownRules
  (p c : StandardFormula) : Prop :=
  ∀ P, MeansProp (∅2) p P -> 
    ∃ C, MeansProp (∅2) c C ∧
      ∀ infs, KnownRules infs -> P infs -> C infs.

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
Fixpoint KnownInferences n : InfSet :=
  match n with
    | 0 => ∅2
    | S pred => MetaInferences (λ infs, infs ⊇2 KnownInferences pred)
    end.




Fixpoint embed_formula
  Ext1 Ext2 (embed : Ext1 -> Ext2)
  (f : (@Formula Ext1)) : (@Formula Ext2)
  := match f with
    | f_atm a => f_atm a
    | f_ext a => f_ext (embed a)
    | f_apl a b => [(embed_formula embed a) (embed_formula embed b)]
    end.


Fixpoint unfold_step_result [Ext] f : option (@Formula Ext) :=
  match f with
    (* Atoms never unfold *)
    | f_atm _ => None
    | f_ext _ => None
    (* Unfold in the LHS until you're done... *)
    | f_apl f x => match unfold_step_result f with
      | Some g => Some [g x]
      (* Then if you're done with the LHS, check its form... *)
      | None => match f with
        | f_apl (f_atm atom_const) a =>
            Some a
        | f_apl (f_apl (f_atm atom_fuse) a) b =>
            Some [[a x] [b x]]
        | _ => None
        end
      end
    end.
Fixpoint unfold_step [Ext] f : option {g : (@Formula Ext) | UnfoldStep f g} :=
  match f with
    (* Atoms never unfold *)
    | f_atm _ => None
    | f_ext _ => None
    (* Unfold in the LHS until you're done... *)
    | f_apl f x => match unfold_step f with
      | Some (exist g u) => Some (exist _ [g x] (unfold_in_lhs x u)) 
      (* Then if you're done with the LHS, check its form... *)
      | None => match f with
        | f_apl (f_atm atom_const) a =>
            Some (exist _ a (unfold_const a x))
        | f_apl (f_apl (f_atm atom_fuse) a) b =>
            Some (exist _ [[a x] [b x]] (unfold_fuse a b x))
        | _ => None
        end
      end
    end.
  




Inductive GetResult t :=
  | success : t -> GetResult t
  | timed_out : GetResult t
  | error : GetResult t.

Notation "? x <- m1 ; m2" :=
  (match m1 with
    | success (x) => m2
    | timed_out => timed_out _
    | error => error _
    end) (right associativity, at level 70, x pattern).

(* Fixpoint unfold_until (t : Type) n
  (body : (Formula -> GetResult t) -> Formula -> GetResult t)
  : (Formula -> GetResult t) :=
  match n with
    | 0 => timed_out _
    | S pred => body (unfold_until pred body) f
    end.
Notation "'unfold_or' body" :=
  (match n with
    | 0 => timed_out _ | S pred => body end) (at level 40). *)


Print MeansProp.
(* Definition Meaning : Meanings := MeansProp (∅2). *)

Inductive OneMoreAtom {OldExt} :=
  | onemore_old : OldExt -> OneMoreAtom
  | onemore_new : OneMoreAtom.

Fixpoint embed_onemore OldExt
  (f : @Formula OldExt)
  : @Formula (@OneMoreAtom OldExt) :=
  match f with
    | f_apl a b => [(embed_onemore a) (embed_onemore b)] 
    | f_atm a => f_atm a
    | f_ext a => f_ext (onemore_old a)
    end.


Fixpoint specialize_onemore OldExt
  (f : @Formula (@OneMoreAtom OldExt))
  (x : @Formula OldExt)
  : @Formula OldExt :=
  match f with
    | f_apl a b => [(specialize_onemore a x) (specialize_onemore b x)] 
    | f_atm a => f_atm a
    | f_ext a => match a with
        | onemore_old a => f_ext a
        | onemore_new => x
      end
    end.

Lemma specialize_embed [OldExt] (f: @Formula OldExt) x :
  specialize_onemore (embed_onemore f) x = f.
  induction f; cbn; [| |rewrite IHf1; rewrite IHf2]; reflexivity.
Qed.

Inductive UnreifiedAssumed [Ext]
  (propvars : Ext -> Prop)
  (pv_meanings : ∀ e, propvars e -> Rule)
  : Meanings :=
  | unreified_assumed e (ae : propvars e) :
  UnreifiedAssumed propvars pv_meanings
    (f_ext e) (pv_meanings e ae).
        
Definition MiSearchResult [Ext]
    (quotvars : Ext -> Prop)
    (propvars : Ext -> Prop)
    (f : @Formula Ext) : Type :=
    ∀ (qv_meanings : ∀ e, quotvars e -> StandardFormula)
      (pv_meanings : ∀ e, propvars e -> Rule),
    Rule.
Definition MiSearchSuccess [Ext]
    (quotvars : Ext -> Prop)
    (propvars : Ext -> Prop)
    (f : @Formula Ext) : Type :=
    ∀ (qv_meanings : ∀ e, quotvars e -> StandardFormula)
      (pv_meanings : ∀ e, propvars e -> Rule),
    {F | MeansProp
      (UnreifiedAssumed propvars pv_meanings)
      f F}.

Definition embed_assumed 
    [OldExt]
    (assumed_meanings : @Meanings OldExt)
    : @Meanings (@OneMoreAtom OldExt) :=
  λ f F, (∃ fp, f = embed_onemore fp /\ assumed_meanings fp F).

Definition assume_one_more
    [OldExt]
    (assumed_meanings : @Meanings OldExt)
    (new_meaning : Rule)
    : @Meanings (@OneMoreAtom OldExt) :=
  (embed_assumed assumed_meanings) ∪2 (Singleton2 (f_ext (onemore_new)) new_meaning).

Definition one_more_var
    [OldExt]
    (vars : OldExt -> Prop)
    : (@OneMoreAtom OldExt) -> Prop :=
  λ a, match a with
    | onemore_old a => vars a
    | onemore_new => True 
    end.
Definition embed_vars
    [OldExt]
    (vars : OldExt -> Prop)
    : (@OneMoreAtom OldExt) -> Prop :=
  λ a, match a with
    | onemore_old a => vars a
    | onemore_new => False
    end.
Definition one_more_revar
    [OldExt]
    (vars : OldExt -> bool)
    : (@OneMoreAtom OldExt) -> bool :=
  λ a, match a with
    | onemore_old a => vars a
    | onemore_new => true 
    end.
Definition embed_revars
    [OldExt]
    (vars : OldExt -> bool)
    : (@OneMoreAtom OldExt) -> bool :=
  λ a, match a with
    | onemore_old a => vars a
    | onemore_new => false
    end.

Definition one_more_var_meaning
    [OldExt]
    [VarType]
    (vars : OldExt -> Prop)
    (meanings : ∀ e, vars e -> VarType)
    (new_meaning : VarType)
    : (∀ e, (one_more_var vars) e -> VarType) :=
  λ e, match e return (one_more_var vars) e -> VarType with
    | onemore_old a => meanings a
    | onemore_new => λ _, new_meaning
    end.
Definition embed_var_meanings
    [OldExt]
    [VarType]
    (vars : OldExt -> Prop)
    (meanings : ∀ e, vars e -> VarType)
    : (∀ e, (embed_vars vars) e -> VarType) :=
  λ e, match e return (embed_vars vars) e -> VarType with
    | onemore_old a => meanings a
    | onemore_new => λ f, match f with end
    end.


Lemma qf_convert [Ext1 Ext2]
  (qf : @Formula Ext1) f :
  MeansQuoted qf f -> {qf2 : @Formula Ext2 | MeansQuoted qf2 f}.
  (* "qf can't have f_ext anywhere in it" *)
  admit.

  (* intros. dependent induction qf.

  apply exist with (f_atm a).
  dependent induction H. apply IHMeansQuoted. dependent induction H.
  
  exfalso.
  dependent induction H. apply IHMeansQuoted with e. dependent induction H.

  dependent induction f.
  apply exist with [f_quote (f_atm a)]. constructor.

  exfalso. dependent induction H.
  (* ugh now I have to convince Coq that you can't unfold to a quoted f_ext? *)
  admit.

  specialize (IHf1 H).

  apply quoted_apply.
  dependent induction H.
  specialize IHqf1 with  *)
Qed.

Lemma mi_monotonic [Ext]
  (assumed1 : @Meanings Ext)
  (assumed2 : @Meanings Ext)
  : (assumed1 ⊆2 assumed2) ->
  (MeansProp assumed1 ⊆2 MeansProp assumed2).
  intros a1_a2 f F mf.

  refine ((fix recurse 
    Ext (assumed1 : @Meanings Ext) assumed2 a1_a2 f F mf
      {struct mf}
      : MeansProp assumed2 f F
    := match mf
        in MeansProp _ f F
        return MeansProp assumed2 f F
        with
    | mi_assumed a A aAassumed => _
    | mi_implies qp p qc c x y => _
    | mi_unfold a b B unf bBimp => _
    | mi_and a A b B aAimp bBimp => _
    | mi_forall_valid_propositions f F fxFXimp => _
    | mi_forall_quoted_formulas f F fxFXimp => _
    end) Ext assumed1 assumed2 a1_a2 f F mf);
      [refine ?[assumed] | refine ?[implies] |
        refine ?[unfold] | refine ?[and] |
        refine ?[forall_prop] | refine ?[forall_quote]];
      clear assumed3 assumed4 f0 F0 a1_a3 mf0.

  [assumed]: { apply mi_assumed. apply a1_a2; assumption. }
  [implies]: { apply mi_implies; assumption. }
  [unfold]: {
    apply mi_unfold with b.
    assumption. apply recurse with assumed1; assumption.
  }
  [and]: {
    apply mi_and; apply recurse with assumed1; assumption.
  }
  [forall_prop]: {
    apply mi_forall_valid_propositions.
    intros.
    specialize (fxFXimp x X).
    apply recurse with (assumed1 ∪2 Singleton2 x X).
    intuition. assumption.
  }
  [forall_quote]: {
    apply mi_forall_quoted_formulas.
    intros.
    specialize (fxFXimp x qx H).
    apply recurse with assumed1; assumption.
  }
Qed.
    
  

Lemma specialize_MeansProp [OldExt] 
    (assumed_meanings : @Meanings OldExt) f F x X :
  MeansProp (assume_one_more assumed_meanings X) f F ->
  MeansProp assumed_meanings x X ->
  MeansProp assumed_meanings (specialize_onemore f x) F.

  intros.

  refine ((fix recurse 
    OldExt (assumed_meanings : @Meanings OldExt) f F x X mf mx
      : MeansProp assumed_meanings
        (specialize_onemore f x) F
    := match mf
        in MeansProp _ f F
        return MeansProp assumed_meanings
    (specialize_onemore f x) F
        with
    | mi_assumed a A aAassumed => _
    | mi_implies qp p qc c x y => _
    | mi_unfold a b B unf bBimp => _
    | mi_and a A b B aAimp bBimp => _
    | mi_forall_valid_propositions f F fxFXimp => _
    | mi_forall_quoted_formulas f F fxFXimp => _
    end) OldExt assumed_meanings f F x X H H0);
      [refine ?[assumed] | refine ?[implies] |
        refine ?[unfold] | refine ?[and] |
        refine ?[forall_prop] | refine ?[forall_quote]];
      clear OldExt0 assumed_meanings0 f0 F0 x0 X0 H H0 mf.

  [assumed] : {
    dependent destruction aAassumed. destruct H.
    
    destruct H. rewrite H.
    rewrite (specialize_embed x0 x).
    apply mi_assumed; assumption.
    
    destruct H. rewrite H. rewrite H0. cbn. assumption.
  }

  [implies] : {
    (* TODO: "quoted formulas should still work because they can't have f_ext in them?" *)
    admit.
  }

  [unfold] : {
    apply mi_unfold with (specialize_onemore b x).

    (* TODO: unfold-specialize lemma *)
    admit.

    apply recurse with X; assumption.
  }

  [and] : {
    apply mi_and; apply recurse with X; assumption.
  }

  [forall_prop] : {
    apply mi_forall_valid_propositions.
    intros y Y.
    specialize (fxFXimp (embed_onemore y) Y).
    specialize (recurse
      OldExt
      (assumed_meanings ∪2 Singleton2 y Y)
      ([f (embed_onemore y)])
      (F Y)
      x
      X
   ).
  assert ([(specialize_onemore f x) y] =
    (specialize_onemore [f (embed_onemore y)] x)).
    cbn.
    rewrite (specialize_embed y x). reflexivity.
    rewrite <- H in recurse.
    apply recurse.
    apply mi_monotonic with  (assume_one_more assumed_meanings X
∪2 Singleton2 (embed_onemore
  y)
  Y); [|assumption].
  intuition idtac; unfold assume_one_more, embed_assumed in *; cbn in *;intuition idtac.
  apply or_introl. destruct H0. apply ex_intro with x1; intuition idtac.
  destruct H1. rewrite H0. rewrite H1.
  apply or_introl. apply ex_intro with y. intuition idtac. apply or_intror. unfold Singleton2. intuition idtac.
  apply mi_monotonic with assumed_meanings; [| assumption].
  intuition idtac.
  }

  [forall_quote] : {
    apply mi_forall_quoted_formulas.
    intros y qy qqy.
    destruct (qf_convert (Ext2:=(@OneMoreAtom OldExt)) qqy) as [qy_ qqy_].
    specialize (fxFXimp y qy_ qqy_).
    specialize (recurse
      OldExt
      assumed_meanings
      ([f qy_])
      (F y)
      x
      X
   ).
  assert ([(specialize_onemore f x) qy] =
    (specialize_onemore [f qy_] x)).
    cbn.
    (* TODO: quoted version of the same formula are basically the same *)
    admit.
    rewrite <- H in recurse.
    apply recurse; assumption.
  }
Qed.
  

Definition specialize_MiSearchSuccess_prop
    [OldExt] f
    (quotvars : OldExt -> Prop)
    (propvars : OldExt -> Prop)
    (x : @Formula OldExt)
    (X : Rule)
    (xXimp : ∀ pv_meanings, MeansProp (UnreifiedAssumed
  propvars pv_meanings) x X)
    (missss : MiSearchSuccess
      (embed_vars quotvars) (one_more_var propvars)
      f)
    :
    (MiSearchSuccess quotvars propvars
      (specialize_onemore f x)).
  refine (
    λ qv_meanings pv_meanings,
       match (missss
         (embed_var_meanings quotvars qv_meanings)
         (one_more_var_meaning propvars pv_meanings X)
         ) with
       exist F p => 
        exist _ F _ end).
  
  apply specialize_MeansProp with X.
  apply mi_monotonic with (UnreifiedAssumed
  (one_more_var propvars)
  (one_more_var_meaning propvars
  pv_meanings X)).
  intros.
  destruct H.
  unfold assume_one_more, embed_assumed.
  destruct e.
  apply or_introl. apply ex_intro with (f_ext o). constructor.
  reflexivity.
  constructor. apply or_intror. constructor; trivial.
  assumption.
  apply xXimp.
Qed.


Definition unreify_vars  [Ext]
  (propvars : Ext -> bool)
  :Ext -> Prop :=
  λ e, true = (propvars e).

Definition embed_revar_meanings
    [OldExt]
    [VarType]
    (vars : OldExt -> bool)
    (meanings : ∀ e, (unreify_vars vars e) -> VarType)
    : (∀ e, (unreify_vars (embed_revars vars)) e -> VarType) :=
  λ e, match e with
    | onemore_old a => meanings a
    | onemore_new => λ f, match f with end
    end.
Definition one_more_revar_meaning
    [OldExt]
    [VarType]
    (vars : OldExt -> bool)
    (meanings : ∀ e, (unreify_vars vars e) -> VarType)
    (new_meaning : VarType)
    : (∀ e, (unreify_vars (one_more_revar vars) e) -> VarType) :=
  λ e, match e with
    | onemore_old a => meanings a
    | onemore_new => λ _, new_meaning
    end.

Lemma unreify_embed1 [Ext] (vars : Ext -> bool) e :
  unreify_vars (embed_revars vars) e ->
  embed_vars (unreify_vars vars) e.
  unfold unreify_vars, embed_vars, embed_revars.
  intros. destruct e.
  assumption. dependent destruction H.
Defined.  

Lemma unreify_embed2 [Ext] R (vars : Ext -> bool) :
  (∀ e, embed_vars (unreify_vars vars) e -> R) ->
  (∀ e, unreify_vars (embed_revars vars) e -> R).
  unfold unreify_vars, embed_vars, embed_revars.
  intros.
  specialize (X e).
  exact (X (unreify_embed1 H)).
Defined.  

Lemma unreify_onemore1 [Ext] (vars : Ext -> bool) e :
  unreify_vars (one_more_revar vars) e ->
  one_more_var (unreify_vars vars) e.
  unfold unreify_vars, embed_vars, embed_revars.
  intros. destruct e.
  assumption.
  cbn. trivial.
  Show Proof.
Qed. 

Lemma unreify_onemore2 [Ext] R (vars : Ext -> bool) :
  (∀ e, one_more_var (unreify_vars vars) e -> R) ->
  (∀ e, unreify_vars (one_more_revar vars) e -> R).
  unfold unreify_vars, embed_vars, embed_revars.
  intros.
  specialize (X e).
  exact (X (unreify_onemore1 H)).
  Show Proof.
Defined.  

Definition QfResult [Ext] (quotvars : Ext -> bool) :=
  (∀ qv_meanings : 
    (∀ e, (unreify_vars quotvars) e -> StandardFormula),
    StandardFormula).

Fixpoint get_quoted_formula [Ext]
  (quotvars : Ext -> bool) n qf
  : GetResult (QfResult quotvars) :=
  match n with 0 => timed_out _ | S pred =>
    match unfold_step_result (Ext:=Ext) qf with
      | Some qg => get_quoted_formula quotvars pred qg
      | None => match qf with
          | f_apl (f_atm atom_quote) (f_atm a) =>
              success (λ _, (f_atm a))
          | f_apl (f_apl (f_atm atom_quote) qa) qb =>
            ? a <- get_quoted_formula quotvars pred qa ; 
            ? b <- get_quoted_formula quotvars pred qb ;
            success (λ qv_meanings, [(a qv_meanings) (b qv_meanings)])
          | f_ext e => match quotvars e as qe
            return qe = quotvars e -> GetResult (QfResult quotvars) with
            | true => λ eq, success (λ qv_meanings, qv_meanings e eq)
            | false => λ _, error _
            end eq_refl
          | _ => error _
          end
      end
  end.

Fixpoint get_MeansQuoted [Ext] n qf
  : GetResult {f : StandardFormula | MeansQuoted qf f} :=
  match n with 0 => timed_out _ | S pred =>
    match unfold_step qf with
      | Some (exist qg u) =>
          ? (exist g gp) <- get_MeansQuoted pred qg ;
          success (exist _ g (quoted_unfold u gp))
      | None => match qf with
          | f_apl (f_atm atom_quote) (f_atm a) =>
              success (exist _ (f_atm a) (quoted_atom a))
          | f_apl (f_apl (f_atm atom_quote) qa) qb =>
            ? (exist a ap) <- get_MeansQuoted pred qa ; 
            ? (exist b bp) <- get_MeansQuoted pred qb ;
            success (exist _ [a b] (quoted_apply (Ext:=Ext) ap bp))
          | _ => error _
          end
      end
  end.
Eval cbv beta iota delta -[embed_onemore embed_vars embed_revars] in
  ( λ quotvars qv_meanings, unreify_embed2 (embed_var_meanings
                    (unreify_vars quotvars) qv_meanings)).
Fixpoint get_prop_meaning (n:nat) [Ext]
  (f : @Formula Ext)
  (quotvars : Ext -> bool)
  (propvars : Ext -> bool)
  : GetResult (MiSearchResult
    (unreify_vars quotvars) (unreify_vars propvars) f) :=
  match n with 0 => timed_out _ | S pred =>
    match unfold_step_result f with
      | Some g => get_prop_meaning pred g quotvars propvars
      | None => match f with
        | f_ext a => match propvars a as pa return
          (pa = propvars a) -> GetResult
  (MiSearchResult (unreify_vars quotvars)
  (unreify_vars propvars) f) with
              | true => λ eq, success (λ qv_meanings pv_meanings,
                 pv_meanings a eq)
              | false => λ _ , error _
              end eq_refl
        | f_apl (f_apl (f_atm atom_implies) qp) qc =>
          ? p <- (get_quoted_formula quotvars pred qp) ;
          ? c <- (get_quoted_formula quotvars pred qc) ;
          success (λ qv_meanings _,
            (Singleton2 (p qv_meanings) (c qv_meanings)))
             
        (* 
    refine (? PQ <- (get_MeansQuoted pred qp) ; _).
    refine (? CQ <- (get_MeansQuoted pred qc) ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct PQ as (p, qqp).
    destruct CQ as (c, qqc).
    apply exist with (Singleton2 p c). *)
        | f_apl (f_apl (f_atm atom_and) a) b =>
          ? A <- (get_prop_meaning pred a quotvars propvars) ;
          ? B <- (get_prop_meaning pred b quotvars propvars) ;
          success (λ qv_meanings pv_meanings,
            ((A qv_meanings pv_meanings) ∪2 (B qv_meanings pv_meanings)))
        | f_apl (f_atm atom_forall_valid_propositions) f =>
          ? FX <- (get_prop_meaning pred
              [(embed_formula (λ a, onemore_old a) f)
                  (f_ext onemore_new)]
                  (embed_revars quotvars)
                  (one_more_revar propvars)) ; 
            success (λ qv_meanings pv_meanings,
              (λ p c, ∃ X : Rule,
                 FX
                 (embed_revar_meanings qv_meanings)
                 (one_more_revar_meaning pv_meanings X)
                 (* (unreify_embed2 (embed_var_meanings
                    (unreify_vars quotvars) qv_meanings)) *)
                (* (unreify_onemore2 (one_more_var_meaning
                    (unreify_vars propvars) pv_meanings X)) *)
                p c
                ))
        | f_apl (f_atm atom_forall_quoted_formulas) f =>
          ? Fx <- (get_prop_meaning pred
              [(embed_formula (λ a, onemore_old a) f)
                  (f_ext onemore_new)]
                  (one_more_revar quotvars)
                  (embed_revars propvars)) ; 
            success (λ qv_meanings pv_meanings,
              (λ p c, ∃ x : StandardFormula,
                 Fx
                 (one_more_revar_meaning qv_meanings x)
                 (embed_revar_meanings pv_meanings)
                 (* (unreify_onemore2 (one_more_var_meaning
                    (unreify_vars quotvars) qv_meanings x))
                (unreify_embed2 (embed_var_meanings
                    (unreify_vars propvars) pv_meanings)) *)
                p c
                ))
        | _ => error _
      end
    end
  end.

  



Definition get_MeansProp (n:nat) [Ext]
  (f : @Formula Ext)
  (quotvars : Ext -> bool)
  (propvars : Ext -> bool)
  : GetResult (MiSearchSuccess
    (unreify_vars quotvars) (unreify_vars propvars) f).
  refine ((fix get_MeansProp Ext
    n f quotvars propvars :=
    match n with 0 => timed_out _ | S pred => _ end) Ext n f quotvars propvars)
    ; clear Ext0 n0 f0 quotvars0 propvars0.
  specialize get_MeansProp with (n := pred).
  
  (* pose (λ pv_meanings, (UnreifiedAssumed (unreify_vars propvars) pv_meanings)) as assumed_meanings. *)

  destruct (unfold_step f) as [(g, unf)|].
  {
    refine (? GS <- get_MeansProp Ext g quotvars propvars ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct (GS qv_meanings pv_meanings) as (G, Gp).
    apply (exist _ G (mi_unfold unf Gp)).
  }

  refine (match f with
          | f_ext a => _
          | f_apl (f_atm atom_forall_valid_propositions) f => _
          | f_apl (f_atm atom_forall_quoted_formulas) f => _
          | f_apl (f_apl (f_atm atom_implies) qp) qc => _
          | f_apl (f_apl (f_atm atom_and) a) b => _
          | _ => error _
          end);
      [refine ?[assumed] |
        refine ?[forall_prop] | refine ?[forall_quote] |
        refine ?[implies] | refine ?[and]].
  
  [assumed]: {
    refine (match propvars a with
              | true => success (λ qv_meanings pv_meanings, _)
              | false => error _
              end).

    (* TODO: sigh, Coq forgot that we're
       in the (propvars a)=true case *)
    assert (unreify_vars propvars a) as pa; [admit|].

    apply exist with (pv_meanings a pa).
    apply mi_assumed.
    apply unreified_assumed.
  }

  [forall_prop]: {
    refine (? FXS <- (get_MeansProp (@OneMoreAtom Ext)
      [(embed_formula (λ a, onemore_old a) f) (f_ext onemore_new)]
      (embed_revars quotvars)
      (one_more_revar propvars)) ; _).
    apply success; intros qv_meanings pv_meanings.
    refine (exist _ (λ p c, ∃ X : Rule, (_ X) p c) _).
    Unshelve. 2: {
      (* TODO reduce duplicate code ID 23489305 *)
      pose (unreify_embed2 (embed_var_meanings
        (unreify_vars quotvars) qv_meanings)) as qv_meanings1.
      pose (unreify_onemore2 (one_more_var_meaning
        (unreify_vars propvars) pv_meanings X)) as pv_meanings1.
      destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
      (* End duplicate code *)
      exact (λ _, FX).
    }

    apply mi_forall_valid_propositions.
    intros.

    (* TODO reduce duplicate code ID 23489305 *)
    pose (unreify_embed2 (embed_var_meanings
      (unreify_vars quotvars) qv_meanings)) as qv_meanings1.
    pose (unreify_onemore2 (one_more_var_meaning
      (unreify_vars propvars) pv_meanings X)) as pv_meanings1.
    destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
    (* End duplicate code *)
    admit.
    (* pose (@specialize_MeansProp
      Ext
      (assumed_meanings pv_meanings)
      [(embed_formula onemore_old f) (f_ext onemore_new)]
      FX
      x
      X
      ) as m.
    apply mi_monotonic with (assumed2 := assume_one_more
  (assumed_meanings
  pv_meanings)
  X) in FXp. 2: {
      clear m.
      intros. destruct H. unfold assume_one_more. cbn.
      dependent destruction e.
      apply or_introl. unfold unreify_vars in ae.
      cbn.
      apply ex_intro with (f_ext e).
      constructor; [reflexivity|].
      (* unfold meanings1  .  *)
      admit.
      apply or_intror.
      admit.
    }
    specialize (m FXp). *)
  }

  [forall_quote]: {
    refine (? FXS <- (get_MeansProp (@OneMoreAtom Ext)
      [(embed_formula (λ a, onemore_old a) f) (f_ext onemore_new)]
      (one_more_revar quotvars)
      (embed_revars propvars)) ; _).
    apply success; intros qv_meanings pv_meanings.
    refine (exist _ (λ p c, ∃ x : StandardFormula, (_ x) p c) _).

    Unshelve. 2: {
      (* TODO reduce duplicate code ID 23489305 *)
      pose (unreify_embed2 (embed_var_meanings
        (unreify_vars propvars) pv_meanings)) as pv_meanings1.
      pose (unreify_onemore2 (one_more_var_meaning
        (unreify_vars quotvars) qv_meanings x)) as qv_meanings1.
      destruct (FXS qv_meanings1 pv_meanings1) as (FX, FXp).
      (* End duplicate code *)
      exact (λ _, FX).
    }

    admit.
  }

  [implies]: {
    refine (? PQ <- (get_MeansQuoted pred qp) ; _).
    refine (? CQ <- (get_MeansQuoted pred qc) ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct PQ as (p, qqp).
    destruct CQ as (c, qqc).
    apply exist with (Singleton2 p c).
    apply mi_implies; assumption.
  }

  [and]: {
    refine (? AS <- (get_MeansProp Ext a quotvars propvars) ; _).
    refine (? BS <- (get_MeansProp Ext b quotvars propvars) ; _).
    apply success; intros qv_meanings pv_meanings.
    destruct (AS qv_meanings pv_meanings) as (A, Ap).
    destruct (BS qv_meanings pv_meanings) as (B, Bp).
    apply exist with (A ∪2 B).
    apply mi_and; assumption.
  }
Defined.

Eval lazy in 2 + 2.
Eval lazy in get_MeansProp (Ext := False) 0 [[f_quote f_quote] -> [f_quote f_quote]] 
  (λ _, false) (λ _, false)
  .
Lemma uhh : False.
  pose (get_MeansProp (Ext := False) 0 [[f_quote f_quote] -> [f_quote f_quote]] 
  (λ _, false) (λ _, false)) as x.
  cbn in x.
  unfold get_MeansProp in x.
Qed.

Fixpoint NMoreAtoms [Ext] n :=
  match n with
    | 0 => Ext
    | S n => @OneMoreAtom (@NMoreAtoms Ext n)
    end.

Fixpoint last_more_atom [Ext] n : (@NMoreAtoms Ext (S n)) :=
  match n with
    | 0 => onemore_new
    | S n => onemore_old (@last_more_atom Ext n)
    end.
  

Definition f_with_variable [n] [Ext]
  (fgen : @Formula (@NMoreAtoms Ext (S n)) ->
          @Formula (@NMoreAtoms Ext n)) : Formula :=
  (fgen (f_ext (last_more_atom n))).

Fixpoint eliminate_abstraction
  [Ext]
  (f : @Formula (@OneMoreAtom Ext))
  : @Formula Ext :=
  match f with
    | f_atm a => [const (f_atm a)]
    | f_ext e => match e with
      | onemore_new => f_id
      | onemore_old e => [const (f_ext e)]
      end
    | f_apl a b => [fuse (eliminate_abstraction a) (eliminate_abstraction b)]
    end.

Fixpoint quote_f [Ext] f : @Formula Ext :=
  match f with
    | f_atm _ => [f_quote f]
    (* assume this is a variable that represents a quoted formula: *)
    | f_ext _ => f
    | f_apl a b => [f_quote (quote_f a) (quote_f b)]
    end.

Require Import Ascii String.
Open Scope string_scope.
Inductive ParensState := ps_default | ps_apply_chain | ps_fuse_chain.
Fixpoint display_f_impl ps [Ext] (f : @Formula Ext) : string :=
  match f with
    | f_ext _ => "@"
    | f_apl (f_apl (f_atm atom_fuse)
      (f_atm atom_const))
      (f_atm atom_const) => "id"
    | f_apl (f_apl (f_atm atom_fuse) a) b => 
      let 
        b := display_f_impl ps_default b in
      let items := match a with
        | f_apl (f_atm atom_const) (f_atm atom_implies) => b ++ " ->" 
         | _ =>
         display_f_impl ps_fuse_chain a ++ " " ++ b
         end in
      match ps with
        | ps_fuse_chain => items
        | _ => "[" ++ items ++ "]"
        end
    | f_apl a b => 
      let 
        b := display_f_impl ps_default b in
      let items := match a with
        | f_atm atom_implies => b ++ " ->" 
        | _ =>
         display_f_impl ps_fuse_chain a ++ " " ++ b
         end in
      match ps with
        | ps_apply_chain => items
        | _ => "(" ++ items ++ ")"
        end
    | f_atm a => match a with
      | atom_const => "c"
      | atom_fuse => "fuse"
      | atom_implies => "implies"
      | atom_and => "and"
      | atom_forall_quoted_formulas => "∀Q"
      | atom_forall_valid_propositions => "∀P"
      | atom_quote => "quote"
      end
    end.
  
Definition display_f := display_f_impl ps_default.

Notation "[ x => y ]" :=
  (eliminate_abstraction (f_with_variable (λ x, y)))
  (at level 0, x at next level, y at next level).
  
Notation "[ ∀ x : 'P' , y ]" :=
  [f_forall_valid_propositions [x => y]]
  (at level 0, x at next level, y at next level).
Notation "[ ∀ x : 'Q' , y ]" :=
  [f_forall_quoted_formulas [x => y]]
  (at level 0, x at next level, y at next level).

(* Definition foo : StandardFormula := [x => [x & x]].
Print foo.
Eval lazy in foo.
Eval cbv beta iota delta -[f_id const fuse] in foo. *)

Definition no_vars (e:False) := false.
Definition no_meanings R (e:False) : (true = false) -> R.
  intro. dependent destruction H.
Defined.

Definition with_no_meanings
  f
  (g : GetResult (MiSearchResult
    (unreify_vars no_vars) (unreify_vars no_vars) f)) :
  GetResult Rule :=
  match g with
    | success g => success (g
        (no_meanings StandardFormula) (no_meanings Rule))
    | error => error _
    | timed_out => timed_out _
    end.

Definition test0 : StandardFormula :=
  [[f_quote const] -> [f_quote const]].
Eval compute in (with_no_meanings (get_prop_meaning 90 test0 no_vars no_vars)).

Definition test05 : StandardFormula :=
  [∀a:P, a].
Eval compute in (with_no_meanings (get_prop_meaning 90 test05 no_vars no_vars)).

Lemma uhh2 :
  success (λ p c, ∃ X : Rule, X p c)
  =
  (with_no_meanings (get_prop_meaning 90 test05 no_vars no_vars)).
  cbn.
  assert (∀ X : Rule, X = unreify_onemore2
  (one_more_var_meaning
  (unreify_vars no_vars)
  (no_meanings Rule) X)
  eq_refl).
  cbv.
Qed.


Definition simple_get_prop_meaning n f :=
  (with_no_meanings (get_prop_meaning n f no_vars no_vars)).

Definition test1 : StandardFormula :=
  [∀a:Q, [a -> a]].
Eval compute in display_f test1.
Eval compute in (simple_get_prop_meaning 90 test1).

Definition test2 : StandardFormula :=
  [∀a:Q, [∀b:Q, [a -> b]]].
Eval compute in display_f test2.
Eval lazy in (simple_get_prop_meaning 90 test2).
Definition test3 : StandardFormula :=
  [∀a:Q, [(quote_f [a const]) -> a]].
Eval compute in display_f test3.
Eval lazy in (simple_get_prop_meaning 90 test3).

(* 
  (λ (_ : False → true = false → Formula)
     (_ : False → true = false → Rule)
     (p c : Formula),
     ∃ x : Formula, p = x ∧ c = x)
 *)

Fixpoint NMore n Ext :=
  match n with
    | 0 => Ext
    | S pred => @OneMoreAtom (NMore pred Ext)
    end.

Fixpoint embed_nmore n [Ext] (f : @Formula Ext)
  : (@Formula (NMore n Ext)) :=
  match n with
    | 0 => f
    | S pred => embed_formula onemore_old (embed_nmore pred f)
    end.
Notation "$ n f" := (embed_nmore n f) (at level 0).

Definition and_sym : StandardFormula :=
  [∀a:Q, [∀b:Q,
    [(quote_f [(embed_nmore 1 a) & b])
    -> (quote_f [b & (embed_nmore 1 a)])]
  ]].
Eval compute in display_f and_sym.
(* Eval cbv beta iota delta in and_sym. *)

(* [(forall_n) p] should mean
  "put a stream of n qfs into p and it'll be true" *)
Fixpoint forall_n n :=
  match n with
    | 0 => f_id
    | S pred => [p => [(forall_n pred) [l => [∀x:Q, [p (f_pair x l)]]]]]
    end.

Definition and_sym : StandardFormula :=
  [(forall_n 2) [[@0 & @1] -> [@1 & @0]]].

Eval lazy in (simple_get_prop_meaning 90 and_sym).

(* Definition TrueOf2 Infs f : Prop :=
  InfsAssertedBy f ⊆2 Infs.

Definition FormulasTrueAbout Infs f : Prop :=
  InfsAssertedBy f ⊆2 Infs. *)

(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
Definition RequiredMetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  (* ∀ p c,
    InfsAssertedBy b p c ->
    (InfsAssertedBy a p c \/ KnownJudgedInferences p c). *)
  ∃ A B,
    InfsAssertedBy a A /\ InfsAssertedBy b B /\
    B ⊆2 (A ∪2 KnownJudgedInferences).

Definition PermittedMetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  ∀ A B,
    InfsAssertedBy a A -> InfsAssertedBy b B ->
    B ⊆2 (A ∪2 KnownJudgedInferences).

(* (want to prove: True -> required -> IC -> permitted -/> False.
    by induction: (permitted -/> False)
    somehow: "all statements that describe IC are provable in IC"
    by induction using that: (required -> IC)
    by proofs for individual rules: (IC -> permitted)
    which yields "all provable IC statements describe IC" I think) *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
Fixpoint KnownRequiredInferences n : InfSet :=
  match n with
    | 0 => ∅2
    | S pred => RequiredMetaInferences (KnownRequiredInferences pred)
    end.

Fixpoint KnownPermittedInferences n : InfSet :=
  match n with
    | 0 => ∅2
    | S pred => PermittedMetaInferences (KnownPermittedInferences pred)
    end.

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that describe the last. *)
(* Fixpoint KnownInferences n : InfSet :=
  match n with
    | 0 => eq (* same as MetaInferences (λ _, False) *)
    | S pred => MetaInferences (KnownInferences pred)
    end. *)

Inductive FType :=
  | t_proposition : FType
  | t_quoted_formula : FType
  | t_function : FType -> FType -> FType.

(* Inductive FMember (t : FType) f : Prop :=
  | tm_proposition p : (InfsAssertedBy f <->2 p) -> FMember t f
  | tm_quoted_formula : True -> FMember t f
  | tm_function a b : (∀x, FMember a x -> FMember b [f x]) -> FMember t f.
  
 
Fixpoint FMember t f : Prop := match t with
  | t_proposition => ∃ p, (InfsAssertedBy f <->2 p) -> FMember t f
  | t_quoted_formula => True
  | t_function a b => ∀x, FMember a x -> FMember b [f x]
  end. *)

Parameter FMember : FType -> Formula -> Prop.

Inductive interpret_result t f :=
  | is_member : FMember t f -> interpret_result t f
  | timed_out : interpret_result t f
  | error : interpret_result t f.

Notation "x <- m1 ; m2" :=
  (match m1 with
    | is_member x => m2
    | timed_out => timed_out
    | error => error
    end) (right associativity, at level 70).
(* Notation "x :? t ; m2" :=
  (x <- recurse t x ; m2) (right associativity, at level 70). *)

Definition interpret_as_prop recurse f :=
  match f with
    | f_apl (f_apl f_implies p) c => 
      p <- recurse t_quoted_formula p ;
      c <- recurse t_quoted_formula c ;
      is_member t_proposition (λ x y, (x = p) /\ (y = c))
    | f_apl (f_apl f_and a) b => 
      a <- recurse t_proposition a ;
      b <- recurse t_proposition b ;
      is_member t_proposition (a ∪2 b)
    | f_apl (f_all) a =>
      a <- recurse (t_function t_quoted_formula t_proposition) a ;
      is_member t_proposition (∀x, a x)
    | _ => error
  end. 
Definition interpret_as_fn recurse f :=
  match f with
  
  | _ => error
  end. 
  
    (* | _ => match
        unfold_step b
        with
      | Some b => CleanExternalMeaning pred b
      | _ => None
      end
    end *)
  

Fixpoint interpret_as n t f :=
  match n with 0 => timed_out | S pred =>
    end.


Fixpoint CleanExternalMeaning n f quoted_args : option InfSet :=
  match n with
    | 0 => None
    | S pred => match f with
      | f_apl (f_apl f_implies p) c => match (
          unquote_formula p,
          unquote_formula c
          ) with
        | (Some p, Some c) => λ x y, x = p /\ y = c
        | _ => None
      end
      | f_apl (f_apl f_and a) b => match (
          CleanExternalMeaning pred a,
          CleanExternalMeaning pred b
          ) with
        | (Some a, Some b) => Some (a ∪2 b)
        | _ => None
      end
      | f_apl (f_all) a => match
          CleanExternalMeaning pred a
          with
        | Some a => Some (∀x, a ∪2 b)
        | _ => None
      end
      | _ => match
          unfold_step b
          with
        | Some b => CleanExternalMeaning pred b
        | _ => None
        end
      end
    end.


Inductive RulesProveInference Rules : Formula -> Formula -> Prop :=
  | proof_by_rule a b : Rules a b -> RulesProveInference Rules a b
  | proof_by_transitivity a b c :
    RulesProveInference Rules a b ->
    RulesProveInference Rules b c ->
    RulesProveInference Rules a c.
Definition InferencesProvenBy Rules : InfSet := RulesProveInference Rules.

(* Definition FormulaMeaning
    (Rules : InfSet)
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
            IsMeansQuotedStream x -> ∃ ap bp,
              UnfoldsToMeansQuoted [a x] ap /\
              UnfoldsToMeansQuoted [b x] bp /\
              RulesProveInference Rules ap bp)
        | _ => UnknownMeanings f
        end. *)

(* Definition InfSetObeysInference Rules a b : Prop :=
  ∀UnknownMeanings,
    (FormulaMeaning Rules UnknownMeanings a) ->
    (FormulaMeaning Rules UnknownMeanings b).

Definition AllInfSetsObeyInference a b : Prop :=
  ∀Rules, InfSetObeysInference Rules a b. *)

(* Definition AllInfSetsObeyAllOf Rules : Prop :=
  ∀a b, Rules a b -> AllInfSetsObeyInference a b. *)

(* Definition InferencesTheseInfSetsObey These a b : Prop :=
  ∀Rules, These Rules -> InfSetObeysInference Rules a b. *)

(* Definition AllTheseInfSetsObeyAllOf These Rules : Prop :=
  ∀a b, Rules a b -> InferencesTheseInfSetsObey These a b. *)

(* Definition NoRules : InfSet := λ _ _, False. *)

(* An increasing progression of inferences that are known to be 
  required, each one adding the ones that are possible
  in all InfSets that include the last *)
(* Fixpoint KnownRequiredInferences n : InfSet :=
  match n with
    | 0 => eq
    | S pred => InferencesTheseInfSetsObey
      (λ Rules, (InferencesProvenBy Rules) ⊇2
        (KnownRequiredInferences pred))
    end. *)


Lemma CleanExternalMeaning_correct n f m :
  (CleanExternalMeaning n f = Some m) ->
  (m <->2 InfsAssertedBy f).

Lemma MetaInferences_closed_under_transitivity K p c :
    RulesProveInference (MetaInferences K) p c
    ->
    (MetaInferences K) p c.
  intro.
  induction H; [assumption|clear H H0].
  unfold MetaInferences in *.
  intros.
  specialize (IHRulesProveInference1 x y).
  specialize (IHRulesProveInference2 x y).
  destruct (IHRulesProveInference2 H); [|constructor; assumption].
  destruct (IHRulesProveInference1 H0); constructor; assumption.
Qed.

Lemma emptyset_closed_under_transitivity p c :
    RulesProveInference (∅2) p c
    ->
    ∅2 p c.
  intro. induction H; assumption.
Qed.

Lemma KnownInferences_closed_under_transitivity p c n :
    RulesProveInference (KnownInferences n) p c
    ->
    KnownInferences n p c.
    destruct n.
    apply emptyset_closed_under_transitivity.
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

(* Lemma eq_justified These : AllTheseInfSetsObeyAllOf These eq.
  unfold AllTheseInfSetsObeyAllOf,
         InferencesTheseInfSetsObey,
         InfSetObeysInference.
  intros.
  subst b; assumption.
Qed. *)

(* Lemma provable_by_eq_means_eq p c :
  RulesProveInference eq p c -> p = c.
  intro.
  induction H; [assumption | ].
  subst b; assumption.
Qed. *)

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
  UnfoldsToMeansQuotedByFn a b -> UnfoldsToMeansQuoted a b.
  intro.
  destruct H.
  unfold UnfoldsToMeansQuotedByFn.
  dependent induction x.
  cbn in H. dependent destruction H.
  cbn in H.
  destruct (unfold_step a).
  
  unfold try_unfold_to_quoted in H.
  unfold UnfoldsToMeansQuoted.
Qed.


  
Lemma pair_first_quoted_byfn a b :
  UnfoldsToMeansQuotedByFn [fp_fst (f_pair (quote_f a) b)] a.
  unfold UnfoldsToMeansQuotedByFn.
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.

  
Lemma pair_first_quoted a b :
  UnfoldsToMeansQuoted [fp_fst (f_pair (quote_f a) b)] a.
  
  apply ex_intro with 11.
  cbn.
  rewrite (quoted_no_unfold a).
  rewrite (quote_unquote a).
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_first :
  UnfoldsToMeansQuotedByFn [fp_fst qfs_tail] f_default.
  unfold UnfoldsToMeansQuotedByFn.
  apply ex_intro with 13.
  cbn; reflexivity.
Qed.
  

Lemma qfs_tail_tail handler hout:
    UnfoldsToMeansQuoted [handler qfs_tail] hout
    ->
    UnfoldsToMeansQuoted [(fs_pop_then handler) qfs_tail] hout.
  unfold UnfoldsToMeansQuoted.
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
    IsMeansQuotedStream s ->
    ∃ f, UnfoldsToMeansQuoted [@n s] f.
  intro.
  unfold UnfoldsToMeansQuoted.
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
  UnfoldsToMeansQuoted a b ->
  UnfoldsToMeansQuoted a c ->
  b = c.
  intros.

Qed.

Definition f_true := [[f_quote f_default] -> [f_quote f_default]].
Definition f_false := [f_all [fuse [const f_all] f_implies]].

(* Lemma KnownRequiredInferences_increasing n :
  KnownRequiredInferences n ⊆2 KnownRequiredInferences (S n).
  intros.
  cbn. *)

(* Lemma True_known n :
  TrueOf (KnownInferences n) f_true.
  apply (t_implies (KnownInferences n) f_default f_default).
  destruct n; [reflexivity|].
  cbn. unfold MetaInferences. intros. assumption.
Qed. *)

Lemma false_implies_everything p c :
  InfsAssertedBy f_false p c.
  apply ia_all with (x := p).
  (* apply ia_unfold with b :=. *)
  admit.
Qed.

Lemma false_not_directly_inferrable :
  InfsAssertedBy f_true f_true f_false -> False.
  intro.
  dependent induction H.

Qed.

Lemma false_never_known n :
  KnownInferences n f_true f_false -> False.
  induction n; [trivial|].

  intro.
  cbn in *. unfold MetaInferences in *.
  specialize (H f_true f_false).

  (* use IHn to eliminate the "or already known" case: *)
  assert (InfsAssertedBy f_false f_true f_false
        → InfsAssertedBy f_true f_true f_false) as H2.
  intro. apply H in H0. destruct H0; [assumption|contradiction].
  clear H IHn n. rename H2 into H.

  


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
  unfold InfSetObeysInference in r.
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
  unfold LowerBoundSequence, InferencesTheseInfSetsObey, InfSetObeysInference ; intros.
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
    IsMeansQuotedStream x
    → ∃ ap bp : Formula,
        UnfoldsToMeansQuoted [(fp_fst) (x)] ap /\
        UnfoldsToMeansQuoted [(fp_fst) (x)] bp /\
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

Definition rule_external (rule : ReifiedRule) : InfSet.
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

Definition IC_axioms_rule : InfSet := (λ a b, b = IC_axioms).

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
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey,
    InfSetObeysInference.
  intros. cbn in *. intros.
  clear H0. (* we're not going to use the proof of True *)
  
Qed.

Lemma and_assoc1_required a b c : KnownRequiredInferences 1 [a & [b & c]] [[a & b] & c].
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey, InfSetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.

Lemma and_assoc2_required a b c : KnownRequiredInferences 1 [[a & b] & c] [a & [b & c]].
  unfold KnownRequiredInferences, InferencesTheseInfSetsObey, InfSetObeysInference.
  intros. cbn in *.
  intuition idtac.
Qed.
(* 
Lemma unfold_further :
  RulseProveInference a b *)

Lemma predimp_trans_required a b c :
  AllInfSetsObeyInference [[a |= b] & [b |= c]] [a |= c].
  unfold AllInfSetsObeyInference, InfSetObeysInference; intros; cbn in *.
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

Inductive IC : InfSet :=
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
    UnfoldsToMeansQuoted qa a ->
    (KnownInferences a -> False) ->
    FormulaTrue KnownInferences [qa |= qb]
  | true_implies2 qa qb b :
    UnfoldsToMeansQuoted qb b ->
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
    Forall2 (λ rule_p p, UnfoldsToMeansQuoted (specialize_fwv rule_p values) p) (inf_premises rule) ps ->
    UnfoldsToMeansQuoted (specialize_fwv (inf_conclusion rule) values) c ->
    RuleSpecializes rule (ps |- c).


    
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
  
(* Fixpoint try_unfold_to_quoted steps f : option Formula :=
  match steps with
    | 0 => None
    | S pred => match unfold_step f with
      | None => unquote_formula f
      | Some g => try_unfold_to_quoted pred g
      end
    end. *)

(* Definition UnfoldsToMeansQuotedByFn f g :=
  ∃ steps, try_unfold_to_quoted steps f = Some g. *)

(* Inductive UnfoldsTo
  Interpretation
  (Interpret : Formula -> Interpretation -> Prop)
  : Formula -> Interpretation -> Prop :=
  | unfold_done f i : Interpret f i -> UnfoldsTo Interpret f i
  | unfold_step_then a b i : UnfoldStep a b ->
    UnfoldsTo Interpret b i ->
    UnfoldsTo Interpret a i. *)

(* Quoted formula streams: *)
(* [f => h => h const (f f)] *)
(* Definition qfs_tail_fn := [fuse
    [const [fuse [fuse f_id [const [f_quote f_default]]]]]
    [fuse [const const] [fuse f_id f_id]]
  ].
Definition qfs_tail := [qfs_tail_fn qfs_tail_fn].
Definition qfs_cons head tail := f_pair (quote_f head) tail.
Inductive IsMeansQuotedStream : Formula -> Prop :=
  | isqfs_tail : IsMeansQuotedStream qfs_tail
  | isqfs_cons head tail : IsMeansQuotedStream tail ->
    IsMeansQuotedStream (qfs_cons head tail). *)


(* Definition ObeysIntrinsicMeanings TruthValues KnownJudgedInferences :=
  (∀ a b, KnownJudgedInferences a b ->
    TruthValues [(quote_f a) -> (quote_f b)]) /\
  (∀ a b, TruthValues [a & b] <-> TruthValues a /\ TruthValues b) /\
  (∀ a, TruthValues [f_all a] <->
    (∀ x, TruthValues [a (quote_f x)])) /\
  (∀ a b, UnfoldStep a b -> (TruthValues a <-> TruthValues b))
  . *)


(* The inferences that are guaranteed to be true on formulas that
   speak _about_ an earlier set of inferences - knowing only
   that certain inferences ARE present, but leaving open
   the possibility that more inferences will be added. *)
(* Definition MetaInferences KnownJudgedInferences (a b : Formula) : Prop :=
  ∀ Infs,
    Infs ⊇2 KnownJudgedInferences ->
    (TrueOf Infs a -> TrueOf Infs b). *)

(* Definition MetaInferences KnownJudgedInferences (a b : Formula) :=
  ∀ TruthValues,
    (ObeysIntrinsicMeanings TruthValues KnownJudgedInferences) ->
    (TruthValues a -> TruthValues b). *)

(* Definition FormulaAsRule f (a b : Formula) : Prop :=
  ∀ Infs, TrueOf Infs f -> Infs a b. *)