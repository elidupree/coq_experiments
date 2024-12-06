Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import List.
Require Import String.

(* Hack - remove later *)
Parameter cheat : ∀ {A}, A.

(* Protect myself from accidental infinite loops during dev work *)
(* Set Typeclasses Iterative Deepening. *)
Set Typeclasses Depth 3.

(****************************************************
                 Proof bureaucracy
****************************************************)

Section ProofBureaucracy.
  (* When proving, there are a lot of simplification steps that I want to be applied automatically, with very little effort. As the definitions and lemmas proceed, I want to add more simplification steps to a hints database.

  Unfortunately, the `auto` family of tactics, which apply hints from a database, cancel all the applications if you didn't solve the entire goal. That's not what I want. As a hack to work around this, it's possible to shelve an incomplete goal, and `auto` will interpret this as "success". So we just end every hint with `shelve`. *)

  Ltac autouse_shelving_db steps db :=
    idtac steps; match steps with
      | S ?p => try ((progress (unshelve typeclasses eauto 99 with db));
        autouse_shelving_db p db)
      | _ => idtac "Warning: steps ran out"
    end.

  Create HintDb simplify.
  Ltac simplify := autouse_shelving_db 20 ident:(simplify).

  (* We *do* want to apply intros if it helps simplify, but not if it doesn't, so don't shelve here. Also, since it's the second-choice and can duplicate work, make it high-cost. *)
  (* Hint Extern 12 => intro; intros : simplify. *)

  (* ...and if we *can* solve easily, might as well. *)
  Hint Extern 1 => solve [trivial | constructor | discriminate] : simplify.

  (* One notable simplification step is to rewrite equality hypotheses when one side is just another hypothesis. But it's kinda expensive, so we give it a high-ish cost. *)
  Hint Extern 9 => progress match goal with
    | x : _ |- _ => match goal with
      | eq : x = _ |- _ => rewrite eq in *; clear x eq
      | eq : _ = x |- _ => rewrite <- eq in *; clear x eq
      end
    end; shelve
    : simplify.

  (* `remember`, but not if it's redundant *)
  Ltac dontforget term :=
    lazymatch term with
    | (_ _) => lazymatch goal with
      | _ : _ = term |- _ => idtac
      | _ : term = _ |- _ => idtac
      | _ => remember term
      end
    | _ => idtac 
    end.
End ProofBureaucracy.

(****************************************************
                   Tree structure
****************************************************)

Inductive WhichChild := wc_left | wc_right.
Definition Location := list WhichChild.
Bind Scope list_scope with Location.
Notation "'𝕃'" := wc_left.
Notation "'ℝ'" := wc_right.
Hint Extern 5 => progress change (list WhichChild) with Location in *; shelve : simplify.

(****************************************************
                   ContextSet
****************************************************)

Notation "P '⊆₂' Q" := (∀ x y, P x y -> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '≡₂' Q" := (∀ x y, P x y <-> Q x y) (at level 70, no associativity) : type_scope.
Notation "P '∩₂' Q" := (λ x y, P x y ∧ Q x y) (at level 80, right associativity) : type_scope.
Notation "P '∪₂' Q" := (λ x y, P x y ∨ Q x y) (at level 85, right associativity) : type_scope.

Section ContextSet.
  Definition Context M := M -> Location -> Prop.
  Definition ContextSet := ∀ M, Context M -> Prop.
    
  Section AbandonedApproaches.
    (* Definition ContextHasSubtreeAt M (x : Location) (C S : Context M) : Prop
      := ∀ d m, S d m -> C (x++d) m. *)
    (* Definition ContextSet_Positive (Cs : ContextSet) :=
      ∀ M C1 C2, C1 ⊆₂ C2 -> Cs M C1 -> ∃ C3, C2 ⊆₂ C3 ∧ Cs M C3. *)
    (* Inductive MappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) : Context N :=
      mc_cons x m d n : Cₘ x m -> Map m d n -> MappedContext Map Cₘ (x++d) n. *)

    (* Definition WithinMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) (Cₙ : Context N) :=
      ∀ y n Cₙ₂, Cₙ y n -> ContainsMappedContext Map Cₘ Cₙ₂ ->
        Cₙ₂ y n. *)

    (* Inductive IsMappedPair M N (Map : M -> Context N) m n x : Location -> Prop :=
      imp_cons d : Map m d n -> IsMappedPair Map m n x (x++d). 
    Definition IsMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) (Cₙ : Context N) :=
      ∀ x d m, Cₘ x m -> ∀ mapped pairs, Cₙ xd n
      ∧
      ∀ xd n, Cₙ xdn -> ∃ mapped pair, Cₘ xd n. *)
        
    (* Definition IsMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) (Cₙ : Context N) :=
        ∀ x m, Cₘ x m <-> ContextHasSubtreeAt x Cₙ (Map m). *)

    (* Definition ContextSet_Extensional (Cs : ContextSet) :=
      ∀ M C1 C2, C1 ≡₂ C2 -> Cs M C1 -> Cs M C2. *)
    (* Definition MeaningsCanContainOtherMeanings (Cs : ContextSet) :=
      ∀ M C1 C2 (Submeanings : M -> Context M),
        C2 ≡₂ (λ x m, ∀ C3, C3 ⊆₂ C2 -> (MeaningsAgree Submeanings C3) -> C3 x m) ->
        Cs M C1 ->
        Cs M C2 *)
        (* (λ)
        Cs M C1 ->
        ∃ C2, Cs M C2 ∧
          C1 ⊆₂ C2 ∧
          ∀ x d m n, Submeanings m d n ->
            C2 x m -> C2 (x++d) n *)
    
    (* Definition ContainsMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) (Cₙ : Context N) :=
      (∀ x d m n, Cₘ m x -> Map m n d ->
        Cₙ n (x++d)).

    Definition CanonicalMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) :=
      λ y n, ∀ Cₙ₂, ContainsMappedContext Map Cₘ Cₙ₂ -> Cₙ₂ y n.

    Definition IsMappedContext M N (Map : M -> Context N)
      (Cₘ : Context M) (Cₙ : Context N) :=
      Cₙ ≡₂ CanonicalMappedContext Map Cₘ. *)
  End AbandonedApproaches.

  Inductive MappedContext M N (Map : M -> Context N)
    (Cₘ : Context M) : Context N :=
    mc_cons x d m n : Cₘ m x -> Map m n d ->
      MappedContext Map Cₘ n (x++d).

  Definition ContextSet_DoesntTreatMeaningsDifferentlyFromSubtrees
    (Cs : ContextSet) := ∀ M N C1 C2 (Submeanings : M -> Context N),
      C2 ≡₂ MappedContext Submeanings C1 ->
      Cs M C1 -> Cs N C2.
  
  Class CsValid (Cs : ContextSet) := {
        csv_subtrees : ContextSet_DoesntTreatMeaningsDifferentlyFromSubtrees Cs
      (* ; csv_full : ∀ M C, (∀ m x, C m x) -> Cs M C *)
    }.
  
  (* Inductive SameLinealRelation (x y xo yo : Location) : 
  (* Location -> Location -> Location -> Location ->  *)
  Prop :=
    slr_cons d e : x++d = xo++e -> y++d = yo++e -> SameLinealRelation x y xo yo. *)
    (* cso_cons x m : C (x++d) m -> CsOffset d e C (x++e) m. *)
  (* Definition ConformsTo x y : ContextSet :=
    λ M C, ∀ d m, C (x++d) m -> C (y++d) m. *)
  (* Definition ConformsTo x y : ContextSet :=
    λ M C, ∀ m xo yo, SameLinealRelation x y xo yo -> C xo m -> C yo m. *)
  Inductive MemberAtLinealRelation S (x d e : Location) : 
  (* Location -> Location -> Location -> Location ->  *)
  Prop :=
    mlr_cons xo : S xo -> x++d = xo++e -> MemberAtLinealRelation S x d e.
  Definition ConformsTo x y : ContextSet :=
    λ M C, ∀ m d e, MemberAtLinealRelation (C m) x d e -> MemberAtLinealRelation (C m) y d e.
  Definition UnifiesWith x y : ContextSet :=
    ConformsTo x y ∩₂ ConformsTo y x.
  (* Definition Independent (I : Location -> Prop) (Cs : ContextSet) : Prop :=
    ∀ M (m : M), ∃ C, Cs M C ∧ ∀ x, I x -> C x m. *)
  
  Section Properties.
    Lemma CsValid_union A B : CsValid A -> CsValid B -> CsValid (A ∪₂ B).
      intros CVA CVB.
      constructor.
      {
        red; intros.
        destruct H0; [left|right]; [destruct CVA|destruct CVB];
          apply (csv_subtrees0 M N C1 C2 Submeanings); assumption.
      }
      (* {
        intros.
        left.
        apply csv_full; assumption.
      } *)
    Qed.
    
    (* Doesn't work because "union of nothing" doesn't have the "full" case *)
    (* Lemma CsValid_Union (CSs : ContextSet -> Prop) :
      (∀ Cs, CSs Cs -> CsValid Cs) ->
      CsValid (λ x m, ∃ Cs, CSs Cs ∧ Cs M C).
      intros CSsV.
      constructor.
      {
        red; intros.
        destruct H0 as (Cs, (CSsCs, CsMC1)).
        exists Cs.
        destruct (CSsV Cs CSsCs).
        split; trivial.
        apply (csv_subtrees0 M N C1 C2 Submeanings); assumption.
      }
      {
        intros.
        
        left.
        apply csv_full; assumption.
      }
    Qed. *)
    Lemma CsValid_intersection A B : CsValid A -> CsValid B -> CsValid (A ∩₂ B).
      intros CVA CVB.
      constructor.
      {
        red; intros.
        destruct H0.
        split; [destruct CVA|destruct CVB];
          apply (csv_subtrees0 M N C1 C2 Submeanings); assumption.
      }
      (* {
        intros. split; apply csv_full; assumption.
      } *)
    Qed.

    Lemma ConformsTo_Valid x y : CsValid (ConformsTo x y).
      constructor.
      {
        red; intros.
        intros n d e Mxde.
        destruct Mxde as (xo, C2nxo, xdxe).

        (* destruct xyo. *)
        red in H.
        pose (proj1 (H _ _) C2nxo) as HX; clearbody HX.

        (* assert (∃ xm ym f m, Submeanings m f n ∧ xm ++ f = x ∧ ym ++ f = y ∧ C1 xm m). *)
        (* assert (∃ xm m f, Submeanings m n f ∧ xm ++ f = xo) as exh. *)
        destruct HX as (xb, f, m, n, C1mxb, Smfn).
        (* assert (∃ xb m f, C1 m xb ∧ Submeanings m n f ∧ xb ++ f = xo) as exh.
        {
          apply HX.
          red; intros.

          exists x0.
          exists m.
          exists d0.
          intuition idtac; trivial.
        }
        destruct exh as (xb, (m, (f, (C1mxb, (Smfn, xbfx))))). *)
        red in H0.
        specialize (H0 m d (f ++ e)).
        lapply H0.
        {
          intros (yb, C1myb, ydye).
          apply mlr_cons with (yb ++ f).
          refine (proj2 (H _ _) _).
          econstructor; try eassumption.
          rewrite <- app_assoc; assumption.
        }
        apply mlr_cons with xb; trivial.
        rewrite app_assoc.
        assumption.
      }
      (* {
        intros. split; apply csv_full; assumption.
      } *)
    Qed.

    Lemma UnifiesWith_Valid x y : CsValid (UnifiesWith x y).
      apply CsValid_intersection; apply ConformsTo_Valid.
    Qed.
  End Properties.
End ContextSet.

(****************************************************
              More concrete ContextSets
****************************************************)
Section ConcreteContextSet.
  (* Inductive FilterToSubtree (x : Location) M (C : Context M) : Context M :=
    fts_cons m l : C m (x++l) -> FilterToSubtree x C m (x++l). *)
  Inductive MovedSubcontext (x y : Location) M (C : Context M) : Context M :=
    movedSc_cons m (l : Location) : C m (x++l) -> MovedSubcontext x y C m (y++l).

  Inductive MoveCS (x y : Location) (S : ContextSet) : ContextSet :=
    moveCS_cons M Cx Cy :
      Cy ≡₂ MovedSubcontext x y Cx ->
      S M Cx -> MoveCS x y S Cy.

  Section Properties.
    Lemma MovedSubcontext_assoc d e x y M (C:Context M) m :
      MovedSubcontext x y C m (y++d++e) <-> MovedSubcontext (x++d) (y++d) C m (y++d++e).
      split; intro; remember (y ++ d ++ e); destruct H.
      {
        apply app_inv_head in Heql.
        rewrite Heql.
        rewrite app_assoc.
        constructor.
        rewrite <- app_assoc.
        rewrite <- Heql.
        assumption.
      }
      {
        rewrite <- app_assoc.
        constructor.
        rewrite app_assoc.
        assumption.
      }
    Qed.


    Lemma MoveCS_Valid x y S : CsValid S -> CsValid (MoveCS x y S).
      intro CVS.
      constructor.
      red; intros.
      destruct H0.
      apply moveCS_cons with (MappedContext Submeanings
       (FilterToSubtree x Cx)
       (* Cx *)
       ).
      split; intros.
      apply H in H2.
      (* remember x0. remember y0. *)
      destruct H2.
      apply H0 in H2.
      destruct H2.
      rewrite <- app_assoc.
      apply MovedSubcontext_assoc.
      rewrite app_assoc.
      econstructor.
      econstructor.
      econstructor.
      eassumption.
      assumption.
      apply H.
      destruct H2.
      remember (x ++ l).
      destruct H2.
      destruct H2.
      rewrite <- app_assoc in Heql0.
      apply app_inv_head in Heql0.
      rewrite <- Heql0.
      rewrite app_assoc.
      econstructor.
      apply H0.
      econstructor.
      eassumption. assumption.
      destruct CVS.
      red in csv_subtrees0.
      eapply csv_subtrees0.

      red; intros n l.
      split; intro.
      destruct H2.
      
       apply H. econstructor.
      apply H0.
      
       apply H. red; intros.
      red in H3.
      refine (H3 y _ _ _ _ _).
      apply H3.
      
  
  End Properties.

End ConcreteContextSet.