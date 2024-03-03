Require Import Unicode.Utf8.

Definition Class (p:(Type -> Type)) := p.
Existing Class Class.

Class SubclassOf Superclass Subclass := {
  superclass_instance : ∀ {T} {_:Class Subclass T}, Class Superclass T
  }.
Notation "R ⊆ S" := (SubclassOf S R) (at level 70).

Definition subclass_apply {A B T}
  : (A ⊆ B) -> Class A T -> Class B T
  := λ _ _, superclass_instance.
Hint Immediate subclass_apply : typeclass_instances.
(* Hint Resolve subclass_apply : typeclass_instances. *)

Definition MyConstrs : Type -> Type := λ t, t.

Set Typeclasses Debug Verbosity 2.
Definition test_subclass_apply_with_VConsClass_FormulaConstructors
  {A B C T} (v:Class A T)
  {_:A ⊆ B}
  {_:C ⊆ B}
  : Class B T.
  clear X0.
  (* typeclasses eauto. *)
  (* eauto with typeclass_instances. *)
  simple eapply subclass_apply ; trivial.
  (* apply X. *)
  trivial.