
Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Vector.
Import EqNotations.
Require Import Coq.Program.Equality.
Load EliUtils.
(* Require Import Eli.EliUtils.

Locate "<". *)

Notation "a ∈ c" := (In a c) (at level 60, no associativity) : type_scope.
Notation "a ∉ c" := (¬In a c) (at level 60, no associativity) : type_scope.

Definition Graph n := Vector.t (list (Fin.t n)) n.

Definition HasPredecessorLeft n (graph : Graph n) (partial_result : list (Fin.t n)) (node : Fin.t n) :=
  ∃ (predecessor : Fin.t n) (edge : listIndex (Vector.nth graph predecessor)), predecessor ∉ partial_result ∧ valueAt edge = node.
  
Inductive TopoStep n (graph : Graph n) (partial_result : list (Fin.t n)) :=
| TopoStepDone (_: ∀ node, HasPredecessorLeft graph partial_result node)
| TopoStepPush next (_: ¬HasPredecessorLeft graph partial_result next).

Inductive PartialTopoSort n (graph : Graph n) : list (Fin.t n) → Prop :=
| TopoSortNil : PartialTopoSort graph nil
| TopoSortCons partial_result next (_: ¬HasPredecessorLeft graph partial_result next) : PartialTopoSort graph (next :: partial_result).

Definition TopoSort n (graph : Graph n) (partial_result : list (Fin.t n)) : Prop := PartialTopoSort graph partial_result ∧ ∀ node, HasPredecessorLeft graph partial_result node.

Lemma PartialTopoSort_is_topological
  n (graph : Graph n) partial_result (sort : PartialTopoSort graph partial_result)
  : 
  (* "If there's an edge from i0 to i1, i1 must come first" *)
  ∀ (i0 i1 : listIndex partial_result) (edge : listIndex (Vector.nth graph (valueAt i0))),
    valueAt edge = valueAt i1 →
    positionOf i1 < positionOf i0.
  admit.
Admitted.  


(*
  
Definition graphRemove n
  (graph: Graph n)
  (removed : Fin.t n)
  : list (list nat)
  := replaceAt removed nil.
  
  
Lemma graphRemoveValid
  (output_edges : list (list nat))
  (output_edges_valid : ∀ (i : listIndex output_edges) (j : listIndex (valueAt i)), valueAt j < length output_edges)
  (removed : listIndex output_edges)
  : let result_edges := (graphRemove removed) in
    ∀ (i : listIndex result_edges) (j : listIndex (valueAt i)), valueAt j < length result_edges.
  intros.
  induction removed; cbn in *.
  
  dependent destruction i; cbn in *.
  easy.
  exact (output_edges_valid (there head i) j).
  
  unfold graphRemove in IHremoved; rewrite (replaceRetainsLength removed nil) in *; dependent destruction i; cbn in *.
  exact (output_edges_valid (here head tail) j).
  admit.
Admitted.

Inductive TopoSort 
  (output_edges : list (list nat))
  (output_edges_valid : ∀ (i : listIndex output_edges) (j : listIndex (valueAt i)), valueAt j < length output_edges) :=
| Done (_: ∀ (node : listIndex output_edges), ∃ (predecessor : listIndex output_edges) (edge : listIndex (valueAt predecessor)), predecessor ≠ node ∧ valueAt edge = positionOf node)
| Step (first : listIndex output_edges) (rest : TopoSort (graphRemoveValid output_edges_valid first)).


Record TopoSortStep := mkTopoSortStep
  { output_edges : Memory
  ; output_edges_valid : list (ThreadId × list Instruction)
  }.
  
  
Record topo_step :
  (output_edges : list (list nat))
  (output_edges_valid : ∀ i j k l , output_edges[i] = l → l[j] = k → k < length output_edges)
  
  
  

Definition topological_ordering_of_noncyclic_machines
  (output_edges : list (list nat))
  (output_edges_valid : ∀ i j k l , output_edges[i] = l → l[j] = k → k < length output_edges)
  : list nat.
  admit.
Admitted.

Lemma topological_ordering_is_topological
  (output_edges : list (list nat))
  (output_edges_valid : ∀ i j k l , output_edges[i] = l → l[j] = k → k < length output_edges)
  : let result := topological_ordering_of_noncyclic_machines output_edges_valid in
  ∀ o0 o1 m0 m1 l i,
    result[o0] = m0 →
    result[o1] = m1 →
    output_edges[m0] = l →
    l[i] = m1 →
    o0 < o1.
  admit.
Admitted.
  *)
