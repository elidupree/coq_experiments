
Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Unicode.Utf8.
Require Import List.
Require Import Vector.
Import EqNotations.
Require Import Coq.Program.Equality.
Load EliUtils.
(* Require Import Eli.EliUtils.
 *)

Notation "a ∈ c" := (In a c) (at level 60, no associativity) : type_scope.
Notation "a ∉ c" := (¬In a c) (at level 60, no associativity) : type_scope.
Notation "g [ i ]" := (Vector.nth g i) (at level 60, no associativity) : type_scope.

Definition Graph n := Vector.t (list (Fin.t n)) n.

Definition HasPredecessorLeft n (graph : Graph n) (partial_result : list (Fin.t n)) (node : Fin.t n) :=
  ∃ (predecessor : Fin.t n) (edge : listIndex (graph[predecessor])), predecessor ∉ partial_result ∧ valueAt edge = node.
  
Inductive TopoStep n (graph : Graph n) (partial_result : list (Fin.t n)) :=
| TopoStepDone (_: ∀ node, HasPredecessorLeft graph partial_result node)
| TopoStepPush next (_: ¬HasPredecessorLeft graph partial_result next).

Inductive PartialTopoSort n (graph : Graph n) : list (Fin.t n) → Prop :=
| TopoSortNil : PartialTopoSort graph nil
| TopoSortCons partial_result next : ¬In next partial_result → ¬HasPredecessorLeft graph partial_result next → PartialTopoSort graph (partial_result) → PartialTopoSort graph (next :: partial_result).

Definition TopoSort n (graph : Graph n) (partial_result : list (Fin.t n)) : Prop := PartialTopoSort graph partial_result ∧ ∀ node, HasPredecessorLeft graph partial_result node.


Lemma PartialTopoSort_NotIn_IfEdgeTo 
  n (graph : Graph n) partial_result (sort : PartialTopoSort graph partial_result)
  (node : Fin.t n) (edge : listIndex (graph[node]))
  : node ∉ partial_result → (valueAt edge) ∉ partial_result.
  intuition idtac; dependent induction sort. easy.
  specialize (IHsort node edge (λ tail, H1 (or_intror tail))).
  destruct (eq_dec next (valueAt edge)).
  rewrite e in *. contradict H0. exists node; exists edge; split.
  contradict H1; right; assumption. reflexivity.
  destruct H2; contradiction.
Qed.

Lemma PartialTopoSort_is_topological
  n (graph : Graph n) partial_result (sort : PartialTopoSort graph partial_result)
  : 
  (* "If there's an edge from i0 to i1, i1 must come first" *)
  ∀ (i0 i1 : listIndex partial_result) (edge : listIndex (graph[valueAt i0])),
    valueAt edge = valueAt i1 →
    positionOf i1 < positionOf i0.
  
  intros; dependent induction sort. easy.
  
  dependent destruction i1; dependent destruction i0; cbn in *.
  
  contradict H0; exists next; exists edge; tauto.
  apply PeanoNat.Nat.lt_0_succ.
  exfalso. pose (PartialTopoSort_NotIn_IfEdgeTo sort next edge H) as vnp. rewrite H1 in *. exact (vnp (listIndex_In i1)).
  
  apply Lt.lt_n_S. exact (IHsort i0 i1 edge H1).
Qed.
  
Search "fold".
Definition InEdgeCount_one n (edges : list (Fin.t n)) i := fold_left (λ count dst, if eq_dec dst i then S count else count) edges 0.
Definition InEdgeCount n (graph : Graph n) partial_result i := Vector.fold_left (λ count edges, if in_dec eq_dec i partial_result then count else count + InEdgeCount_one edges i) 0 graph.
Definition InEdgeCounts n (graph : Graph n) (counts : Vector.t nat n) partial_result := ∀ i, counts[i] = InEdgeCount graph partial_result i.

Lemma InEdgeCount_nonzero_HasPredecessorLeft n (graph : Graph n) partial_result i (nonzero : InEdgeCount graph partial_result i ≠ 0) : HasPredecessorLeft graph partial_result i.
  unfold Graph in graph.
  refine((fix iH n2 (v: Vector.t (list (Fin.t n)) n2) := _) n graph).
  
  (*; destruct v.
  admit.
  induction graph.
  unfold InEdgeCount in nonzero.
  induction graph.*)
  admit.
Admitted.

Record TopoSortAlgo_State n := mkTopoSortAlgo_State
  { in_edge_counts : Vector.t nat n
  ; unrecorded_nodes_with_no_in_edges : list (Fin.t n)
  ; partial_result : list (Fin.t n)
  }.
  
Definition TopoSortAlgo_State_Valid n (graph : Graph n) state :=
  InEdgeCounts graph (in_edge_counts state) (partial_result state) ∧ (∀ i, (in_edge_counts state)[i] = 0 ↔ i ∈ unrecorded_nodes_with_no_in_edges state) ∧ NoDup (unrecorded_nodes_with_no_in_edges state) ∧ PartialTopoSort graph (partial_result state).

Fixpoint uncount_edges
  n (graph : Graph n) 
  (in_edge_counts : Vector.t nat n)
  (unrecorded_nodes_with_no_in_edges : list (Fin.t n))
  (dsts : list (Fin.t n))
  : Vector.t nat n × list (Fin.t n)
  := match dsts with
  | nil => (in_edge_counts, unrecorded_nodes_with_no_in_edges)
  | dst :: tail => let (in_edge_counts, unrecorded_nodes_with_no_in_edges) := uncount_edges graph in_edge_counts unrecorded_nodes_with_no_in_edges tail in
    let new := in_edge_counts[dst] - 1 in (
    Vector.replace in_edge_counts dst new,
    match new with
    | 0 => dst :: unrecorded_nodes_with_no_in_edges
    | S _ => unrecorded_nodes_with_no_in_edges
    end)
  end.
  

Definition TopoSortAlgo_step
  n (graph : Graph n)
  (state : TopoSortAlgo_State n)
  : TopoSortAlgo_State n + list (Fin.t n)
  := 
  match unrecorded_nodes_with_no_in_edges state with
  | nil => inr (partial_result state)
  | head :: tail => let (in_edge_counts, unrecorded_nodes_with_no_in_edges) := (uncount_edges graph (in_edge_counts state) tail (graph[head])) in
  inl (mkTopoSortAlgo_State
    in_edge_counts
    unrecorded_nodes_with_no_in_edges
    (head :: partial_result state)
  )
  end.

Lemma TopoSortAlgo_step_valid
  n (graph : Graph n)
  (state : TopoSortAlgo_State n)
  (state_valid : TopoSortAlgo_State_Valid graph state)
  (step_result := TopoSortAlgo_step graph state)
  : match step_result with
    | inr result => TopoSort graph result
    | inl state => TopoSortAlgo_State_Valid graph state
    end.
  destruct state.
  destruct state_valid as [counts_valid q]; destruct q as [unrecorded_correct q]; destruct q as [unrecorded_nodup partial_sort].
  destruct unrecorded_nodes_with_no_in_edges0; cbn in *.
  
  split.
  assumption.
  intros.
  specialize (unrecorded_correct node); destruct unrecorded_correct as [node_in_edge_count_nonzero _].
  specialize (counts_valid node).
  rewrite counts_valid in node_in_edge_count_nonzero.
  
  admit.
  
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
