module

public import Phylogenetics.Graph.Connectivity

/-!
# Indegree and outdegree in directed multigraphs

## Main results

* `indegree_eq_zero_iff`, `one_le_indegree_iff`, `indegree_eq_one_iff`, `outdegree_eq_one_iff`: small
  degrees in terms of the arcs.
-/

@[expose] public section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

theorem indegree_eq_zero_iff [Finite E] (v : V) : G.indegree v = 0 ↔ ∀ e, G.target e ≠ v := by
  rw [indegree, Set.ncard_eq_zero]
  exact Set.eq_empty_iff_forall_notMem

theorem one_le_indegree_iff [Finite E] (v : V) : 1 ≤ G.indegree v ↔ ∃ e, G.target e = v := by
  rw [Nat.one_le_iff_ne_zero, Ne, indegree_eq_zero_iff]
  push Not
  exact Iff.rfl

theorem indegree_eq_one_iff (v : V) : G.indegree v = 1 ↔ ∃ e, ∀ f, G.target f = v ↔ f = e := by
  rw [indegree, Set.ncard_eq_one]
  exact exists_congr fun e => Set.ext_iff

theorem outdegree_eq_one_iff (v : V) : G.outdegree v = 1 ↔ ∃ e, ∀ f, G.source f = v ↔ f = e := by
  rw [outdegree, Set.ncard_eq_one]
  exact exists_congr fun e => Set.ext_iff

end Phylogenetics.DirectedMultigraph
