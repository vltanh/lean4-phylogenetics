module

public import Phylogenetics.Network.Basic

/-!
# Pendant taxon cuts

Each labelled leaf of a phylogenetic network has precisely one incoming arc and no outgoing arc. Its
incident arc is therefore a bridge and induces the singleton taxon split.

## Main results

* `exists_singleton_vertex_cut`: a sink of indegree one is separated by exactly its incoming arc.
* `hasSingletonCut`: every taxon gives its singleton cut.
-/

@[expose] public section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

theorem source_ne_target_of_acyclic (hG : G.IsAcyclic) (e : E) :
    G.source e ≠ G.target e := by
  intro he
  apply hG (G.source e)
  exact Relation.TransGen.single ⟨e, rfl, he.symm⟩

/-- Indegree one identifies an actual unique incoming arc. -/
theorem exists_incoming_of_indegree_one {v : V} (hv : G.indegree v = 1) :
    ∃ e, ∀ f, G.target f = v ↔ f = e := by
  obtain ⟨e, he⟩ := Set.ncard_eq_one.mp hv
  refine ⟨e, ?_⟩
  intro f
  have hf := Set.ext_iff.mp he f
  exact hf

/-- An indegree-one sink is separated by exactly its unique incoming arc. -/
theorem exists_singleton_vertex_cut [Finite E] {v : V}
    (hin : G.indegree v = 1) (hout : G.outdegree v = 0) :
    ∃ e, ∀ f, G.Crosses f {v} ↔ f = e := by
  obtain ⟨e, he⟩ := G.exists_incoming_of_indegree_one hin
  refine ⟨e, ?_⟩
  intro f
  have hsource := (G.outdegree_eq_zero_iff v).mp hout f
  change ((G.source f = v ∧ G.target f ≠ v) ∨
    (G.target f = v ∧ G.source f ≠ v)) ↔ f = e
  simp [hsource, he f]

end Phylogenetics.DirectedMultigraph

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- Every pendant taxon gives its singleton cut in the original multigraph. -/
theorem hasSingletonCut (hN : N.IsPhylogenetic) (x : X) :
    N.HasCutSplit {x} := by
  let : Finite E := hN.finite_arcs
  have hout : N.graph.outdegree (N.leaf x) = 0 := (hN.leaves _).mpr ⟨x, rfl⟩
  obtain ⟨e, he⟩ := N.graph.exists_singleton_vertex_cut
    (hN.leaf_indegree x) hout
  refine ⟨e, {N.leaf x}, he, ?_⟩
  ext y
  exact hN.leaf_injective.eq_iff

end Phylogenetics.RootedNetwork
