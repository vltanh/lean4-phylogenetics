module

public import Phylogenetics.Graph.Complete
public import Phylogenetics.Graph.Invariance
public import Phylogenetics.Graph.Sound
/-!
# Rooted binary metric level-1 networks are the graphs of the network terms

A directed graph with leaf labels, edge lengths and inheritance probabilities is a rooted binary
metric level-1 phylogenetic network on the taxa `X` (`Phylogenetics.MetricDigraph.IsNetwork`) if
and only if it is isomorphic to the graph of a well-formed term `Phylogenetics.Net X` with at least
two leaves (`Phylogenetics.MetricDigraph.isNetwork_iff_exists_net`):
`Phylogenetics.Net.isNetwork_toGraph`, `Phylogenetics.MetricDigraph.IsNetwork.exists_net`, and the
invariance of the definitions under isomorphisms (`Phylogenetics.MetricDigraph.Iso.isNetwork_iff`).
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

variable {X : Type u}

/-- **Rooted binary metric level-1 networks are the graphs of the network terms.** A directed
graph `G` with leaf labels, edge lengths and inheritance probabilities is a rooted binary metric
level-1 phylogenetic network on the taxa `X` if and only if it is isomorphic to the graph of a
well-formed term `N : Net X` with at least two leaves. -/
theorem MetricDigraph.isNetwork_iff_exists_net {V : Type*} (G : MetricDigraph V X) :
    G.IsNetwork ↔
      ∃ N : Net X, N.WellFormed ∧ 2 ≤ N.leaves.length ∧ Nonempty (G.Iso N.toGraph) := by
  refine ⟨fun hG => hG.exists_net, ?_⟩
  rintro ⟨N, hN, h2, ⟨e⟩⟩
  exact e.isNetwork_iff.2 (Net.isNetwork_toGraph hN h2)

end Phylogenetics
