module

public import Phylogenetics.Network.Level1.Digraph.InvariantCycle
public import Phylogenetics.Network.Level1.Digraph.InvariantSide
public import Phylogenetics.Network.Level1.Digraph.InvariantTree
/-!
# Every well-formed network term is a rooted binary metric level-1 network

The graph of a well-formed term `N : Phylogenetics.Net X` with at least two leaves is a rooted
binary metric level-1 phylogenetic network on the taxa `X` in the sense of
`Phylogenetics.MetricDigraph.IsNetwork` (`Phylogenetics.Net.isNetwork_toGraph`).

The proof follows the term (`Phylogenetics.Net.isSubnet_toGraph`): the graph of every well-formed
term has the invariant `Phylogenetics.MetricDigraph.IsSubnet` (`Phylogenetics.Network.Level1.Digraph.Invariant`),
which passes from the subnetworks and the sides (`Phylogenetics.SideGraph.IsSide`) to a tree node
(`Phylogenetics.Network.Level1.Digraph.InvariantTree`), a node of a side (`Phylogenetics.Network.Level1.Digraph.InvariantSide`) and a
cycle (`Phylogenetics.Network.Level1.Digraph.InvariantCycle`). A graph with the invariant whose root has two children
is a network (`Phylogenetics.MetricDigraph.IsSubnet.isNetwork`); the root of a term with at least
two leaves does. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

variable {X : Type u}

mutual
/-- The graph of a well-formed network term has the invariant `MetricDigraph.IsSubnet`, with the
root of the term as its root. -/
theorem Net.isSubnet_toGraph : (N : Net X) → N.IsMetric → N.leaves.Nodup →
    N.toGraph.IsSubnet N.root
  | .leaf x, _, _ => MetricDigraph.isSubnet_leaf x
  | .tree ℓ₁ N₁ ℓ₂ N₂, ⟨hℓ₁, hℓ₂, hN₁, hN₂⟩, hnd => by
    rw [Net.leaves, List.nodup_append] at hnd
    exact MetricDigraph.isSubnet_tree hℓ₁ hℓ₂ (N₁.isSubnet_toGraph hN₁ hnd.1)
      (N₂.isSubnet_toGraph hN₂ hnd.2.1) fun a b x ha hb =>
        hnd.2.2 x ((N₁.exists_label_eq_some_iff x).1 ⟨a, ha⟩) x
          ((N₂.exists_label_eq_some_iff x).1 ⟨b, hb⟩) rfl
  | .cycle γ S₁ S₂ ℓ N, ⟨hγ, hγ1, hℓ, hS₁, hS₂, hN, hne⟩, hnd => by
    rw [Net.leaves, List.nodup_append, List.nodup_append] at hnd
    obtain ⟨⟨hnd₁, hnd₂, hd₁₂⟩, hndN, hd⟩ := hnd
    have hne' : S₁.toGraph.first ≠ none ∨ S₂.toGraph.first ≠ none := by
      rw [Ne, Ne, Side.toGraph_first_eq_none_iff, Side.toGraph_first_eq_none_iff]
      exact hne
    exact MetricDigraph.isSubnet_cycle hγ hγ1 hℓ (S₁.isSide_toGraph hS₁ hnd₁)
      (S₂.isSide_toGraph hS₂ hnd₂) (N.isSubnet_toGraph hN hndN) hne'
      (fun a b x ha hb => hd₁₂ x ((S₁.exists_label_eq_some_iff x).1 ⟨a, ha⟩) x
        ((S₂.exists_label_eq_some_iff x).1 ⟨b, hb⟩) rfl)
      (fun a c x ha hc => hd x (List.mem_append_left _
        ((S₁.exists_label_eq_some_iff x).1 ⟨a, ha⟩)) x
        ((N.exists_label_eq_some_iff x).1 ⟨c, hc⟩) rfl)
      (fun b c x hb hc => hd x (List.mem_append_right _
        ((S₂.exists_label_eq_some_iff x).1 ⟨b, hb⟩)) x
        ((N.exists_label_eq_some_iff x).1 ⟨c, hc⟩) rfl)

/-- The graph of a well-formed side of a cycle has the invariant `SideGraph.IsSide`. -/
theorem Side.isSide_toGraph : (S : Side X) → S.IsMetric → S.leaves.Nodup → S.toGraph.IsSide
  | .hyb _, hℓ, _ => SideGraph.isSide_hyb hℓ
  | .node ℓ b N S, ⟨hℓ, hb, hN, hS⟩, hnd => by
    rw [Side.leaves, List.nodup_append] at hnd
    exact SideGraph.isSide_node hℓ hb (N.isSubnet_toGraph hN hnd.1) (S.isSide_toGraph hS hnd.2.1)
      fun a c x ha hc => hnd.2.2 x ((N.exists_label_eq_some_iff x).1 ⟨a, ha⟩) x
        ((S.exists_label_eq_some_iff x).1 ⟨c, hc⟩) rfl
end

/-- **Every well-formed network term with at least two leaves is a network.** The graph of a
well-formed `N` (positive edge lengths, inheritance probabilities in `(0, 1)`, no cycle of two
edges, distinct leaf labels) with at least two leaves is a rooted binary metric level-1
phylogenetic network on the taxa `X`. -/
theorem Net.isNetwork_toGraph {N : Net X} (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) :
    N.toGraph.IsNetwork := by
  refine (N.isSubnet_toGraph hN.1 hN.2).isNetwork ?_
  cases N with
  | leaf x => simp [Net.leaves] at h2
  | tree ℓ₁ N₁ ℓ₂ N₂ => exact MetricDigraph.tree_outdeg_root
  | cycle γ S₁ S₂ ℓ N =>
    obtain ⟨-, -, -, -, -, -, hne⟩ := hN.1
    refine MetricDigraph.cycle_outdeg_top ?_
    rw [Ne, Ne, Side.toGraph_first_eq_none_iff, Side.toGraph_first_eq_none_iff]
    exact hne

end Phylogenetics
