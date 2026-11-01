module

public import Phylogenetics.Network.Defs
public import Phylogenetics.Graph.Blobs
public import Mathlib.Basic.Real.Basic

/-!
# Rooted networks: basic facts

The graph, the root and the taxon labels of a `RootedNetwork` are data; finiteness and the defining laws
are the separate proposition `RootedNetwork.IsPhylogenetic`. This representation permits parallel arcs,
tree vertices of outdegree one, multifurcations and hybrid vertices of higher degree.

## Main results

* `IsStableAncestor`, `IsLeastStableAncestor`, `IsLSANetwork`: stable ancestors of a set of taxa.
* `hasCutSplit_compl`: a cut-edge split has two sides.
* `graph_connected`: a phylogenetic network is connected.
* `bridgeQuotientData`, `hasCutSplit_iff_bridgeQuotient`: contracting the components left by deleting the
  bridges keeps the labelled cuts.
-/

@[expose] public section

namespace Phylogenetics

namespace RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- A directed path avoiding a vertex, including at its endpoints. -/
def HasPathAvoiding (u v w : V) : Prop :=
  u ≠ w ∧ v ≠ w ∧
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ w ∧ b ≠ w) u v

/-- Every root-to-taxon path for the specified taxa passes through this vertex. -/
def IsStableAncestor (Y : Set X) (v : V) : Prop :=
  ∀ x ∈ Y, ¬ N.HasPathAvoiding N.root (N.leaf x) v

/-- A stable ancestor below every other stable ancestor in the directed order. -/
def IsLeastStableAncestor (Y : Set X) (v : V) : Prop :=
  N.IsStableAncestor Y v ∧
    ∀ w, N.IsStableAncestor Y w → N.graph.Reaches w v

/-- The root is the least stable ancestor of all labelled taxa. -/
def IsLSANetwork : Prop := N.IsLeastStableAncestor Set.univ N.root

theorem root_isStableAncestor (Y : Set X) : N.IsStableAncestor Y N.root := by
  intro x _ h
  exact h.1 rfl

theorem leaf_ne_root (hN : N.IsPhylogenetic) (x : X) : N.leaf x ≠ N.root := by
  intro h
  have hi := hN.leaf_indegree x
  rw [h, hN.root_indegree] at hi
  exact Nat.zero_ne_one hi

theorem hasCutSplit_compl (A : Set X) : N.HasCutSplit Aᶜ ↔ N.HasCutSplit A := by
  have flip : ∀ B, N.HasCutSplit B → N.HasCutSplit Bᶜ := by
    rintro B ⟨e, S, hS, hB⟩
    refine ⟨e, Sᶜ, ?_, ?_⟩
    · intro f
      have hc : N.graph.Crosses f Sᶜ ↔ N.graph.Crosses f S := by
        simp only [DirectedMultigraph.Crosses, Set.mem_compl_iff, not_not]
        tauto
      exact hc.trans (hS f)
    · rw [Set.preimage_compl, hB]
  exact ⟨fun h => by simpa only [compl_compl] using flip Aᶜ h, flip A⟩

/-- A cut split always has an actual bridge arc in the original multigraph. -/
theorem exists_bridge_of_hasCutSplit {A : Set X} (h : N.HasCutSplit A) :
    ∃ e, N.graph.underlying.IsBridge e := by
  obtain ⟨e, S, he, _⟩ := h
  exact ⟨e, (N.graph.isBridge_iff e).mpr ⟨S, he⟩⟩

/-- Root reachability supplies the connectedness required of the underlying
undirected graph. The root also excludes the empty-vertex case. -/
theorem graph_connected (hN : N.IsPhylogenetic) : N.graph.IsConnected := by
  intro u v
  exact (N.graph.walks_symm (N.graph.walks_of_reaches (hN.root_reaches u))).trans
    (N.graph.walks_of_reaches (hN.root_reaches v))

/-- Root and taxon labels transported to the bridge-component quotient.
This is unsuppressed graph data, not a claim that the output already satisfies
every rooted-network degree convention. -/
def bridgeQuotientData : RootedNetwork N.graph.BlobVertex N.graph.BridgeArc X where
  graph := N.graph.bridgeQuotient
  root := Quotient.mk N.graph.blobSetoid N.root
  leaf x := Quotient.mk N.graph.blobSetoid (N.leaf x)

/-- The unsuppressed bridge contraction preserves every labelled cut split. -/
theorem hasCutSplit_iff_bridgeQuotient (A : Set X) :
    N.HasCutSplit A ↔ N.bridgeQuotientData.HasCutSplit A :=
  N.graph.labelled_cut_iff_quotient N.leaf A

end RootedNetwork
end Phylogenetics
