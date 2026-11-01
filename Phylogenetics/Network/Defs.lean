module

public import Phylogenetics.Graph.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Rooted phylogenetic networks: definitions

A rooted network on the taxa `X` is a directed multigraph on arbitrary vertex and arc types, with a
root and a labelling of its sinks. Parallel arcs and vertices of any degree are allowed; binary and
level-1 conditions are separate predicates.

* `RootedNetwork V E X`, `RootedNetwork.IsPhylogenetic`, `IsTreeArc`, `IsHybridArc`, `IsBinary`.
* `RootedNetwork.MetricData`, `RootedNetwork.IsMetric`: edge lengths in coalescent units and
  inheritance probabilities, and their ranges.
* `RootedNetwork.HasCutSplit A`: `A` is the taxon side of a cut edge.
* `RootedNetwork.ancestralVertices`, `ancestralArcs`, `HasCutSplitOn`: the induced subgraph on a set of
  taxa, and its cut-edge splits.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

/-- A rooted network on taxa `X`: graph, root and taxon labels. -/
structure RootedNetwork (V E X : Type*) where
  graph : DirectedMultigraph V E
  root : V
  leaf : X → V

namespace RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- The defining laws of a rooted phylogenetic network: a finite directed acyclic graph in which the
root, of indegree zero, reaches every vertex; sinks are exactly the taxon labels, bijectively, each of
indegree one. Internal vertices of any degree are allowed, including tree vertices of outdegree one.
The root need not be the least stable ancestor of the taxa: what lies above it affects no split with
taxa on both sides. -/
structure IsPhylogenetic : Prop where
  finite_vertices : Finite V
  finite_arcs : Finite E
  finite_taxa : Finite X
  acyclic : N.graph.IsAcyclic
  root_reaches : ∀ v, N.graph.Reaches N.root v
  root_indegree : N.graph.indegree N.root = 0
  nonroot_indegree : ∀ v, v ≠ N.root → 1 ≤ N.graph.indegree v
  leaf_injective : Function.Injective N.leaf
  leaf_indegree : ∀ x, N.graph.indegree (N.leaf x) = 1
  leaves : ∀ v, N.graph.outdegree v = 0 ↔ ∃ x, N.leaf x = v

/-- A tree arc enters a vertex with one incoming arc. -/
def IsTreeArc (e : E) : Prop := N.graph.indegree (N.graph.target e) = 1

/-- A hybrid (reticulation) arc enters a vertex with at least two incoming arcs. -/
def IsHybridArc (e : E) : Prop := 2 ≤ N.graph.indegree (N.graph.target e)

/-- Binary: the root has degree two and every other internal vertex has degree three. -/
def IsBinary : Prop :=
  N.graph.outdegree N.root = 2 ∧
    ∀ v, v ≠ N.root → N.graph.outdegree v ≠ 0 →
      N.graph.indegree v + N.graph.outdegree v = 3

/-- The numerical parameters of a network: edge lengths in coalescent units and inheritance
probabilities. Their ranges are the separate predicate `IsMetric`. -/
structure MetricData (E : Type*) where
  length : E → ℝ
  inheritance : E → ℝ

/-- Valid numerical parameters: tree edges have positive length, hybrid edges nonnegative length,
and the inheritance probabilities of the hybrid edges entering a vertex are positive and sum to one;
tree edges have inheritance one. -/
def IsMetric [Fintype E] (m : MetricData E) : Prop :=
  (∀ e, N.IsTreeArc e → 0 < m.length e) ∧
  (∀ e, N.IsHybridArc e → 0 ≤ m.length e) ∧
  (∀ e, N.IsTreeArc e → m.inheritance e = 1) ∧
  (∀ e, N.IsHybridArc e → 0 < m.inheritance e) ∧
  ∀ v, 2 ≤ N.graph.indegree v →
    ∑ e, (if N.graph.target e = v then m.inheritance e else 0) = 1

/-- `A` is the taxon side of a cut edge: some arc `e` is the only arc crossing a vertex set `S` whose
taxa are exactly `A`. Since the graph is connected, deleting `e` leaves exactly the two components
`S` and its complement, so this is the cut-edge split `A|Aᶜ` (`hasCutSplit_compl`). -/
def HasCutSplit (A : Set X) : Prop :=
  ∃ (e : E) (S : Set V), (∀ f, N.graph.Crosses f S ↔ f = e) ∧ N.leaf ⁻¹' S = A

/-- The vertices ancestral to a taxon of `Y`. -/
def ancestralVertices (Y : Set X) : Set V :=
  {v | ∃ x ∈ Y, N.graph.Reaches v (N.leaf x)}

/-- The arcs ancestral to a taxon of `Y`. They and the vertices above form the induced subgraph on
`Y`, which retains degree-two vertices and everything above the least stable ancestor of `Y`. -/
def ancestralArcs (Y : Set X) : Set E :=
  {e | N.graph.target e ∈ N.ancestralVertices Y}

/-- `A ∩ Y | Y \ A` is a cut-edge split of the network induced on `Y`: some arc of the induced
subgraph is the only arc of that subgraph crossing a vertex set meeting `Y` exactly in `A`. For a
split with two taxa on each side this is unchanged by removing what lies above the least stable
ancestor of `Y` and by suppressing degree-two vertices, so it is the cut-edge split of the induced
4-taxon network (`Phylogenetics.Network.Induced`). -/
def HasCutSplitOn (Y A : Set X) : Prop :=
  ∃ e ∈ N.ancestralArcs Y, ∃ S : Set V,
    (∀ f ∈ N.ancestralArcs Y, N.graph.Crosses f S ↔ f = e) ∧ ∀ x ∈ Y, N.leaf x ∈ S ↔ x ∈ A

end RootedNetwork

end Phylogenetics
