module

public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
/-!
# Phylogenetic networks as directed graphs

Rooted phylogenetic networks are directed acyclic graphs; the library describes them by the terms
`Phylogenetics.Net` (`Phylogenetics.Network.Level1.Defs`). This module states the usual definitions for directed
graphs, so that `Phylogenetics.Network.Level1.Digraph.Sound` and `Phylogenetics.Network.Level1.Digraph.Complete` can compare the
two.

* `Phylogenetics.MetricDigraph V X`: a directed graph on the vertices `V` (Mathlib's `Digraph`) with
  the data of a metric phylogenetic network on the taxa `X`: the labels of the leaves, the edge
  lengths `ω` and the inheritance probabilities `γ`.
* In- and out-degrees; roots, leaves, tree nodes and hybrid nodes; the undirected graph
  (Mathlib's `Digraph.toSimpleGraphInclusive`) and its cycles (Mathlib's
  `SimpleGraph.Walk.IsCycle`).
* `Phylogenetics.MetricDigraph.IsNetwork`: a rooted binary metric level-1 phylogenetic network on
  the taxa `X`: binary (`IsBinary`), level-1 (`IsLevel1`), metric (`IsMetric`), with leaves labelled
  by distinct taxa (`IsLabelled`).
* `Phylogenetics.MetricDigraph.Iso`: isomorphisms, which preserve the edges, the leaf labels, the
  edge lengths and the inheritance probabilities. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v w

/-- A directed graph on the vertices `V` with the data of a metric phylogenetic network on the
taxa `X`: the edges `E` (`Adj u v` iff `(u, v) ∈ E`), the labels of the leaves, the edge lengths
`ω` and the inheritance probabilities `γ`. The data are total functions: only the labels of the
leaves, the lengths of the edges and the probabilities of the hybrid edges carry meaning.
`MetricDigraph.IsNetwork` asks that the other vertices carry no label and asks nothing of the other
lengths and probabilities; `MetricDigraph.Iso` compares the labels of all vertices, the lengths of
the edges and the probabilities of the hybrid edges only. -/
structure MetricDigraph (V : Type u) (X : Type v) extends Digraph V where
  /-- The label of each vertex: the taxon of a leaf; `none` for the other vertices. -/
  label : V → Option X
  /-- The length `ω(u, v)` of the edge `(u, v)`, in coalescent units. -/
  len : V → V → ℝ
  /-- The inheritance probability `γ(u, v)` of the hybrid edge `(u, v)`. -/
  inh : V → V → ℝ

namespace MetricDigraph

variable {V : Type u} {W : Type w} {X : Type v} (G : MetricDigraph V X)

/-! ### Degrees and kinds of vertices -/

/-- The in-degree of `v`: the number of edges `(u, v)`. -/
def indeg (v : V) : ℕ := {u | G.Adj u v}.ncard

/-- The out-degree of `v`: the number of edges `(v, w)`. -/
def outdeg (v : V) : ℕ := {w | G.Adj v w}.ncard

/-- A root: in-degree zero and out-degree two. -/
def IsRoot (v : V) : Prop := G.indeg v = 0 ∧ G.outdeg v = 2

/-- A leaf: in-degree one and out-degree zero. -/
def IsLeaf (v : V) : Prop := G.indeg v = 1 ∧ G.outdeg v = 0

/-- A tree node: in-degree one and out-degree two. -/
def IsTreeNode (v : V) : Prop := G.indeg v = 1 ∧ G.outdeg v = 2

/-- A hybrid (reticulation) node: in-degree two and out-degree one. Its two incoming edges are
the hybrid edges. -/
def IsHybrid (v : V) : Prop := G.indeg v = 2 ∧ G.outdeg v = 1

/-! ### Rooted binary metric level-1 networks -/

/-- A binary directed phylogenetic network `N⁺ = (V, E)`: a finite directed acyclic graph with a
unique vertex of in-degree zero, the root, which has out-degree two; every other vertex is a leaf
(in-degree one, out-degree zero), a tree node (in-degree one, out-degree two) or a hybrid node
(in-degree two, out-degree one). -/
structure IsBinary : Prop where
  /-- The graph is finite. -/
  finite : Finite V
  /-- The graph has no directed cycle. -/
  acyclic : ∀ v, ¬ Relation.TransGen G.Adj v v
  /-- A unique vertex, the root, has in-degree zero. -/
  existsUnique_indeg_eq_zero : ∃! r, G.indeg r = 0
  /-- Every vertex is the root, a leaf, a tree node or a hybrid node. -/
  degrees : ∀ v, G.IsRoot v ∨ G.IsLeaf v ∨ G.IsTreeNode v ∨ G.IsHybrid v

/-- The undirected graph of `G`: the directions of the edges forgotten (Mathlib's
`Digraph.toSimpleGraphInclusive`). In an acyclic graph there are no loops and no two edges join
the same two vertices, so no edge is lost. -/
def undirected : SimpleGraph V := G.toDigraph.toSimpleGraphInclusive

/-- Level-1 (after Huson et al. 2010): no two cycles share an edge. Cycles are closed paths
ignoring the directions of the edges: cycles of the undirected graph (`SimpleGraph.Walk.IsCycle`),
traversed from any of their vertices in either direction, so two cycles are the same when they
have the same edges. -/
def IsLevel1 : Prop :=
  ∀ ⦃u v : V⦄ (c : G.undirected.Walk u u) (c' : G.undirected.Walk v v), c.IsCycle →
    c'.IsCycle → (c.edgeSet ∩ c'.edgeSet).Nonempty → c.edgeSet = c'.edgeSet

/-- The metric of a network: the edges have positive lengths, and the hybrid edges inheritance
probabilities in `(0, 1)`, those of the two hybrid edges of a hybrid node `h` adding to one (`γ_h`
and `1 - γ_h`). -/
structure IsMetric : Prop where
  /-- The edges have positive lengths. -/
  len_pos : ∀ u v, G.Adj u v → 0 < G.len u v
  /-- The hybrid edges have inheritance probabilities in `(0, 1)`. -/
  inh_mem_Ioo : ∀ u v, G.Adj u v → G.IsHybrid v → G.inh u v ∈ Set.Ioo 0 1
  /-- The inheritance probabilities of the two hybrid edges of a hybrid node add to one. -/
  inh_add_inh : ∀ u u' v, G.Adj u v → G.Adj u' v → u ≠ u' → G.IsHybrid v →
    G.inh u v + G.inh u' v = 1

/-- The leaves are labelled by taxa, distinct leaves by distinct taxa, and the other vertices
carry no label. -/
structure IsLabelled : Prop where
  /-- Exactly the leaves carry a label. -/
  isSome_label_iff : ∀ v, (G.label v).isSome ↔ G.IsLeaf v
  /-- Distinct leaves carry distinct labels. -/
  label_injective : ∀ u v x, G.label u = some x → G.label v = some x → u = v

/-- `G` is a rooted binary metric level-1 phylogenetic network on the taxa `X`: binary, level-1
and metric, with its leaves labelled by distinct taxa. -/
structure IsNetwork : Prop where
  /-- A binary directed phylogenetic network. -/
  binary : G.IsBinary
  /-- Level-1: no two cycles share an edge. -/
  level1 : G.IsLevel1
  /-- Positive edge lengths, inheritance probabilities in `(0, 1)` adding to one. -/
  metric : G.IsMetric
  /-- The leaves, and only they, are labelled by distinct taxa. -/
  labelled : G.IsLabelled

/-! ### Isomorphisms -/

/-- An isomorphism from `G` to `H`: a bijection of the vertices that preserves the edges in both
directions, the labels (the taxa of the leaves; the other vertices of a network carry none), the
lengths of the edges and the inheritance probabilities of the hybrid edges. Since it preserves
the edges, it preserves in- and out-degrees, so it maps the root, the leaves, the tree nodes and
the hybrid nodes of `G` to those of `H`. Lengths and probabilities off the edges, and
probabilities of tree edges, carry no meaning and are not compared. -/
structure Iso (G : MetricDigraph V X) (H : MetricDigraph W X) extends V ≃ W where
  /-- The edges are preserved in both directions. -/
  adj_iff : ∀ u v, H.Adj (toFun u) (toFun v) ↔ G.Adj u v
  /-- The labels are preserved. -/
  label_eq : ∀ v, H.label (toFun v) = G.label v
  /-- The lengths of the edges are preserved. -/
  len_eq : ∀ u v, G.Adj u v → H.len (toFun u) (toFun v) = G.len u v
  /-- The inheritance probabilities of the hybrid edges are preserved. -/
  inh_eq : ∀ u v, G.Adj u v → G.IsHybrid v → H.inh (toFun u) (toFun v) = G.inh u v

end MetricDigraph

end Phylogenetics
