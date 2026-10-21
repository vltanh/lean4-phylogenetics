module

public import Phylogenetics.Defs
public import Phylogenetics.Graph.Defs
public import Mathlib.Tactic.DeriveFintype
/-!
# The graph of a network term

A term `N : Phylogenetics.Net X` describes a network from its root (`Phylogenetics.Defs`). This
module builds the directed graph that it describes,
`Phylogenetics.Net.toGraph N : MetricDigraph N.Vert X`, with its leaf labels, edge lengths and
inheritance probabilities.

* The vertices: `Phylogenetics.Net.Vert N` and `Phylogenetics.Side.Vert S`, by recursion on the
  term, with the vertex types `Phylogenetics.TreeVert` (a tree node on no cycle and its two
  subnetworks), `Phylogenetics.CycleVert` (the top node of a cycle, the two sides, the hybrid node
  and the subnetwork below it) and `Phylogenetics.NodeVert` (a node of a side, its pendant
  subnetwork and the rest of the side).
* The constructions, on any graphs: `Phylogenetics.MetricDigraph.leaf`,
  `Phylogenetics.MetricDigraph.tree`, `Phylogenetics.MetricDigraph.cycle`, and for the sides of a
  cycle `Phylogenetics.SideGraph.hyb` and `Phylogenetics.SideGraph.node`. The graph of a term
  applies them along the term (`Phylogenetics.Net.toGraph`, `Phylogenetics.Side.toGraph`);
  `Phylogenetics.Graph.Complete` also applies them to parts of an arbitrary network.
* The labels in the graph of `N` are the leaves of `N`
  (`Phylogenetics.Net.exists_label_eq_some_iff`, and `Phylogenetics.Side.exists_label_eq_some_iff`
  for the sides).

In the graph of `Net.cycle γ S₁ S₂ ℓ N`, a side with no node is a single hybrid edge from the top
node to the hybrid node; the hybrid edge ending the side `S₁` has inheritance probability `γ`, the
one ending `S₂` has `1 - γ`. If both sides have no node, the two hybrid edges would be parallel
edges, and the graph has only one: `Phylogenetics.Net.IsMetric` excludes this case.
-/

@[expose] public noncomputable section

namespace Phylogenetics

-- BEGIN GRAPHOF DEFINITIONS

universe u

/-! ### Vertex types -/

/-- The vertices of a tree node on no cycle with its two subnetworks (`Net.tree ℓ₁ N₁ ℓ₂ N₂`): the
node, the vertices `left a` of `N₁` and the vertices `right b` of `N₂`. -/
inductive TreeVert (A B : Type) where
  /-- The tree node. -/
  | root
  /-- A vertex of the first subnetwork. -/
  | left (a : A)
  /-- A vertex of the second subnetwork. -/
  | right (b : B)
  deriving DecidableEq, Fintype

/-- The vertices of a side `Side.node ℓ b N S`: its first node, the vertices `pendant a` of the
network `N` hanging from that node, and the vertices `rest c` of the rest `S` of the side. -/
inductive NodeVert (A B : Type) where
  /-- The first node of the side. -/
  | node
  /-- A vertex of the network hanging from the first node. -/
  | pendant (a : A)
  /-- A vertex of the rest of the side. -/
  | rest (c : B)
  deriving DecidableEq, Fintype

/-- The vertices of `Net.cycle γ S₁ S₂ ℓ N`: the top node of the cycle, the vertices `side₁ a` and
`side₂ b` of its two sides, its hybrid node, and the vertices `below c` of the network `N` below
the hybrid node. -/
inductive CycleVert (A B C : Type) where
  /-- The top node of the cycle. -/
  | top
  /-- A vertex of the first side (a node of the side, or of a network hanging from it). -/
  | side₁ (a : A)
  /-- A vertex of the second side. -/
  | side₂ (b : B)
  /-- The hybrid node of the cycle. -/
  | hyb
  /-- A vertex of the network below the hybrid node. -/
  | below (c : C)
  deriving DecidableEq, Fintype

/-! ### The constructions -/

namespace MetricDigraph

variable {X : Type u} {A B C : Type}

/-- The network with a single vertex, a leaf labelled `x`. -/
def leaf (x : X) : MetricDigraph Unit X where
  Adj _ _ := False
  label _ := some x
  len _ _ := 0
  inh _ _ := 0

/-- A tree node on no cycle (`Net.tree ℓ₁ N₁ ℓ₂ N₂`): a new vertex with edges of lengths `ℓ₁` and
`ℓ₂` to the vertex `r₁` of `G₁` and the vertex `r₂` of `G₂` (their roots). -/
def tree (ℓ₁ : ℝ) (G₁ : MetricDigraph A X) (r₁ : A) (ℓ₂ : ℝ) (G₂ : MetricDigraph B X) (r₂ : B) :
    MetricDigraph (TreeVert A B) X where
  Adj
    | .root, .left a => a = r₁
    | .root, .right b => b = r₂
    | .left a, .left a' => G₁.Adj a a'
    | .right b, .right b' => G₂.Adj b b'
    | _, _ => False
  label
    | .root => none
    | .left a => G₁.label a
    | .right b => G₂.label b
  len
    | .root, .left _ => ℓ₁
    | .root, .right _ => ℓ₂
    | .left a, .left a' => G₁.len a a'
    | .right b, .right b' => G₂.len b b'
    | _, _ => 0
  inh
    | .left a, .left a' => G₁.inh a a'
    | .right b, .right b' => G₂.inh b b'
    | _, _ => 0

end MetricDigraph

/-- A side of a cycle (`Phylogenetics.Side`) as a graph: the graph on the nodes of the side and the
vertices of the networks hanging from them; the first and the last node of the side (`none` for a
side that is a single hybrid edge); the length of the edge from the top node of the cycle to the
first node; and the length of the hybrid edge that ends the side, from the last node (or from the
top node, for a side with no node) to the hybrid node. -/
structure SideGraph (A : Type) (X : Type u) where
  /-- The graph on the nodes of the side and the vertices hanging from them. -/
  graph : MetricDigraph A X
  /-- The first node of the side, if any. -/
  first : Option A
  /-- The last node of the side, if any. -/
  last : Option A
  /-- The length of the edge from the top node of the cycle to the first node. -/
  topLen : ℝ
  /-- The length of the hybrid edge ending the side. -/
  hybLen : ℝ

namespace SideGraph

variable {X : Type u} {A B : Type}

/-- The side `Side.hyb ℓ`: a single hybrid edge, of length `ℓ`, and no node. -/
def hyb (ℓ : ℝ) : SideGraph Empty X where
  graph := { Adj := fun _ _ => False, label := fun _ => none, len := fun _ _ => 0,
             inh := fun _ _ => 0 }
  first := none
  last := none
  topLen := ℓ
  hybLen := ℓ

/-- The side `Side.node ℓ b N S`: an edge of length `ℓ` to a node, which has a pendant edge of
length `b` to the vertex `r` of `G` (the root of the graph of `N`), followed by the side `S`. -/
def node (ℓ b : ℝ) (G : MetricDigraph A X) (r : A) (S : SideGraph B X) :
    SideGraph (NodeVert A B) X where
  graph :=
    { Adj := fun
        | .node, .pendant a => a = r
        | .node, .rest c => S.first = some c
        | .pendant a, .pendant a' => G.Adj a a'
        | .rest c, .rest c' => S.graph.Adj c c'
        | _, _ => False
      label := fun
        | .node => none
        | .pendant a => G.label a
        | .rest c => S.graph.label c
      len := fun
        | .node, .pendant _ => b
        | .node, .rest _ => S.topLen
        | .pendant a, .pendant a' => G.len a a'
        | .rest c, .rest c' => S.graph.len c c'
        | _, _ => 0
      inh := fun
        | .pendant a, .pendant a' => G.inh a a'
        | .rest c, .rest c' => S.graph.inh c c'
        | _, _ => 0 }
  first := some .node
  last := some ((S.last.map .rest).getD .node)
  topLen := ℓ
  hybLen := S.hybLen

end SideGraph

namespace MetricDigraph

variable {X : Type u} {A B C : Type}

/-- The top node of a cycle with its two sides and the network below its hybrid node
(`Net.cycle γ S₁ S₂ ℓ N`): edges from the top node to the first nodes of the sides `S₁` and `S₂`
(to the hybrid node, for a side with no node), the hybrid edges from their last nodes to the
hybrid node (inheritance probability `γ` at the end of `S₁`, `1 - γ` at the end of `S₂`), and an
edge of length `ℓ` from the hybrid node to the vertex `r` of `G` (its root). -/
def cycle (γ : ℝ) (S₁ : SideGraph A X) (S₂ : SideGraph B X) (ℓ : ℝ) (G : MetricDigraph C X)
    (r : C) : MetricDigraph (CycleVert A B C) X where
  Adj
    | .top, .side₁ a => S₁.first = some a
    | .top, .side₂ b => S₂.first = some b
    | .top, .hyb => S₁.first = none ∨ S₂.first = none
    | .side₁ a, .side₁ a' => S₁.graph.Adj a a'
    | .side₁ a, .hyb => S₁.last = some a
    | .side₂ b, .side₂ b' => S₂.graph.Adj b b'
    | .side₂ b, .hyb => S₂.last = some b
    | .hyb, .below c => c = r
    | .below c, .below c' => G.Adj c c'
    | _, _ => False
  label
    | .side₁ a => S₁.graph.label a
    | .side₂ b => S₂.graph.label b
    | .below c => G.label c
    | _ => none
  len
    | .top, .side₁ _ => S₁.topLen
    | .top, .side₂ _ => S₂.topLen
    | .top, .hyb => match S₁.first with
      | none => S₁.hybLen
      | some _ => S₂.hybLen
    | .side₁ a, .side₁ a' => S₁.graph.len a a'
    | .side₁ _, .hyb => S₁.hybLen
    | .side₂ b, .side₂ b' => S₂.graph.len b b'
    | .side₂ _, .hyb => S₂.hybLen
    | .hyb, .below _ => ℓ
    | .below c, .below c' => G.len c c'
    | _, _ => 0
  inh
    | .top, .hyb => match S₁.first with
      | none => γ
      | some _ => 1 - γ
    | .side₁ a, .side₁ a' => S₁.graph.inh a a'
    | .side₁ _, .hyb => γ
    | .side₂ b, .side₂ b' => S₂.graph.inh b b'
    | .side₂ _, .hyb => 1 - γ
    | .below c, .below c' => G.inh c c'
    | _, _ => 0

end MetricDigraph

/-! ### The graph of a network term -/

variable {X : Type u}

/- The definitions below on `Net` and `Side` list their cases in the reverse order of the
constructors. Within one module, Lean reuses a pattern-matching function (`match_1`) of the same
shape. A project's `Challenge.lean`, a single module, can copy these definitions together with
`Net.leaves` and the other definitions of `Phylogenetics/Defs.lean`, which list the cases in order.
Their reverse order gives these definitions the same constants in such a copy as here, which
Comparator requires (the same constants in the Challenge and the Solution). -/

mutual
/-- The vertices of the network `N`. -/
def Net.Vert : Net X → Type
  | .cycle _ S₁ S₂ _ N => CycleVert S₁.Vert S₂.Vert N.Vert
  | .tree _ N₁ _ N₂ => TreeVert N₁.Vert N₂.Vert
  | .leaf _ => Unit

/-- The vertices of the side `S`: its nodes and the vertices of the networks hanging from
them. -/
def Side.Vert : Side X → Type
  | .node _ _ N S => NodeVert N.Vert S.Vert
  | .hyb _ => Empty
end

mutual
/-- The vertices of a network are finitely many. -/
@[instance_reducible]
def Net.fintypeVert : (N : Net X) → Fintype N.Vert
  | .cycle _ S₁ S₂ _ N =>
    letI := S₁.fintypeVert
    letI := S₂.fintypeVert
    letI := N.fintypeVert
    inferInstanceAs (Fintype (CycleVert S₁.Vert S₂.Vert N.Vert))
  | .tree _ N₁ _ N₂ =>
    letI := N₁.fintypeVert
    letI := N₂.fintypeVert
    inferInstanceAs (Fintype (TreeVert N₁.Vert N₂.Vert))
  | .leaf _ => inferInstanceAs (Fintype Unit)

/-- The vertices of a side are finitely many. -/
@[instance_reducible]
def Side.fintypeVert : (S : Side X) → Fintype S.Vert
  | .node _ _ N S =>
    letI := N.fintypeVert
    letI := S.fintypeVert
    inferInstanceAs (Fintype (NodeVert N.Vert S.Vert))
  | .hyb _ => inferInstanceAs (Fintype Empty)
end

/-- The vertices of a network are finitely many. -/
instance (N : Net X) : Fintype N.Vert := N.fintypeVert

/-- The vertices of a side are finitely many. -/
instance (S : Side X) : Fintype S.Vert := S.fintypeVert

/-- The root of the network `N`: the leaf, the tree node, or the top node of the cycle. -/
def Net.root : (N : Net X) → N.Vert
  | .cycle .. => (.top : CycleVert _ _ _)
  | .tree .. => (.root : TreeVert _ _)
  | .leaf _ => (() : Unit)

mutual
/-- The graph of the network `N`: its vertices and edges, the labels of its leaves, the lengths of
its edges and the inheritance probabilities of its hybrid edges. -/
def Net.toGraph : (N : Net X) → MetricDigraph N.Vert X
  | .cycle γ S₁ S₂ ℓ N => MetricDigraph.cycle γ S₁.toGraph S₂.toGraph ℓ N.toGraph N.root
  | .tree ℓ₁ N₁ ℓ₂ N₂ => MetricDigraph.tree ℓ₁ N₁.toGraph N₁.root ℓ₂ N₂.toGraph N₂.root
  | .leaf x => MetricDigraph.leaf x

/-- The graph of the side `S` of a cycle, with its first and last nodes and the lengths of its
edges to the top node and to the hybrid node. -/
def Side.toGraph : (S : Side X) → SideGraph S.Vert X
  | .node ℓ b N S => SideGraph.node ℓ b N.toGraph N.root S.toGraph
  | .hyb ℓ => SideGraph.hyb ℓ
end

-- END GRAPHOF DEFINITIONS

mutual
/-- The labels in the graph of `N` are the leaves of `N`. -/
theorem Net.exists_label_eq_some_iff : (N : Net X) → (x : X) →
    ((∃ v, N.toGraph.label v = some x) ↔ x ∈ N.leaves)
  | .leaf y, x => by
    simp only [Net.leaves, List.mem_singleton]
    exact ⟨fun ⟨_, h⟩ => (Option.some_injective _ h).symm, fun h => ⟨(), by rw [h]; rfl⟩⟩
  | .tree ℓ₁ N₁ ℓ₂ N₂, x => by
    rw [Net.leaves, List.mem_append, ← N₁.exists_label_eq_some_iff x,
      ← N₂.exists_label_eq_some_iff x]
    constructor
    · rintro ⟨v, hv⟩
      cases v with
      | root => exact absurd hv (by simp [Net.toGraph, MetricDigraph.tree])
      | left a => exact Or.inl ⟨a, hv⟩
      | right b => exact Or.inr ⟨b, hv⟩
    · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
      · exact ⟨.left a, ha⟩
      · exact ⟨.right b, hb⟩
  | .cycle γ S₁ S₂ ℓ N, x => by
    rw [Net.leaves, List.mem_append, List.mem_append, ← S₁.exists_label_eq_some_iff x,
      ← S₂.exists_label_eq_some_iff x, ← N.exists_label_eq_some_iff x]
    constructor
    · rintro ⟨v, hv⟩
      cases v with
      | top => exact absurd hv (by simp [Net.toGraph, MetricDigraph.cycle])
      | side₁ a => exact Or.inl (Or.inl ⟨a, hv⟩)
      | side₂ b => exact Or.inl (Or.inr ⟨b, hv⟩)
      | hyb => exact absurd hv (by simp [Net.toGraph, MetricDigraph.cycle])
      | below c => exact Or.inr ⟨c, hv⟩
    · rintro ((⟨a, ha⟩ | ⟨b, hb⟩) | ⟨c, hc⟩)
      · exact ⟨.side₁ a, ha⟩
      · exact ⟨.side₂ b, hb⟩
      · exact ⟨.below c, hc⟩

/-- The labels in the graph of the side `S` are the leaves below its nodes. -/
theorem Side.exists_label_eq_some_iff : (S : Side X) → (x : X) →
    ((∃ v, S.toGraph.graph.label v = some x) ↔ x ∈ S.leaves)
  | .hyb ℓ, x => by
    simp only [Side.leaves, List.not_mem_nil, iff_false, not_exists]
    intro v
    exact v.elim
  | .node ℓ b N S, x => by
    rw [Side.leaves, List.mem_append, ← N.exists_label_eq_some_iff x,
      ← S.exists_label_eq_some_iff x]
    constructor
    · rintro ⟨v, hv⟩
      cases v with
      | node => exact absurd hv (by simp [Side.toGraph, SideGraph.node])
      | pendant a => exact Or.inl ⟨a, hv⟩
      | rest c => exact Or.inr ⟨c, hv⟩
    · rintro (⟨a, ha⟩ | ⟨c, hc⟩)
      · exact ⟨.pendant a, ha⟩
      · exact ⟨.rest c, hc⟩
end

/-- A side has a first node exactly when it has nodes. -/
theorem Side.toGraph_first_eq_none_iff : (S : Side X) → (S.toGraph.first = none ↔ S.nodes = [])
  | .hyb _ => iff_of_true rfl rfl
  | .node _ _ _ _ => iff_of_false (by simp [Side.toGraph, SideGraph.node]) (by simp [Side.nodes])

end Phylogenetics
