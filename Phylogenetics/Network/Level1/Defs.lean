module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Rooted metric level-1 networks, as terms

* `Phylogenetics.Net X`, `Phylogenetics.Side X`: rooted binary metric level-1 networks, described
  recursively from the root; `Net.leaves`, `Net.subnets`, `Side.nodes`, `Net.IsMetric`,
  `Net.WellFormed`, `Net.taxa`.
* `Net.Cycle N`: a cycle of `N`, with its components in their cyclic order (`Net.Cycle.components`),
  its size and the lengths of its edges.

`Phylogenetics.Network.Level1.Digraph` proves that these terms are exactly the rooted binary metric
level-1 networks given as directed graphs. The network multispecies coalescent on them is in
`Phylogenetics.NMSC.Level1`.
-/

@[expose] public noncomputable section

namespace Phylogenetics

/-! ### Rooted metric level-1 networks -/

universe u

mutual
/-- A rooted binary metric level-1 phylogenetic network on the taxa `X`, described from its root.
Edge lengths are in coalescent units.

In a binary rooted network in which no two cycles share an edge, the root of the network, or of
the subnetwork below a cut edge, is a tree node on no cycle, the *top node* of a cycle (the node
of the cycle whose two cycle edges both leave it), or (for a subnetwork) a leaf; the child edges
of a tree node on no cycle, the pendant edges of the nodes along a cycle and the child edge of the
hybrid node of a cycle are cut edges. The network is therefore described recursively:
* `leaf x`: a leaf labelled `x`;
* `tree ℓ₁ N₁ ℓ₂ N₂`: a tree node on no cycle, with child edges of lengths `ℓ₁` and `ℓ₂` to the
  networks `N₁` and `N₂`;
* `cycle γ S₁ S₂ ℓ N`: the top node `s` of a cycle. The cycle consists of two directed paths `S₁`
  and `S₂` (its *sides*) from `s` to the hybrid node `h` of the cycle; the last edge of `S₁` is a
  hybrid edge with inheritance probability `γ`, the last edge of `S₂` one with `1 - γ`; `h` has a
  child edge of length `ℓ` to the network `N`. -/
inductive Net (X : Type u) where
  | leaf (x : X)
  | tree (ℓ₁ : ℝ) (N₁ : Net X) (ℓ₂ : ℝ) (N₂ : Net X)
  | cycle (γ : ℝ) (S₁ S₂ : Side X) (ℓ : ℝ) (N : Net X)

/-- A side of a cycle: the directed path from the top node of the cycle to its hybrid node,
described from the top.
* `hyb ℓ`: the path is a single hybrid edge, of length `ℓ`;
* `node ℓ b N S`: the path starts with an edge of length `ℓ` to a tree node `u`, which has a pendant
  edge of length `b` to the network `N`; the path continues from `u` along `S`. -/
inductive Side (X : Type u) where
  | hyb (ℓ : ℝ)
  | node (ℓ b : ℝ) (N : Net X) (S : Side X)
end

variable {X : Type u}

mutual
/-- The labels of the leaves of a network. -/
def Net.leaves : Net X → List X
  | .leaf x => [x]
  | .tree _ N₁ _ N₂ => N₁.leaves ++ N₂.leaves
  | .cycle _ S₁ S₂ _ N => S₁.leaves ++ S₂.leaves ++ N.leaves

/-- The labels of the leaves below the nodes of a side. -/
def Side.leaves : Side X → List X
  | .hyb _ => []
  | .node _ _ N S => N.leaves ++ S.leaves
end

mutual
/-- The network itself and its subnetworks below its cut edges (below the child edges of the tree
nodes on no cycle, the pendant edges of the nodes of the sides of a cycle, and the child edge of
the hybrid node of a cycle). -/
def Net.subnets : Net X → List (Net X)
  | .leaf x => [.leaf x]
  | .tree ℓ₁ N₁ ℓ₂ N₂ => .tree ℓ₁ N₁ ℓ₂ N₂ :: (N₁.subnets ++ N₂.subnets)
  | .cycle γ S₁ S₂ ℓ N => .cycle γ S₁ S₂ ℓ N :: (S₁.subnets ++ S₂.subnets ++ N.subnets)

/-- The subnetworks hanging from the nodes of a side, and their subnetworks. -/
def Side.subnets : Side X → List (Net X)
  | .hyb _ => []
  | .node _ _ N S => N.subnets ++ S.subnets
end

/-- The nodes of a side, from the top: for each, the length of the edge above it, the length of its
pendant edge, and the network below the pendant edge. -/
def Side.nodes : Side X → List (ℝ × ℝ × Net X)
  | .hyb _ => []
  | .node ℓ b N S => (ℓ, b, N) :: S.nodes

/-- The length of the hybrid edge at the bottom of a side. -/
def Side.hybLen : Side X → ℝ
  | .hyb ℓ => ℓ
  | .node _ _ _ S => S.hybLen

mutual
/-- A metric network: edge lengths are positive and inheritance probabilities lie in `(0, 1)`;
moreover no cycle has only two edges, since a network is a graph, without parallel edges. -/
def Net.IsMetric : Net X → Prop
  | .leaf _ => True
  | .tree ℓ₁ N₁ ℓ₂ N₂ => 0 < ℓ₁ ∧ 0 < ℓ₂ ∧ N₁.IsMetric ∧ N₂.IsMetric
  | .cycle γ S₁ S₂ ℓ N =>
      0 < γ ∧ γ < 1 ∧ 0 < ℓ ∧ S₁.IsMetric ∧ S₂.IsMetric ∧ N.IsMetric ∧
        (S₁.nodes ≠ [] ∨ S₂.nodes ≠ [])

/-- The edges of a side have positive lengths, and the networks hanging from it are metric. -/
def Side.IsMetric : Side X → Prop
  | .hyb ℓ => 0 < ℓ
  | .node ℓ b N S => 0 < ℓ ∧ 0 < b ∧ N.IsMetric ∧ S.IsMetric
end

/-- A metric level-1 phylogenetic network: metric, with distinct leaf labels. -/
def Net.WellFormed (N : Net X) : Prop := N.IsMetric ∧ N.leaves.Nodup

/-- The taxa of a network: the labels of its leaves. -/
def Net.taxa [DecidableEq X] (N : Net X) : Finset X := N.leaves.toFinset

variable [DecidableEq X]

/-! ### The cycles of a network and their components -/

/-- A cycle `Ω` of the network `N`: the subnetwork
`Ω.top = cycle Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below` below the top node of the cycle occurs in `N`. The
side `side₁` (the side of the component `C₁`) ends with the hybrid edge of inheritance probability
`γ`, the side `side₂` (of `C_{d-1}`) with the hybrid edge of inheritance probability `1 - γ`. -/
structure Net.Cycle (N : Net X) where
  /-- The inheritance probability of the hybrid edge ending the side `side₁`. -/
  γ : ℝ
  /-- The side whose hybrid edge has inheritance probability `γ`. -/
  side₁ : Side X
  /-- The side whose hybrid edge has inheritance probability `1 - γ`. -/
  side₂ : Side X
  /-- The length of the child edge of the hybrid node. -/
  ℓ : ℝ
  /-- The network below the hybrid node. -/
  below : Net X
  mem : Net.cycle γ side₁ side₂ ℓ below ∈ N.subnets

namespace Net.Cycle

variable {N : Net X} (Ω : N.Cycle)

/-- The subnetwork of `N` below the top node of the cycle `Ω`. -/
def top : Net X := .cycle Ω.γ Ω.side₁ Ω.side₂ Ω.ℓ Ω.below

open Classical in
/-- The components `C₀, …, C_{d-1}` of the cycle `Ω` (their sets of taxa) in their cyclic order,
which goes around the cycle of the semi-directed network: the hybrid component `C₀`, below the
hybrid node; the components hanging from the side `side₁`, from the hybrid node up; the component
containing the root of `N`, attached at the top node, unless the root of `N` is the top node of
`Ω` (in the semi-directed network the root is then suppressed, and is not a node of the cycle);
and the components hanging from the side `side₂`, from the top node down. -/
def components : List (Finset X) :=
  [Ω.below.taxa] ++ Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
    (if Ω.top = N then [] else [N.taxa \ Ω.top.taxa]) ++ Ω.side₂.nodes.map (fun n => n.2.2.taxa)

/-- The size `d` of the cycle: its number of components, the number of nodes (and of edges) of the
cycle in the semi-directed network, where the root is suppressed if it is the top node of the
cycle. (Counted in the rooted network, the cycle has `d + 1` nodes when the root is its top node;
a `d`-cycle here always has `d` components.) -/
def size : ℕ := Ω.components.length

/-- The component at position `i` (empty if `i ≥ d`). -/
def component (i : ℕ) : Finset X := Ω.components.getD i ∅

open Classical in
/-- The lengths of the edges of the cycle in the semi-directed network, in the cyclic order: the
edge at index `m` joins the nodes of the components at positions `m` and `m + 1` (indices mod `d`).
If the root of `N` is the top node of `Ω`, the two edges at the root form one edge. -/
def edges : List ℝ :=
  let E := [Ω.side₁.hybLen] ++ Ω.side₁.nodes.reverse.map (fun n => n.1) ++
    Ω.side₂.nodes.map (fun n => n.1) ++ [Ω.side₂.hybLen]
  let p := Ω.side₁.nodes.length
  if Ω.top = N then E.take p ++ [E.getD p 0 + E.getD (p + 1) 0] ++ E.drop (p + 2) else E

/-- The length `w_m` of the edge of the cycle between the nodes of the components at positions `m`
and `m + 1`. -/
def edgeLen (m : ℕ) : ℝ := Ω.edges.getD m 0

end Net.Cycle

/-- A network term has a leaf. -/
theorem Net.leaves_ne_nil {X : Type*} : (N : Net X) → N.leaves ≠ []
  | .leaf _ => by simp [Net.leaves]
  | .tree _ N₁ _ _ => by simp [Net.leaves, N₁.leaves_ne_nil]
  | .cycle _ _ _ _ N => by simp [Net.leaves, N.leaves_ne_nil]

end Phylogenetics
