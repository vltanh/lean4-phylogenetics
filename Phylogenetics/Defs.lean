module

public import Phylogenetics.MSC.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fintype.Powerset
/-!
# Phylogenetic networks, the network multispecies coalescent, quartet CFs

The definitions of the library `Phylogenetics` for networks. The block between the two marker
comments is self-contained, given Mathlib and the block of `Phylogenetics.MSC.Defs`, so that a
project's `Challenge.lean` can copy both verbatim (Comparator needs the same constants in the
Challenge and the Solution); the definitions are in one module because Lean shares the auxiliary
definitions of identical pattern matches within a module.

* Rooted metric level-1 networks (`Phylogenetics.Net`, `Phylogenetics.Side`,
  `Phylogenetics.Net.WellFormed`), their cycles and components (`Phylogenetics.Net.Cycle`),
  Kingman's coalescent on forests (`Phylogenetics.MSC.Defs`) and the network multispecies coalescent
  (NMSC): `Phylogenetics.Net.forestDist`, `Phylogenetics.Net.geneTreeDist`, the quartet concordance
  factors (CFs) `Phylogenetics.Net.quartetCF` and the CFs of the components of a cycle,
  `Phylogenetics.Net.componentCF`; whether a gene tree displays a quartet,
  `Phylogenetics.geneTreeDisplays`.
* The metric `d`-cycle (`Phylogenetics.MetricCycle`) and the quartet CFs of its components given by
  the induced metric quarnets: `Phylogenetics.pathCF`, `Phylogenetics.cycleCF`, and the property
  `Phylogenetics.NMSCQuartetCF` of a family of CFs to be given by them
  (`Phylogenetics.nmsc_quartetCF` proves it for the cycles of a network).
* Cyclic orders up to rotation and reversal (`Phylogenetics.SameCyclicOrder`).
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace Phylogenetics

-- BEGIN PHYLO DEFINITIONS

/-! ### Rooted metric level-1 networks -/

section Networks

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

/-! ### Kingman's coalescent and the network multispecies coalescent

Kingman's coalescent on forests of gene lineages is defined in `Phylogenetics.MSC.Defs`
(`Phylogenetics.kingmanTransition`, `Phylogenetics.kingmanAbsorption`): a forest of rooted gene
trees on the lineages `L` is the set of its clusters, a `Finset (Finset L)`; its roots are its
maximal clusters. -/

section NetworkCoalescent

variable {L : Type*} [Fintype L] [DecidableEq L]

variable [DecidableEq X]

/-- The forest of the singleton clusters `{l}` of the gene lineages `l` sampled from the taxon `x`
(lineage `l` is sampled from the taxon `s l`). -/
def sampledAt (s : L → X) (x : X) : Finset (Finset L) :=
  (univ.filter fun l => s l = x).image fun l => {l}

/-- The distribution of the union of two independent random forests with distributions `μ` and
`ν` (on disjoint sets of lineages). -/
def forestUnion (μ ν : Finset (Finset L) → ℝ) (G : Finset (Finset L)) : ℝ :=
  ∑ F, ∑ F', if F ∪ F' = G then μ F * ν F' else 0

/-- The part of the forest `F` below its roots in `A`: the clusters contained in a member of
`A`. -/
def forestBelow (F A : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun B => ∃ C ∈ A, B ⊆ C

mutual
/-- The network multispecies coalescent (NMSC; Nakhleh 2011, Yu et al. 2012), with gene lineages
`L` sampled from the taxa by `s : L → X`: `N.forestDist s G` is the probability that `G` is the
forest of gene lineages at the root of `N` (as it enters the edge above the root, or the
population above the root of the whole network). Going up from the leaves:
* a leaf `x` holds the singletons of the lineages sampled from `x`;
* along an edge of length `t` the lineages coalesce by Kingman's coalescent for the time `t`;
* the lineages arriving at a tree node from its two child edges, independent, form one forest;
* at the hybrid node of a cycle, each lineage (a root of the forest arriving from below), with its
  subtree, independently takes the hybrid edge of the side `S₁` with probability `γ` and that of
  `S₂` with probability `1 - γ`; the two forests then travel up the two sides (`Side.forestDist`),
  independently, and form one forest at the top node of the cycle. -/
noncomputable def Net.forestDist (s : L → X) : Net X → Finset (Finset L) → ℝ
  | .leaf x => fun G => if G = sampledAt s x then 1 else 0
  | .tree ℓ₁ N₁ ℓ₂ N₂ =>
      forestUnion (N₁.forestDist s ᵥ* kingmanTransition ℓ₁)
        (N₂.forestDist s ᵥ* kingmanTransition ℓ₂)
  | .cycle γ S₁ S₂ ℓ N => fun G =>
      ∑ F, (N.forestDist s ᵥ* kingmanTransition ℓ) F *
        ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A))) G

/-- The NMSC along a side of a cycle: `S.forestDist s F G` is the probability that `G` is the
forest of gene lineages arriving at the top node of the cycle along the side `S`, when the forest
`F` takes the hybrid edge at the bottom of `S` (for a part `S` of a side: the probability of the
forest arriving at the upper end of the first edge of `S`). At each node of the side, the lineages
arriving from below along the side and those arriving along the pendant edge form one forest. -/
noncomputable def Side.forestDist (s : L → X) : Side X → Finset (Finset L) → Finset (Finset L) → ℝ
  | .hyb ℓ => fun F => kingmanTransition ℓ F
  | .node ℓ b N S => fun F =>
      forestUnion (S.forestDist s F) (N.forestDist s ᵥ* kingmanTransition b) ᵥ* kingmanTransition ℓ
end

/-- The distribution of rooted gene trees under the NMSC on `N` (given by their clusters): the
forest at the root of `N` enters the population above the root, of infinite length, where its
lineages coalesce into a single tree. -/
noncomputable def Net.geneTreeDist (N : Net X) (s : L → X) : Finset (Finset L) → ℝ :=
  N.forestDist s ᵥ* kingmanAbsorption

end NetworkCoalescent

variable [DecidableEq X]

/-- The quartet concordance factor `CF(ab|ce)` of the taxa `a, b, c, e` under the NMSC on `N`: one
gene lineage is sampled from each taxon (the lineages `0, 1, 2, 3` of `Fin 4`), and `CF(ab|ce)` is
the probability that the unrooted gene tree displays the quartet `ab|ce`, that is, has the split
`{0, 1} | {2, 3}`. (A gene tree on all the taxa gives the same CF: by the sampling consistency of
the coalescent, the gene tree that it induces on `a, b, c, e` has the distribution of the gene tree
of these four lineages, which this definition uses; see the theorem `quartetCF_eq_displays`.) -/
noncomputable def Net.quartetCF (N : Net X) (a b c e : X) : ℝ :=
  ∑ G, if ({0, 1} : Finset (Fin 4)) ∈ unroot G then N.geneTreeDist ![a, b, c, e] G else 0

/-- The component CFs `CF(C_a C_b | C_c C_e)` of a cycle, for a choice of one taxon `x i` in each
component `C_i` of the cycle (components labelled by `Fin d`): the quartet CFs of the chosen
taxa. -/
noncomputable def Net.componentCF {d : ℕ} (N : Net X) (x : Fin d → X) (a b c e : Fin d) : ℝ :=
  N.quartetCF (x a) (x b) (x c) (x e)

/-- Whether the rooted gene tree `G` (given by its clusters, whose elements are taxa) displays the
quartet `ab|ce`, for distinct taxa `a, b, c, e` that are leaves of `G`: whether the tree that it
induces on `a, b, c, e` has the split `ab|ce`, that is, whether some cluster of `G` contains `a`
and `b` but neither `c` nor `e`, or contains `c` and `e` but neither `a` nor `b`. -/
def geneTreeDisplays (G : Finset (Finset X)) (a b c e : X) : Bool :=
  decide (∃ C ∈ G, (a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C) ∨ (c ∈ C ∧ e ∈ C ∧ a ∉ C ∧ b ∉ C))

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

end Networks

/-! ### The metric cycle and the quartet concordance factors of its components -/

/-- A metric `d`-cycle `Ω` of a level-1 phylogenetic network. Its components `C₀, …, C_{d-1}` are
numbered by their positions in the cyclic order around the cycle: `C₀` is the hybrid component,
and `C₁` and `C_{d-1}` are its neighbours. `γ` is the inheritance probability of the hybrid edge
on the side of `C₁` (the other hybrid edge has `1 - γ`). For `1 ≤ m ≤ d - 2`, `w m` is the length,
in coalescent units, of the edge of the cycle between the nodes where `C_m` and `C_{m+1}` attach;
the values of `w` outside this range are never used. -/
structure MetricCycle (d : ℕ) where
  /-- The inheritance probability of the hybrid edge on the side of `C₁`. -/
  γ : ℝ
  /-- The edge lengths `w₁, …, w_{d-2}` of the cycle. -/
  w : ℕ → ℝ
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  w_pos : ∀ m, 1 ≤ m → m ≤ d - 2 → 0 < w m

/-- The length `w_a + ⋯ + w_{b-1}` of the path of the cycle between the nodes at positions
`a ≤ b`. -/
def pathLen (w : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ m ∈ Finset.Ico a b, w m

/-- The quartet CF of a metric quartet tree whose four taxa hang from a path at the distinct
positions `a, b, c, e`: the tree separates the two smallest positions from the two largest, and
its internal edge is the part of the path between the two middle positions, of length `t`. Under
the multispecies coalescent the gene tree displays `ab|ce` with probability `1 - (2/3) e^{-t}` if
`ab|ce` is the split of the tree, and `(1/3) e^{-t}` otherwise (see Allman, Degnan and Rhodes 2011,
Section 4.1). The two middle positions are `max (min a b) (min c e)` and `min (max a b) (max c e)`,
in some order. -/
def pathCF (w : ℕ → ℝ) (a b c e : ℕ) : ℝ :=
  let t := pathLen w (min (max (min a b) (min c e)) (min (max a b) (max c e)))
    (max (max (min a b) (min c e)) (min (max a b) (max c e)))
  if max a b < min c e ∨ max c e < min a b then 1 - 2 / 3 * Real.exp (-t) else 1 / 3 * Real.exp (-t)

/-- In the displayed tree in which the lineage of the hybrid component `C₀` takes the hybrid edge
on the side of `C_{d-1}`, the component `C₀` hangs next to `C_{d-1}`: position `0` moves to `d`. -/
def toRightEnd (d a : ℕ) : ℕ := if a = 0 then d else a

/-- The quartet CF `CF(C_a C_b | C_c C_e)` of the components at the distinct positions
`a, b, c, e` of the metric cycle `Ω` under the NMSC, which is the CF of the induced metric quarnet
(Baños 2019):
* if `0 ∉ {a, b, c, e}`, the induced quarnet is a tree, obtained by opening the cycle at the
  hybrid node: the components hang from the path `C₁ — C₂ — ⋯ — C_{d-1}`;
* otherwise it is a network quarnet; the lineage of `C₀` takes the hybrid edge on the side of
  `C₁` with probability `γ`, and the gene tree then follows the displayed tree in which `C₀`
  hangs next to `C₁` (position `0`), or it takes the other hybrid edge, with probability `1 - γ`,
  and `C₀` hangs next to `C_{d-1}` (position `d`). -/
def cycleCF {d : ℕ} (Ω : MetricCycle d) (a b c e : ℕ) : ℝ :=
  if a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0 then
    Ω.γ * pathCF Ω.w a b c e +
      (1 - Ω.γ) * pathCF Ω.w (toRightEnd d a) (toRightEnd d b) (toRightEnd d c) (toRightEnd d e)
  else pathCF Ω.w a b c e

/-- The component CFs `CF` of a metric cycle are those of its induced metric quarnets. The
components carry arbitrary labels `0, …, d-1`; the component at position `i` of the cyclic order
around the cycle has label `ord i`. `CF a b c e` stands for the component CF
`CF(C_a C_b | C_c C_e)`, and the property is that, for distinct components, it is the CF of the
induced metric quarnet, `Phylogenetics.cycleCF` (the induced quarnets, and the dependence of
quartet CFs on them only, are Baños 2019; the quartet-tree CFs are those of the multispecies
coalescent, see Allman, Degnan and Rhodes 2011, Section 4.1). The theorem `nmsc_quartetCF` proves
it for the component CFs of every cycle of a metric level-1 network under the network multispecies
coalescent. -/
def NMSCQuartetCF {d : ℕ} (Ω : MetricCycle d) (ord : Equiv.Perm (Fin d))
    (CF : Fin d → Fin d → Fin d → Fin d → ℝ) : Prop :=
  ∀ a b c e : Fin d, a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
    CF a b c e = cycleCF Ω (ord.symm a) (ord.symm b) (ord.symm c) (ord.symm e)

/-! ### Cyclic orders -/

/-- The cyclic orderings `σ` and `ord` of the labels are the same up to rotation and reversal:
`σ k` is the label at position `k` of `σ`, as `ord k` is in `ord`. -/
def SameCyclicOrder {d : ℕ} (σ ord : Equiv.Perm (Fin d)) : Prop :=
  ∃ r : Fin d, (∀ k, σ k = ord (k + r)) ∨ (∀ k, σ k = ord (r - k))

-- END PHYLO DEFINITIONS

/-- A network term has a leaf. -/
theorem Net.leaves_ne_nil {X : Type*} : (N : Net X) → N.leaves ≠ []
  | .leaf _ => by simp [Net.leaves]
  | .tree _ N₁ _ _ => by simp [Net.leaves, N₁.leaves_ne_nil]
  | .cycle _ _ _ _ N => by simp [Net.leaves, N.leaves_ne_nil]

end Phylogenetics
