module

public import Phylogenetics.Coalescent.Defs
public import Phylogenetics.Hierarchy.Defs
public import Phylogenetics.Network.Level1.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Fintype.Powerset

/-!
# The network multispecies coalescent on level-1 networks: definitions

* The network multispecies coalescent (NMSC) on the terms `Phylogenetics.Net`, with independent
  inheritance: `Phylogenetics.Net.forestDist`, `Phylogenetics.Net.geneTreeDist`, the quartet
  concordance factors (CFs) `Phylogenetics.Net.quartetCF` and the CFs of the components of a cycle,
  `Phylogenetics.Net.componentCF`.
* The metric `d`-cycle (`Phylogenetics.MetricCycle`) and the quartet CFs of its components given by
  the induced metric quarnets: `Phylogenetics.pathCF`, `Phylogenetics.cycleCF`, and the property
  `Phylogenetics.NMSCQuartetCF` of a family of CFs to be given by them
  (`Phylogenetics.nmsc_quartetCF` proves it for the cycles of a network).

The NMSC on general networks, with correlated inheritance, is in `Phylogenetics.NMSC`.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace Phylogenetics

universe u

variable {X : Type u}

/-! ### Kingman's coalescent and the network multispecies coalescent

Kingman's coalescent on forests of gene lineages is defined in `Phylogenetics.Coalescent.Defs`
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

end Phylogenetics
