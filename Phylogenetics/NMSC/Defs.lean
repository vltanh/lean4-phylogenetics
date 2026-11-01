module

public import Phylogenetics.Coalescent.Defs
public import Phylogenetics.Network.Quartets
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Instances.Matrix

/-!
# The network multispecies coalescent on arbitrary networks: definitions

The network multispecies coalescent (NMSC) on `Phylogenetics.RootedNetwork`, with an inheritance
correlation `ρ`: `ρ = 0` is independent inheritance and `ρ = 1` common inheritance. It uses one lineage
per taxon. It is written as a product over vertices and arcs of the joint law of the forests at the
bottom and the top of every arc, summed over all such histories, so that it mentions no processing
order.

* `allocationWeight`: the Pólya urn law of the parents that the lineages take at a reticulation.
* `arrivingForest`, `allocationFactor`, `historyWeight`: a history and its weight.
* `geneTreeDist N θ ρ`: the distribution of rooted gene trees; `nmscCF N θ ρ s`: the quartet concordance
  factor of the quartet tree `s`.
* `geneCount`, `IsGeneTreeSample`: samples of gene trees.
* `RootedNetwork.IsGenericNull`: null sets of the numerical parameters.

The level-1 version on network terms, with independent inheritance, is `Phylogenetics.NMSC.Level1`.

## References

* Y. Yu, J. H. Degnan, L. Nakhleh, *The probability of a gene tree topology within a phylogenetic network
  with applications to hybridization detection*, PLoS Genet. 8 (2012), e1002660.
* J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of
  blobs reconstruction under the network multispecies coalescent*, Genome Res., doi
  10.1101/gr.282203.126: the inheritance correlation.
-/

@[expose] public noncomputable section

open Finset MeasureTheory
open scoped Classical

namespace Phylogenetics

section Allocation

/-- The probability that the lineages `R` choose the parents `a` at a reticulation with inheritance
probabilities `γ` and inheritance correlation `ρ` (Dai, Han, Molloy 2026, Supplement, Section 1.2): the Pólya urn in which
the first lineage draws from `γ` and the lineage after `i` others takes a given parent with weight
`((1 - ρ) γ_e + ρ n_e) / ((1 - ρ) + ρ i)`, `n_e` being the number of earlier lineages that took it.
This closed form does not depend on the order of the lineages and holds at `ρ = 1` too; it is
`∏ γ_{a r}` at `ρ = 0`, and at `ρ = 1` it vanishes unless all lineages take one parent `e`, when it
is `γ_e` (`Phylogenetics.NMSC.Inheritance`). -/
def allocationWeight {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P] (ρ : ℝ) (γ : P → ℝ)
    (a : R → P) : ℝ :=
  (1 - ρ) ^ ((univ.image a).card - 1) *
    (∏ e ∈ univ.image a,
      (γ e * ∏ j ∈ Ico 1 (univ.filter fun r => a r = e).card, ((1 - ρ) * γ e + ρ * j))) /
    ∏ i ∈ Ico 1 (Fintype.card R), ((1 - ρ) + ρ * i)

end Allocation

section NMSC

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable (N : RootedNetwork V E X) (θ : RootedNetwork.MetricData E) (ρ : ℝ)

/-- The forest arriving at the vertex `v` from below, given the forests `top e` at the top of its
child arcs: the singleton lineage of the taxon labelling `v`, if any, and those forests. -/
def arrivingForest (top : E → Finset (Finset X)) (v : V) : Finset (Finset X) :=
  ((univ.filter fun x => N.leaf x = v).image fun x => ({x} : Finset X)) ∪
    (univ.filter fun e => N.graph.source e = v).biUnion top

/-- The probability that the roots of the forest `F` arriving at `v` choose the parents that put the
forests `bot e` at the bottom of the arcs `e` entering `v`. -/
def allocationFactor (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) : ℝ :=
  ∑ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
    if ∀ e : {e // N.graph.target e = v},
        bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) then
      allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a
    else 0

/-- The joint probability of a history of the network multispecies coalescent: the forests `bot e`
at the bottom and `top e` at the top of every arc. Going up from the taxa, the roots of the forest
arriving at each non-root vertex choose parents, and along each arc the lineages coalesce by Kingman's
coalescent for the length of the arc, independently given the bottoms. -/
def historyWeight (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ univ.erase N.root, allocationFactor N θ ρ (arrivingForest N top v) v bot) *
    ∏ e, kingmanTransition (θ.length e) (bot e) (top e)

/-- The distribution of rooted gene trees on `X` (given by their clusters) under the network
multispecies coalescent with inheritance correlation `ρ`: the forest arriving at the root coalesces
in the population above the root, of infinite length. -/
def geneTreeDist (G : Finset (Finset X)) : ℝ :=
  ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    historyWeight N θ ρ bot top * kingmanAbsorption (arrivingForest N top N.root) G

/-- The quartet concordance factor of the quartet tree `s` under the network multispecies
coalescent: the probability that a gene tree displays `s`. -/
def nmscCF (s : QuartetTree X) : ℝ :=
  ∑ G : Finset (Finset X), if Displays (unroot G) s then geneTreeDist N θ ρ G else 0

/-- The number of the first `k` gene trees of the sequence `G` that display `s`. -/
def geneCount {Ω : Type*} (G : ℕ → Ω → Finset (Finset X)) (k : ℕ) (ω : Ω) (s : QuartetTree X) : ℝ :=
  ((Finset.range k).filter fun i => Displays (unroot (G i ω)) s).card

/-- A sequence of independent gene trees, each from the network multispecies coalescent. -/
structure IsGeneTreeSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : ℕ → Ω → Finset (Finset X)) : Prop where
  /-- The gene trees are measurable. -/
  measurable : ∀ i g, MeasurableSet (G i ⁻¹' {g})
  /-- The gene trees are independent. -/
  indep : ∀ (s : Finset ℕ) (g : ℕ → Finset (Finset X)),
    P (⋂ i ∈ s, G i ⁻¹' {g i}) = ∏ i ∈ s, P (G i ⁻¹' {g i})
  /-- Each gene tree has the law of the network multispecies coalescent. -/
  law : ∀ i g, P.real (G i ⁻¹' {g}) = geneTreeDist N θ ρ g

/-- A set of numerical parameters of a network is null: in the coordinates given by all edge lengths
and, at each hybrid vertex, the inheritance probability of all but one parent, for Lebesgue measure. The
inheritance coordinates of tree arcs and left-out parents are dummies: the set is a cylinder over them,
so it is null exactly when its base is. -/
def RootedNetwork.IsGenericNull (A : Set (RootedNetwork.MetricData E)) : Prop :=
  ∀ d : V → E, (∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) →
    ((Measure.pi fun _ : E => (volume : Measure ℝ)).prod (Measure.pi fun _ : E => (volume : Measure ℝ)))
      {x | ∃ θ ∈ A, N.IsMetric θ ∧ θ.length = x.1 ∧
        ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e} = 0

end NMSC

end Phylogenetics
