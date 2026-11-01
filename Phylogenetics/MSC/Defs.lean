module

public import Phylogenetics.Coalescent.Defs
public import Phylogenetics.Hierarchy.SpeciesTree

/-!
# The multispecies coalescent: definitions

The multispecies coalescent model on a species tree, and the distributions of rooted and unrooted
gene tree topologies that it induces.

## Conventions

* Taxa form a finite type `X`; gene lineages form a finite type `L`, and a sampling map
  `s : L → X` says from which taxon each lineage is sampled. With one lineage per taxon, `L = X`
  and `s = id`.
* A rooted tree on a finite set is identified with its set of clusters
  (`Phylogenetics.Hierarchy.Defs`); a rooted *forest* of gene lineages is likewise a
  `Finset (Finset L)` (`Phylogenetics.Coalescent.Defs`).
* An unrooted tree is identified with the set of sides of its splits: `unroot G` consists of
  every non-root cluster of `G` and its complement. Trivial splits are included.
* The multispecies coalescent: the forest entering the population above a cluster `A` is the
  union of the forests leaving the populations of the children of `A` (independent of each
  other), together with the singletons of the lineages sampled at `A`; the forest leaving the
  population is obtained by running Kingman's coalescent for the length of the edge above `A`.

## Main definitions

* `forestDist H len s A G`: the forest leaving the population above the cluster `A`.
* `SpeciesTree.rootedDist σ s`, `SpeciesTree.unrootedDist σ s`: the gene tree distributions.
* `SpeciesTree.rootedTripleProb σ a b c`: the probability that the rooted gene tree displays the
  rooted triple `ab|c`.
-/

@[expose] public section

namespace Phylogenetics

open Finset

section MultispeciesCoalescent

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The population on the edge above the cluster `A`: Kingman's coalescent runs for the time
`len A`, or, above the root `A = univ`, for an infinite time. -/
noncomputable def populationKernel (len : Finset X → ℝ) (A : Finset X) :
    Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  if A = univ then kingmanAbsorption else kingmanTransition (len A)

/-- The multispecies coalescent on the species tree with clusters `H` and edge lengths `len`,
with lineages sampled according to `s : L → X`: `forestDist H len s A G` is the probability that
the forest of gene lineages leaving the population above the cluster `A` (at its ancient end) is
`G`. The forests leaving the populations of the children of `A` are independent; their union,
together with the singletons of the lineages sampled at `A`, enters the population above `A`. -/
noncomputable def forestDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    (∏ B : childClusters H A, forestDist H len s B (f B)) *
      populationKernel len A (univ.sup f ∪ sampledForest s A) G
termination_by #A
decreasing_by exact card_lt_card (mem_filter.1 B.2).2.1

namespace SpeciesTree

/-- The distribution of rooted gene trees (topologies, given by their clusters) under the
multispecies coalescent on `σ`, with lineages sampled according to `s : L → X`. -/
noncomputable def rootedDist (σ : SpeciesTree X) (s : L → X) (G : Finset (Finset L)) : ℝ :=
  forestDist σ.clusters σ.length s univ G

/-- The distribution of unrooted gene tree topologies under the multispecies coalescent on `σ`,
with lineages sampled according to `s`: the probability of an unrooted tree `T` is the sum of the
probabilities of its rooted versions. -/
noncomputable def unrootedDist (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then σ.rootedDist s G else 0

/-- The probability that the rooted gene tree (one lineage per taxon) displays the rooted triple
`ab|c`, that is, has a cluster containing `a` and `b` but not `c`. -/
noncomputable def rootedTripleProb (σ : SpeciesTree X) (a b c : X) : ℝ :=
  ∑ G, if ∃ C ∈ G, a ∈ C ∧ b ∈ C ∧ c ∉ C then σ.rootedDist id G else 0

end SpeciesTree

end MultispeciesCoalescent

end Phylogenetics
