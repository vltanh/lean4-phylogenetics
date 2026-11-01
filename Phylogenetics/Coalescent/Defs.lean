module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.Instances.Matrix

/-!
# Kingman's coalescent on forests: definitions

A rooted *forest* of gene lineages `L` is the set of its clusters, a `Finset (Finset L)`; its *roots*
are its maximal clusters. Kingman's coalescent on forests is the continuous-time Markov chain in which
each pair of roots merges at rate `1`. Its transition probabilities over a time `t`, in coalescent
units, are the matrix exponential `exp (t • Q)` of its generator `Q`; over an infinite time (the
population above the root of a species tree or network) they are the limits as `t → ∞`.

* `roots F`, `kingmanGenerator`, `kingmanTransition t`, `kingmanAbsorption`.
* `forestBelow F A`: the part of the forest `F` below its roots in `A`.
* `sampledForest s A`: the singleton clusters of the lineages sampled from the taxa in `A`;
  `singletonForest n`: the forest of `n` uncoalesced lineages.
* `coalescenceProb i j t`: the `g_ij(t)` of Allman, Degnan and Rhodes (2011, Section 3), the
  probability that `i` lineages coalesce into `j` lineages within time `t`.

[E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862]

The theory is in the other modules of `Phylogenetics.Coalescent`. No species tree or network appears
here.
-/

@[expose] public section

namespace Phylogenetics

open Finset

section Kingman

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The roots of a forest `F`: its maximal clusters. -/
def roots (F : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

/-- The generator of Kingman's coalescent on forests. From a forest `F` with `k` roots, each of
the `k.choose 2` pairs of distinct roots `A, B` merges at rate `1`; the merge adds the cluster
`A ∪ B` to `F`. -/
noncomputable def kingmanGenerator : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if G = F then -((#(roots F)).choose 2 : ℝ)
    else if ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ G = insert (A ∪ B) F then 1 else 0

/-- The transition probabilities of Kingman's coalescent on forests over a time `t`, in
coalescent units: the matrix exponential `exp (t • Q)` of the generator. -/
noncomputable def kingmanTransition (t : ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  NormedSpace.exp (t • kingmanGenerator)

/-- The transition probabilities of Kingman's coalescent on forests over an infinite time: the
entrywise limits of `kingmanTransition t` as `t → ∞`. -/
noncomputable def kingmanAbsorption : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => Filter.limUnder Filter.atTop fun t : ℝ => kingmanTransition t F G

/-- The part of the forest `F` below its roots in `A`: the clusters contained in a member of
`A`. -/
def forestBelow (F A : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun B => ∃ C ∈ A, B ⊆ C

end Kingman

section Sampling

variable {X : Type*} [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The forest of singleton clusters `{l}` of the lineages `l` sampled from the taxa in `A` (at an
internal cluster these singletons already belong to the forests of its children). -/
def sampledForest (s : L → X) (A : Finset X) : Finset (Finset L) :=
  (univ.filter fun l => s l ∈ A).image fun l => {l}

end Sampling

/-- The forest of `n` singleton lineages `{0}, …, {n - 1}`. -/
def singletonForest (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.image fun l => {l}

/-- The `g_ij(t)` of Allman, Degnan and Rhodes (2011, Section 3): the probability that `i` lineages
coalesce into `j` lineages within time `t` under Kingman's coalescent, that is, that the forest
reached from `i` singletons after time `t` has `j` roots. -/
noncomputable def coalescenceProb (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ G : Finset (Finset (Fin i)), if #(roots G) = j then kingmanTransition t (singletonForest i) G
    else 0

end Phylogenetics
