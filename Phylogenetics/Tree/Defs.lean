module

public import Phylogenetics.Hierarchy.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card

/-!
# Unrooted trees as split families, and quartet trees: definitions

An unrooted tree on the taxa `X` is the family of the sides of its splits, pendant edges included. A
resolved quartet tree `ab|cd` is the unordered pair of its two cherries.

* `IsUnrootedTree`, `IsBinaryTree`, `IsResolutionOf`.
* `QuartetTree X`, with `QuartetTree.taxa` and `QuartetTree.alternatives`; `treesOn q`: the three
  resolved quartet trees on the four taxa `q`.
* `Displays T s`: the tree `T` displays the quartet tree `s`.
* `quartetSupport w T`, `IsWQCOptimal`: the Maximum Quartet Support objective and its optima.
* `contractSides`, `internalSides`, `bipartitionQuartets`, `multipartitionQuartets`.
* `Separated`, `quartetDistance`: the quartet intertaxon distance of Rhodes (2020).
* `IsUniformOn`, `IsT1Strict`: patterns of concordance factors (Allman et al.
  2023).
* `quartetCount`, `displayCF`: the number and the probability of gene trees displaying a quartet tree.

The theory is in `Phylogenetics.Tree.Splits`. That these families are the sides of the splits of actual
graphs is in `Phylogenetics.Network.OfHierarchy` and `Phylogenetics.Network.CutHierarchy`.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
* J. A. Rhodes, *Topological metrizations of trees, and new quartet methods of tree inference*,
  IEEE/ACM Trans. Comput. Biol. Bioinform. 17 (2020) 2107–2118.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

section Trees

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- An unrooted phylogenetic tree on `X`, given by the sides of its splits (pendant edges
included). -/
def IsUnrootedTree (T : Finset (Finset X)) : Prop :=
  ∃ H : Finset (Finset X), IsHierarchy H ∧ unroot H = T

/-- A binary unrooted tree: it has a binary rooting, in which every cluster with at least two taxa
has exactly two children. -/
def IsBinaryTree (T : Finset (Finset X)) : Prop :=
  ∃ H : Finset (Finset X), IsHierarchy H ∧ unroot H = T ∧
    ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2

/-- `T` is a resolution of `T'`: an unrooted tree from which `T'` is obtained by contracting edges,
that is, by removing splits. It may be nonbinary. -/
def IsResolutionOf (T T' : Finset (Finset X)) : Prop := IsUnrootedTree T ∧ T' ⊆ T

/-- A resolved quartet tree `ab|cd`: the unordered pair of its cherries `{a,b}`, `{c,d}`. -/
def IsQuartetTree (s : Finset (Finset X)) : Prop :=
  s.card = 2 ∧ (∀ B ∈ s, B.card = 2) ∧ ∀ B ∈ s, ∀ C ∈ s, B ≠ C → Disjoint B C

/-- The resolved quartet trees on `X`. -/
abbrev QuartetTree (X : Type*) [DecidableEq X] := {s : Finset (Finset X) // IsQuartetTree s}

instance : Fintype (QuartetTree X) := Fintype.ofFinite _

omit [Fintype X] in
/-- The four taxa of a quartet tree. -/
def QuartetTree.taxa (s : QuartetTree X) : Finset X := s.val.sup id

/-- The quartet trees on the same four taxa as `s`, other than `s`: the two alternatives. -/
def QuartetTree.alternatives (s : QuartetTree X) : Finset (QuartetTree X) :=
  univ.filter fun r => r.taxa = s.taxa ∧ r ≠ s

/-- The three resolved quartet trees on a set of four taxa. -/
def treesOn (q : Finset X) : Finset (QuartetTree X) := univ.filter fun r => r.taxa = q

/-- The tree (given by the sides of its splits) displays the quartet tree `ab|cd`: some split
restricts to `ab|cd`. An unresolved quartet on `T` is one with no displayed quartet tree. -/
def Displays (T : Finset (Finset X)) (s : QuartetTree X) : Prop := ∃ A ∈ T, A ∩ s.taxa ∈ s.val

/-- The Maximum Quartet Support objective, or weighted quartet score of `T`: the sum, over the quartet
trees that `T` displays, of the weight `w`. -/
def quartetSupport (w : QuartetTree X → ℝ) (T : Finset (Finset X)) : ℝ :=
  ∑ s, if Displays T s then w s else 0

/-- The family obtained from a tree `T` by contracting the edges with sides in `C`. -/
def contractSides (T C : Finset (Finset X)) : Finset (Finset X) := T.filter fun A => A ∉ C ∧ Aᶜ ∉ C

/-- The sides of the internal edges of `T`: both sides have at least two taxa. -/
def internalSides (T : Finset (Finset X)) : Finset (Finset X) :=
  T.filter fun A => 2 ≤ A.card ∧ 2 ≤ Aᶜ.card

/-- The quartet trees whose two cherries lie on the two sides of the edge with side `A`: the sets of
four taxa around a bipartition, each with the quartet tree that defines the edge on a tree. -/
def bipartitionQuartets (A : Finset X) : Finset (QuartetTree X) :=
  univ.filter fun s => A ∩ s.taxa ∈ s.val

/-- The quartet trees around the edge with side `A` of `T` drawing their taxa from distinct blocks
of the multipartition of `T` at that edge. Two taxa on one side are in one block exactly when a split
of `T` properly inside that side contains both. On a binary `T` these are the quartets of the
quadripartition at the edge. -/
def multipartitionQuartets (T : Finset (Finset X)) (A : Finset X) : Finset (QuartetTree X) :=
  (bipartitionQuartets A).filter fun s =>
    (¬ ∃ C ∈ T, C ⊂ A ∧ A ∩ s.taxa ⊆ C) ∧ (¬ ∃ C ∈ T, C ⊂ Aᶜ ∧ Aᶜ ∩ s.taxa ⊆ C)

/-- An optimal solution of Weighted Quartet Consensus for the weights `c`: a binary tree of largest
quartet support. -/
def IsWQCOptimal (c : QuartetTree X → ℝ) (B : Finset (Finset X)) : Prop :=
  IsBinaryTree B ∧ ∀ T, IsBinaryTree T → quartetSupport c T ≤ quartetSupport c B

/-- Taxa `a`, `e` are separated in the quartet tree `s`: they lie in different cherries. -/
def Separated (s : QuartetTree X) (a e : X) : Prop :=
  a ∈ s.taxa ∧ e ∈ s.taxa ∧ ∀ B ∈ s.val, ¬ (a ∈ B ∧ e ∈ B)

/-- The quartet intertaxon distance of Rhodes (2020, Theorem 2), from a family `Bq` of unresolved 4-taxon
sets and a family `τ` of resolved quartet trees: for `x ≠ y`, `2 |Q_{x,y}| + 2N - 4` where `Q_{x,y}`
holds the unresolved sets containing `x, y` and the quartet trees separating `x, y`. -/
def quartetDistance (Bq : Set (Finset X)) (τ : Set (QuartetTree X)) (x y : X) : ℝ :=
  if x = y then 0 else
    2 * (((univ.filter fun q : Finset X =>
        q.card = 4 ∧ x ∈ q ∧ y ∈ q ∧ (q ∈ Bq ∨ ∃ s ∈ τ, s.taxa = q ∧ Separated s x y)).card : ℕ) : ℝ) +
      2 * (Fintype.card X : ℝ) - 4

/-- All three concordance factors on the taxa `q` are `1/3`: the pattern of a trivial 4-blob. -/
def IsUniformOn (p : QuartetTree X → ℝ) (q : Finset X) : Prop := ∀ r ∈ treesOn q, p r = 1 / 3

/-- The pattern of the T1 model for the quartet tree `s = ab|cd`: `p_ab|cd > p_ac|bd = p_ad|bc`. -/
def IsT1Strict (p : QuartetTree X → ℝ) (s : QuartetTree X) : Prop :=
  (∀ r ∈ s.alternatives, p r < p s) ∧ ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, p r = p r'

end Trees

section Sampling

variable {Γ : Type*} [Fintype Γ] {X : Type*} [Fintype X] [DecidableEq X]

/-- The number of the gene trees `ω`, each given by the sides of its splits through `sides`, that
display the quartet tree `s`. -/
def quartetCount {n : ℕ} (sides : Γ → Finset (Finset X)) (ω : Fin n → Γ) (s : QuartetTree X) : ℝ :=
  ((univ.filter fun i => Displays (sides (ω i)) s).card : ℝ)

/-- The probability that a gene tree displays the quartet tree `s`, for a distribution `dist` on gene
trees given by the sides of their splits through `sides`. -/
def displayCF {Γ : Type*} [Fintype Γ] (dist : Γ → ℝ) (sides : Γ → Finset (Finset X))
    (s : QuartetTree X) : ℝ :=
  ∑ g, if Displays (sides g) s then dist g else 0

end Sampling

end Phylogenetics
