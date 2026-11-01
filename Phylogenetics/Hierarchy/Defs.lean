module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Hierarchies: definitions

A rooted tree on a finite set `X` is identified with its *hierarchy*: the set of its clusters, the
sets of leaves below its nodes. An unrooted tree is identified with the set of sides of its splits.

* `IsHierarchy H`: `H` is a hierarchy of clusters on `X`; `IsBinaryHierarchy H`: a binary one.
* `childClusters H A`: the children of a cluster `A` of `H`.
* `unroot G`: the unrooted tree of a rooted tree (or forest) `G`, as the sides of its splits.
* `restrictClusters S H`, `restrictSplits S T`: the induced rooted and unrooted trees on the taxa
  `S`, viewed on the subtype `S`.
* `geneTreeDisplays G a b c e`: whether the rooted tree `G` displays the quartet `ab|ce`.

The theory is in `Phylogenetics.Hierarchy.Basic`.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A hierarchy of clusters on `X`: a rooted tree on `X` given by its clusters. It contains `X` and
every singleton, its clusters are nonempty, and any two of them are nested or disjoint. -/
def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- The children of a cluster `A` in a family `H` of clusters: the maximal members of `H`
strictly contained in `A`. -/
def childClusters (H : Finset (Finset X)) (A : Finset X) : Finset (Finset X) :=
  H.filter fun B => B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A

/-- The unrooted tree of a rooted tree (or of a rooted forest) `G`: the sides of the splits
induced by its non-root clusters. -/
def unroot {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Finset (Finset L) :=
  G.erase univ ∪ (G.erase univ).image compl

/-- A rooted binary tree on the leaves `L`, given by its clusters: a hierarchy in which every
cluster with at least two leaves is the union of two disjoint clusters. See
`isBinaryHierarchy_iff_card_childClusters`: equivalently, every such cluster has exactly two
children. -/
def IsBinaryHierarchy {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Prop :=
  IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A

/-- The clusters of `H` that meet `S`, restricted to `S`, as clusters on the subtype `S`. -/
def restrictClusters (S : Finset X) (H : Finset (Finset X)) : Finset (Finset S) :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

/-- The induced unrooted tree `T(S)` of an unrooted tree `T` (given by the sides of its splits):
the splits of `T` whose two sides both meet `S`, restricted to `S`. -/
def restrictSplits (S : Finset X) (T : Finset (Finset X)) : Finset (Finset S) :=
  (T.filter fun A => (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty).image fun A => A.subtype (· ∈ S)

/-- Whether the rooted gene tree `G` (given by its clusters, whose elements are taxa) displays the
quartet `ab|ce`, for distinct taxa `a, b, c, e` that are leaves of `G`: whether the tree that it
induces on `a, b, c, e` has the split `ab|ce`, that is, whether some cluster of `G` contains `a`
and `b` but neither `c` nor `e`, or contains `c` and `e` but neither `a` nor `b`. -/
def geneTreeDisplays (G : Finset (Finset X)) (a b c e : X) : Bool :=
  decide (∃ C ∈ G, (a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C) ∨ (c ∈ C ∧ e ∈ C ∧ a ∉ C ∧ b ∉ C))

end Phylogenetics
