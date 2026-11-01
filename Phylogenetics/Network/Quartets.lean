module

public import Phylogenetics.Graph.Blobs
public import Phylogenetics.Network.Defs
public import Phylogenetics.Tree.Defs

/-!
# The tree of blobs and the quartets of a network: definitions

* `treeOfBlobs N`: the tree of blobs of `N`, given by the sides of its splits.
* `InducedCutSplit`, `IsTreelike`, `HasTrivialFourBlob`, `IsBQuartet`: what a network does on a set of
  four taxa.
* `CutExchangeable`: exchangeability of taxa across a cut edge.
* `RootedNetwork.IsLevelOne`: the level of a network, through its blobs.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a
  species network under the coalescent model*, Algorithms Mol. Biol. 19 (2024), 23.
* C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies
  coalescent: theory and prevalence*, J. Math. Biol. 88 (2024), 29.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

section NetworkQuartets

variable {V E X : Type*} [Fintype X] [DecidableEq X] (N : RootedNetwork V E X)

/-- The (reduced unrooted) tree of blobs `T_B(N)`, given by the sides of its splits: the nonempty
proper taxon sides of the cut edges of `N`. `Phylogenetics.Network.TreeOfBlobs` proves that contracting
the blobs of `N` and suppressing degree-two vertices gives a tree with exactly these splits. -/
def treeOfBlobs : Finset (Finset X) :=
  univ.filter fun A => A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X)

/-- The quartet tree `s = ab|cd` is a cut-edge split of the network induced on its four taxa. -/
def InducedCutSplit (s : QuartetTree X) : Prop :=
  ∃ B ∈ s.val, N.HasCutSplitOn (s.taxa : Set X) (B : Set X)

/-- The network induced on the taxa `q` has a nontrivial cut-edge split: it is *treelike*, and has no
4-blob. -/
def IsTreelike (q : Finset X) : Prop :=
  ∃ s ∈ treesOn q, InducedCutSplit N s

/-- The network induced on `q` has a trivial 4-blob, a multifurcation: there is a vertex `v` with,
for each taxon `x` of `q`, a cut edge of the induced subgraph at `v` separating exactly `x`
from `v`. Chains of 2-blobs may lead to the taxa, and `v` lies on no cycle below the least stable
ancestor of `q`: a vertex of a non-trivial blob of the induced semidirected network is not a trivial
4-blob. A cycle above `v` is possible when `v` is that ancestor, since the induced semidirected network
omits it. -/
def HasTrivialFourBlob (q : Finset X) : Prop :=
  ∃ v : V, ∀ x ∈ q, ∃ e ∈ N.ancestralArcs (q : Set X), ∃ S : Set V,
    (∀ f ∈ N.ancestralArcs (q : Set X), N.graph.Crosses f S ↔ f = e) ∧
    (∀ y ∈ q, N.leaf y ∈ S ↔ y = x) ∧ v ∉ S ∧ (N.graph.source e = v ∨ N.graph.target e = v)

/-- Exchangeability of taxa across a cut edge (Ané et al. 2024): replacing a taxon `a` of a quartet
tree `s` by a taxon `a'` that a cut edge groups with it, away from the other three taxa, does not
change the weight. The network multispecies coalescent has this property
(`Phylogenetics.NMSC.exchangeability`). -/
def CutExchangeable (p : QuartetTree X → ℝ) : Prop :=
  ∀ (s s' : QuartetTree X) (a a' : X), a ∈ s.taxa → a' ∉ s.taxa →
    s'.val = s.val.image (fun B => if a ∈ B then insert a' (B.erase a) else B) →
    (∃ A : Finset X, N.HasCutSplit (A : Set X) ∧ a ∈ A ∧ a' ∈ A ∧ Disjoint A (s.taxa.erase a)) →
    p s = p s'

/-- The taxa `q` form a B-quartet of the network (Allman, Baños, Mitchell, Rhodes 2024, Definition 4): the tree of blobs does not
resolve them. -/
def IsBQuartet (q : Finset X) : Prop := ∀ s ∈ treesOn q, ¬ Displays (treeOfBlobs N) s

end NetworkQuartets

namespace RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- A network is level-1: every blob has level at most one, the level of a blob being its number of
reticulation edges minus its number of reticulation vertices. The blobs are the classes of
`DirectedMultigraph.blobSetoid` (`DirectedMultigraph.isBlob_iff`). -/
def IsLevelOne [Fintype V] [Fintype E] : Prop :=
  ∀ v : V,
    ((univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
        N.graph.blobSetoid v (N.graph.target e)).card : ℤ) -
      ((univ.filter fun u => 2 ≤ N.graph.indegree u ∧ N.graph.blobSetoid v u).card : ℤ) ≤ 1

end RootedNetwork

end Phylogenetics
