module

public import Phylogenetics.Network.Induced

/-!
# The parameters of an induced network

The numerical parameters that a network `N` gives its induced network on a set of taxa `Y`: the
parameters of the arcs that stay, with the lengths along each suppressed chain added, and with the
inheritance of the chain's last arc (the other arcs of a chain enter vertices of indegree one, so that
under `IsNormalized` their inheritance is `1`, and the product below is the last arc's).

## Main definitions

* `RootedNetwork.belowMetric`, `RootedNetwork.suppressMetric`, `RootedNetwork.inducedMetric`.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
-/

@[expose] public noncomputable section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

open Classical in
/-- The parameters of the suppressed network: along a chain, lengths add and inheritances multiply. -/
def suppressMetric [Fintype E] (N : RootedNetwork V E X) (θ : MetricData E) :
    MetricData {e // ¬ N.IsChainVertex (N.graph.source e)} where
  length e := ∑ f with N.IsOnChain e.1 f, θ.length f
  inheritance e := ∏ f with N.IsOnChain e.1 f, θ.inheritance f

/-- The parameters of a network on the arcs below a vertex: those of the same arcs. -/
def belowMetric (l : V) (Y : Set X) (θ : MetricData E) : MetricData (N.belowArcs l Y) where
  length e := θ.length e.1
  inheritance e := θ.inheritance e.1

open Classical in
/-- **The parameters of the network induced on `Y`**: restrict to the arcs below the LSA of `Y` and
ancestral to `Y`, then suppress. -/
def inducedMetric [Fintype E] (hN : N.IsPhylogenetic) (Y : Set X) (hY : Y.Nonempty) (θ : MetricData E) :
    MetricData {e : N.belowArcs (lsa hN Y hY) Y //
      ¬ (lsaNetwork hN Y hY).IsChainVertex ((lsaNetwork hN Y hY).graph.source e)} :=
  have : Fintype (N.belowArcs (lsa hN Y hY) Y) := Fintype.ofFinite _
  (lsaNetwork hN Y hY).suppressMetric (belowMetric (lsa hN Y hY) Y θ)

end Phylogenetics.RootedNetwork
