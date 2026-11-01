module

public import Phylogenetics.NMSC.InducedAbove

/-!
# Concordance factors on an induced network

Concordance factors do not change on passing to the network induced on a set of four taxa
(`RootedNetwork.inducedNetwork`), with its parameters (`RootedNetwork.inducedMetric`).

The proof has two steps, each a theorem:

* passing to the part below the least stable ancestor of the taxa and ancestral to them
  (`NMSC.nmscCF_belowNetwork`, `Phylogenetics.NMSC.InducedAbove`), which uses that the four taxa are four;
* suppressing the vertices of indegree one and outdegree one (`NMSC.geneTreeDist_suppress`,
  `Phylogenetics.NMSC.InducedSuppress`), for every network and every gene tree.

A quartet tree on the type `↥(Q : Set X)` of the four taxa is carried to a quartet tree on `X` by
`QuartetTree.map Subtype.val_injective` (`taxa_map_val`, `exists_map_val_eq`).

Allman, Baños, Mitchell, Rhodes (2023, Definition 6) define an induced network that keeps what lies above the least stable
ancestor of the taxa. `RootedNetwork.inducedNetwork` removes it, following Rhodes, Allman, Ané, Baños (2026, Section 2),
and the first step is where the four taxa are used.

## Main results

* `NMSC.nmscCF_inducedNetwork`: the theorem.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
* J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*, bioRxiv 10.64898/2026.05.28.728501.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

omit [Fintype X] in
/-- The image in `X` of a quartet tree on four taxa `Q` is a quartet tree on `Q`. -/
theorem taxa_map_val {Q : Finset X} (hQ : #Q = 4) [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]
    (s : QuartetTree (Q : Set X)) : (s.map Subtype.val_injective).taxa = Q := by
  have hcard : Fintype.card (Q : Set X) = 4 := by
    rw [← hQ]
    exact Fintype.card_coe Q
  have hstaxa : s.taxa = univ := eq_univ_of_card _ (by rw [s.card_taxa, hcard])
  rw [QuartetTree.map_taxa, hstaxa]
  ext x
  simp

omit [Fintype X] in
/-- Every quartet tree on four taxa `Q` comes from a quartet tree on the type of `Q`. -/
theorem exists_map_val_eq {Q : Finset X} [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]
    {r : QuartetTree X} (hr : r.taxa = Q) :
    ∃ s : QuartetTree (Q : Set X), s.map Subtype.val_injective = r := by
  refine QuartetTree.exists_map_eq Subtype.val_injective r fun x hx => ?_
  rw [hr] at hx
  exact mem_image.2 ⟨⟨x, hx⟩, mem_univ _, rfl⟩

/-- **Concordance factors do not change on passing to an induced network** (Allman, Baños, Mitchell,
Rhodes 2023): for a set `Q` of four taxa and a
quartet tree `s` on them, the concordance factor of `s` under the network induced on `Q`, with the
induced parameters, is that of `s` under the network. -/
theorem nmscCF_inducedNetwork (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {Q : Finset X} (hQ : #Q = 4) (hY : (Q : Set X).Nontrivial) [Fintype (Q : Set X)]
    [DecidableEq (Q : Set X)]
    [Fintype {v // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex v}]
    [Fintype {e // ¬ (lsaNetwork hN (Q : Set X) hY.nonempty).IsChainVertex
      ((lsaNetwork hN (Q : Set X) hY.nonempty).graph.source e)}]
    (s : QuartetTree (Q : Set X)) :
    nmscCF (inducedNetwork hN (Q : Set X) hY) (inducedMetric hN (Q : Set X) hY.nonempty θ) ρ s =
      nmscCF N θ ρ (s.map Subtype.val_injective) := by
  have hst := (lsa_spec hN (Q : Set X) hY.nonempty).1
  have hL := lsaNetwork_isPhylogenetic hN hY
  let : Fintype (N.belowVertices (lsa hN (Q : Set X) hY.nonempty) (Q : Set X)) :=
    Fintype.ofFinite _
  let : Fintype (N.belowArcs (lsa hN (Q : Set X) hY.nonempty) (Q : Set X)) := Fintype.ofFinite _
  have hθL : (lsaNetwork hN (Q : Set X) hY.nonempty).IsMetric
      (belowMetric (lsa hN (Q : Set X) hY.nonempty) (Q : Set X) θ) :=
    belowMetric_isMetric hN hst hL hθ
  exact (nmscCF_suppress hL hθL.isNormalized hρ.1 s).trans
    (nmscCF_belowNetwork hN hθ hρ hQ hY hst s)

end NMSC

end Phylogenetics
