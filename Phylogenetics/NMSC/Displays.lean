module

public import Phylogenetics.NMSC.Consistency
/-!
# Quartet CFs and gene trees on all the taxa

The quartet CF `Phylogenetics.Net.quartetCF N a b c e` samples one lineage from each of the four
taxa, while a gene tree usually has all the taxa. By the sampling consistency of the coalescent
(`Phylogenetics.Net.geneTreeDist_restrict`), the gene tree on all the taxa (one lineage per taxon)
restricted to `a, b, c, e` has the distribution of the gene tree of the four lineages, and it
displays `ab|ce` (`Phylogenetics.geneTreeDisplays`) exactly when its restriction has the split
`{0, 1} | {2, 3}`. Hence `Phylogenetics.quartetCF_eq_displays`. -/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u

/-! ### The split `{0, 1} | {2, 3}` of a restricted gene tree -/

/-- The clusters of the restriction of `G` to the lineages `v 0, …, v 3` are the nonempty traces
of the clusters of `G`. -/
private theorem nd_mem_restrictForest {X : Type u} [Fintype X] [DecidableEq X] (v : Fin 4 ↪ X)
    (G : Finset (Finset X)) (D : Finset (Fin 4)) :
    D ∈ restrictForest v G ↔
      ∃ C ∈ G, (∃ l, v l ∈ C) ∧ (univ.filter fun l => v l ∈ C) = D := by
  unfold restrictForest
  simp only [mem_image, mem_filter, and_assoc]

/-- The trace of a cluster `C` on `v 0, …, v 3` is `{0, 1}` exactly when `C` contains `v 0, v 1`
and neither `v 2` nor `v 3`. -/
private theorem nd_trace_eq_01 {X : Type u} [DecidableEq X] (v : Fin 4 → X) (C : Finset X) :
    (univ.filter fun l => v l ∈ C) = ({0, 1} : Finset (Fin 4)) ↔
      v 0 ∈ C ∧ v 1 ∈ C ∧ v 2 ∉ C ∧ v 3 ∉ C := by
  rw [Finset.ext_iff]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨(h 0).2 (by decide), (h 1).2 (by decide), fun h2 => ?_, fun h3 => ?_⟩
    · exact absurd ((h 2).1 h2) (by decide)
    · exact absurd ((h 3).1 h3) (by decide)
  · rintro ⟨h0, h1, h2, h3⟩ l
    fin_cases l <;> simp_all

/-- The trace of a cluster `C` on `v 0, …, v 3` is `{2, 3}` exactly when `C` contains `v 2, v 3`
and neither `v 0` nor `v 1`. -/
private theorem nd_trace_eq_23 {X : Type u} [DecidableEq X] (v : Fin 4 → X) (C : Finset X) :
    (univ.filter fun l => v l ∈ C) = ({2, 3} : Finset (Fin 4)) ↔
      v 2 ∈ C ∧ v 3 ∈ C ∧ v 0 ∉ C ∧ v 1 ∉ C := by
  rw [Finset.ext_iff]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨(h 2).2 (by decide), (h 3).2 (by decide), fun h0 => ?_, fun h1 => ?_⟩
    · exact absurd ((h 0).1 h0) (by decide)
    · exact absurd ((h 1).1 h1) (by decide)
  · rintro ⟨h2, h3, h0, h1⟩ l
    fin_cases l <;> simp_all

/-- A family of clusters on `Fin 4` has the split `{0, 1} | {2, 3}` exactly when it has the cluster
`{0, 1}` or the cluster `{2, 3}` (neither is `univ`, and `{0, 1}ᶜ = {2, 3}`). -/
private theorem nd_mem_unroot_iff (G : Finset (Finset (Fin 4))) :
    ({0, 1} : Finset (Fin 4)) ∈ unroot G ↔
      ({0, 1} : Finset (Fin 4)) ∈ G ∨ ({2, 3} : Finset (Fin 4)) ∈ G := by
  have hu : ({0, 1} : Finset (Fin 4)) ≠ univ := by decide
  have hc : ∀ D : Finset (Fin 4), Dᶜ = {0, 1} ↔ D = {2, 3} := by
    intro D
    rw [compl_eq_comm, eq_comm, show ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} by decide]
  simp only [unroot, mem_union, mem_erase, mem_image, hc]
  constructor
  · rintro (⟨-, h⟩ | ⟨D, ⟨-, hD⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr hD
  · rintro (h | h)
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr ⟨{2, 3}, ⟨by decide, h⟩, rfl⟩

/-- The restriction of a gene tree `G` on `X` to the lineages `v 0, …, v 3` has the split
`{0, 1} | {2, 3}` exactly when `G` displays the quartet `(v 0) (v 1) | (v 2) (v 3)`. -/
private theorem nd_mem_unroot_restrict_iff {X : Type u} [Fintype X] [DecidableEq X]
    (v : Fin 4 ↪ X) (G : Finset (Finset X)) :
    ({0, 1} : Finset (Fin 4)) ∈ unroot (restrictForest v G) ↔
      geneTreeDisplays G (v 0) (v 1) (v 2) (v 3) = true := by
  rw [nd_mem_unroot_iff, nd_mem_restrictForest, nd_mem_restrictForest, geneTreeDisplays,
    decide_eq_true_iff]
  simp only [nd_trace_eq_01, nd_trace_eq_23]
  constructor
  · rintro (⟨C, hC, -, h⟩ | ⟨C, hC, -, h⟩)
    · exact ⟨C, hC, Or.inl h⟩
    · exact ⟨C, hC, Or.inr h⟩
  · rintro ⟨C, hC, h | h⟩
    · exact Or.inl ⟨C, hC, ⟨0, h.1⟩, h⟩
    · exact Or.inr ⟨C, hC, ⟨2, h.1⟩, h⟩

/-- Four distinct taxa give an embedding of the lineages `Fin 4`. -/
private theorem nd_injective {X : Type u} {a b c e : X} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : Function.Injective ![a, b, c, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- **Quartet CFs from gene trees on all the lineages** (the sampling consistency of the
coalescent), for any sampling: when lineage `t` of `L` is sampled from the taxon `s t`, the quartet
CF of the taxa `s i, s j, s k, s l` of distinct lineages is the probability that the gene tree of
the NMSC on all the lineages displays `ij|kl`. Its restriction to `i, j, k, l` has the distribution
of the gene tree of four lineages sampled from these taxa. -/
theorem quartetCF_eq_displays_sample {X : Type u} [DecidableEq X] {L : Type*} [Fintype L]
    [DecidableEq L] (N : Net X) (hN : N.leaves.Nodup) (s : L → X) {i j k l : L} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    N.quartetCF (s i) (s j) (s k) (s l) =
      ∑ G, if geneTreeDisplays G i j k l then N.geneTreeDist s G else 0 := by
  -- the four lineages `i, j, k, l` of `L`, through the embedding `v`
  set v : Fin 4 ↪ L := ⟨![i, j, k, l], nd_injective hij hik hil hjk hjl hkl⟩
  have hsv : (![s i, s j, s k, s l] : Fin 4 → X) = s ∘ v := by
    funext r
    fin_cases r <;> rfl
  -- sampling consistency: the gene tree of the four lineages is the restriction of the gene tree
  -- on all the lineages
  have hres : ∀ G', N.geneTreeDist ![s i, s j, s k, s l] G' =
      ∑ G, if restrictForest v G = G' then N.geneTreeDist s G else 0 := fun G' => by
    rw [hsv]
    exact (N.geneTreeDist_restrict hN s v G').symm
  unfold Net.quartetCF
  simp_rw [hres]
  calc ∑ G', (if ({0, 1} : Finset (Fin 4)) ∈ unroot G' then
          ∑ G, (if restrictForest v G = G' then N.geneTreeDist s G else 0) else 0)
      = ∑ G', ∑ G, if restrictForest v G = G' then
          (if ({0, 1} : Finset (Fin 4)) ∈ unroot G' then N.geneTreeDist s G else 0) else 0 := by
        refine Finset.sum_congr rfl fun G' _ => ?_
        split_ifs with h
        · exact Finset.sum_congr rfl fun G _ => by split_ifs <;> rfl
        · simp
    _ = ∑ G, ∑ G', if restrictForest v G = G' then
          (if ({0, 1} : Finset (Fin 4)) ∈ unroot G' then N.geneTreeDist s G else 0) else 0 :=
        Finset.sum_comm
    _ = ∑ G, if geneTreeDisplays G i j k l then N.geneTreeDist s G else 0 := by
        refine Finset.sum_congr rfl fun G _ => ?_
        rw [Fintype.sum_ite_eq]
        exact if_congr (nd_mem_unroot_restrict_iff v G) rfl rfl

/-- **Quartet CFs from gene trees on all the taxa** (the sampling consistency of the coalescent):
for distinct taxa `a, b, c, e`, the quartet CF of four lineages sampled from them is the
probability that the gene tree of the NMSC on all the taxa displays `ab|ce` (one lineage per
taxon: lineage `t` is sampled from taxon `t`; elements of `X` that are not leaves of `N` are not
sampled). The case `s = id` of `Phylogenetics.quartetCF_eq_displays_sample`. -/
theorem quartetCF_eq_displays {X : Type u} [Fintype X] [DecidableEq X] (N : Net X)
    (hN : N.leaves.Nodup) {a b c e : X} (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e) :
    N.quartetCF a b c e = ∑ G, if geneTreeDisplays G a b c e then N.geneTreeDist id G else 0 :=
  quartetCF_eq_displays_sample N hN id hab hac hae hbc hbe hce

end Phylogenetics
