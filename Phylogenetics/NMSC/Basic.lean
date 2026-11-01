module

public import Phylogenetics.NMSC.History
public import Phylogenetics.Tree.Splits

/-!
# Basic properties of the network multispecies coalescent on arbitrary networks

For a phylogenetic network with valid numerical parameters and inheritance correlation `0 ≤ ρ ≤ 1`:
`geneTreeDist` is a probability distribution, supported on binary rooted trees on the taxa, on each
of which it is positive. Hence the quartet concordance factors are positive and sum to one on each
set of four taxa. The proofs go along a linear extension of the network, one vertex at a time
(`Phylogenetics.NMSC.History`).

## Main results

* `geneTreeDist_nonneg`, `sum_geneTreeDist`: `geneTreeDist` is a probability distribution.
* `geneTreeDist_support`, `geneTreeDist_pos`: it is supported on the binary rooted trees on the taxa,
  on each of which it is positive.
* `nmscCF_pos`, `sum_nmscCF`: the quartet concordance factors.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

open NMSC

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- A term of `geneTreeDist` is nonnegative: the absorption from the arriving forest is a real
probability on the histories of nonzero weight. -/
private theorem history_term_nonneg (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (bot top : E → Finset (Finset X)) (G : Finset (Finset X)) :
    0 ≤ historyWeight N θ ρ bot top * kingmanAbsorption (arrivingForest N top N.root) G := by
  by_cases h : historyWeight N θ ρ bot top = 0
  · simp [h]
  · exact mul_nonneg (historyWeight_nonneg hθ hρ bot top)
      (kingmanAbsorption_nonneg (good_arrivingForest_root hN h).1.1 G)

/-- The network multispecies coalescent gives a probability distribution on gene trees. -/
theorem geneTreeDist_nonneg (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (G : Finset (Finset X)) : 0 ≤ geneTreeDist N θ ρ G :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => history_term_nonneg hN hθ hρ _ _ G

/-- The gene tree distribution has total mass one. -/
theorem sum_geneTreeDist (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    [Nonempty X] : ∑ G, geneTreeDist N θ ρ G = 1 := by
  unfold geneTreeDist
  rw [sum_comm, ← sum_sum_historyWeight (θ := θ) (ρ := ρ) hN hθ hρ]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [← mul_sum]
  by_cases h : historyWeight N θ ρ bot top = 0
  · simp [h]
  · rw [kingmanAbsorption_sum (good_arrivingForest_root hN h).1.1, mul_one]

/-- Gene trees are binary rooted trees on all the taxa. -/
theorem geneTreeDist_support (hN : N.IsPhylogenetic) [Nonempty X] {G : Finset (Finset X)}
    (hG : geneTreeDist N θ ρ G ≠ 0) : IsBinaryHierarchy G := by
  obtain ⟨bot, -, hbot⟩ := exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨top, -, htop⟩ := exists_ne_zero_of_sum_ne_zero hbot
  obtain ⟨hgood, hlin⟩ := good_arrivingForest_root hN (left_ne_zero_of_mul htop)
  obtain ⟨h1, -, h3, h4⟩ := kingmanAbsorption_support_good hgood (right_ne_zero_of_mul htop)
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨A, hA, -⟩ := mem_lineages.1 (hlin ▸ mem_univ x)
  exact isGoodForest_iff_binaryHierarchy.2 ⟨h1, h3.trans hlin, h4 ⟨A, hA⟩⟩

/-- Every binary rooted tree on the taxa has positive probability. -/
theorem geneTreeDist_pos (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    [Nonempty X] {G : Finset (Finset X)} (hG : IsBinaryHierarchy G) : 0 < geneTreeDist N θ ρ G := by
  obtain ⟨hgood, hlin, hone⟩ := isGoodForest_iff_binaryHierarchy.1 hG
  obtain ⟨top, hw, htop⟩ := exists_chain_history (θ := θ) (ρ := ρ) hN hθ hρ
  have hpos : 0 < historyWeight N θ ρ top top *
      kingmanAbsorption (arrivingForest N top N.root) G := by
    rw [htop]
    exact mul_pos hw (kingmanAbsorption_singletons_pos hgood hlin hone)
  refine lt_of_lt_of_le hpos ?_
  unfold geneTreeDist
  have h1 := single_le_sum (s := univ) (a := top)
    (f := fun top' => historyWeight N θ ρ top top' *
      kingmanAbsorption (arrivingForest N top' N.root) G)
    (fun _ _ => history_term_nonneg hN hθ hρ _ _ G) (mem_univ _)
  have h2 := single_le_sum (s := univ) (a := top)
    (f := fun bot => ∑ top', historyWeight N θ ρ bot top' *
      kingmanAbsorption (arrivingForest N top' N.root) G)
    (fun _ _ => sum_nonneg fun _ _ => history_term_nonneg hN hθ hρ _ _ G) (mem_univ _)
  exact h1.trans h2

/-- Quartet concordance factors are positive. -/
theorem nmscCF_pos (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) : 0 < nmscCF N θ ρ s := by
  obtain ⟨hcard, hB2, hdisj⟩ := s.property
  obtain ⟨A, hA⟩ : s.val.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, hAB⟩ := exists_mem_ne (by omega : 1 < #s.val) A
  have hAc := hB2 A hA
  obtain ⟨a, b, hab, hAeq⟩ := card_eq_two.1 hAc
  have : Nonempty X := ⟨a⟩
  -- the forest in which only `a` and `b` have merged
  set F₀ : Finset (Finset X) := univ.image fun x => ({x} : Finset X) with hF₀
  have hg₀ : IsGoodForest F₀ := isGoodForest_singletons _
  have hroot : ∀ x, ({x} : Finset X) ∈ roots F₀ := fun x => by
    refine mem_roots.2 ⟨mem_image_of_mem _ (mem_univ x), fun C hC hxC => ?_⟩
    obtain ⟨y, -, rfl⟩ := mem_image.1 hC
    rw [mem_singleton.1 (singleton_subset_iff.1 hxC)]
  have hne : ({a} : Finset X) ≠ {b} := fun h => hab (singleton_injective h)
  have hg₁ := hg₀.merge (hroot a) (hroot b) hne
  have hlin₁ : lineages (insert (({a} : Finset X) ∪ {b}) F₀) = univ := by
    rw [lineages_merge (hroot a) (hroot b), hF₀, lineages_image_singleton]
  obtain ⟨G, hsub, hgood, hlin, hone⟩ := exists_binary_completion hg₁ (insert_nonempty _ _) hlin₁
  have hbin : IsBinaryHierarchy G := isGoodForest_iff_binaryHierarchy.2 ⟨hgood, hlin, hone⟩
  have hAG : A ∈ G := hsub (mem_insert.2 (Or.inl (by rw [hAeq]; rfl)))
  have hAu : A ≠ univ := by
    rintro rfl
    obtain ⟨y, hy⟩ := card_pos.1 (by rw [hB2 B hB]; omega : 0 < #B)
    exact disjoint_left.1 (hdisj _ hA B hB (Ne.symm hAB)) (mem_univ y) hy
  have hdisp : Displays (unroot G) s := by
    refine ⟨A, mem_unroot.2 (Or.inl ⟨hAG, hAu⟩), ?_⟩
    have hAq : A ⊆ s.taxa := le_sup (f := id) hA
    rwa [inter_eq_left.2 hAq]
  have hpos := geneTreeDist_pos hN hθ hρ hbin
  refine lt_of_lt_of_le hpos ?_
  unfold nmscCF
  have h1 := single_le_sum (s := univ) (a := G)
    (f := fun G => if Displays (unroot G) s then geneTreeDist N θ ρ G else 0)
    (fun G _ => by
      split_ifs
      · exact geneTreeDist_nonneg hN hθ hρ G
      · exact le_rfl) (mem_univ _)
  simpa only [hdisp, ↓reduceIte] using h1

/-- The quartet concordance factors on a set of four taxa sum to one. -/
theorem sum_nmscCF (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : q.card = 4) : ∑ r ∈ treesOn q, nmscCF N θ ρ r = 1 := by
  obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < #q)
  have : Nonempty X := ⟨x⟩
  unfold nmscCF
  rw [sum_comm, ← sum_geneTreeDist (θ := θ) (ρ := ρ) hN hθ hρ]
  refine sum_congr rfl fun G _ => ?_
  by_cases hd : geneTreeDist N θ ρ G = 0
  · simp [hd]
  · obtain ⟨hH, hbin⟩ := isBinaryHierarchy_iff_card_childClusters.1 (geneTreeDist_support hN hd)
    obtain ⟨r₀, hr₀, hdisp⟩ := IsBinaryTree.exists_displays ⟨G, hH, rfl, hbin⟩ hq
    rw [sum_eq_single r₀]
    · simp only [hdisp, ↓reduceIte]
    · intro r hr hne
      refine ite_eq_right fun hdr => hne ?_
      exact IsUnrootedTree.displays_unique ⟨G, hH, rfl⟩ hdr hdisp
        ((mem_filter.1 hr).2.trans (mem_filter.1 hr₀).2.symm)
    · exact fun h => absurd hr₀ h

end Phylogenetics
