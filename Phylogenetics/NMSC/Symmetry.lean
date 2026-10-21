module

public import Phylogenetics.NMSC.Basic
/-!
# Symmetric kernels and the score of a quartet

Once three or four of the lineages `0, 1, 2, 3` are together at a point of the network and have not
coalesced, the rest of the process treats them alike, so that each of the three splits of the four
lineages ends up in the unrooted gene tree with probability `1/3`; and once two of them have
coalesced, the split is decided. `Phylogenetics.NiceKernel S Φ` packages what a kernel `Φ` on
forests of the four lineages (the rest of the process, from some point on) needs for this: it adds
the lineages `S` (from elsewhere in the network), is invariant under the relabellings that fix `S`,
and sends good forests to probability distributions on good forests that contain them.
`Phylogenetics.NiceKernel.score` then says that the expected score `Phylogenetics.quartetScore` is
unchanged: `∑ G, Φ F G * quartetScore G = quartetScore F` for every good forest `F` of at least
three lineages outside `S`.

Kingman's coalescent, the population above the root, the addition of an independent forest, and
products of such kernels are nice (`Phylogenetics.niceKernel_kingmanTransition`,
`Phylogenetics.niceKernel_kingmanAbsorption`, `Phylogenetics.niceKernel_unionKernel`,
`Phylogenetics.NiceKernel.mul`).
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

/-- A kernel on forests of the four lineages `0, 1, 2, 3` that adds the lineages `S`, treats the
others symmetrically, and sends good forests to probability distributions on good forests that
contain them. -/
structure NiceKernel (S : Finset (Fin 4))
    (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ) : Prop where
  relabel : ∀ σ : Equiv.Perm (Fin 4), (∀ l ∈ S, σ l = l) → ∀ F G,
    Φ (relabelFamily σ F) (relabelFamily σ G) = Φ F G
  sum_eq_one : ∀ F, IsGood F → Disjoint (lineages F) S → ∑ G, Φ F G = 1
  support : ∀ F, IsGood F → Disjoint (lineages F) S → ∀ G, Φ F G ≠ 0 →
    IsGood G ∧ F ⊆ G ∧ lineages G = lineages F ∪ S

theorem niceKernel_one : NiceKernel ∅ 1 := by
  refine ⟨fun σ _ F G => ?_, fun F _ _ => ?_, fun F hF _ G hG => ?_⟩
  · simp only [Matrix.one_apply, (relabelFamily_injective σ).eq_iff]
  · simp [Matrix.one_apply]
  · obtain rfl : F = G := by
      by_contra h
      exact hG (Matrix.one_apply_ne h)
    exact ⟨hF, subset_rfl, (union_empty _).symm⟩

theorem NiceKernel.mul {S₁ S₂ : Finset (Fin 4)}
    {Φ₁ Φ₂ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ}
    (h₁ : NiceKernel S₁ Φ₁) (h₂ : NiceKernel S₂ Φ₂) (hS : Disjoint S₁ S₂) :
    NiceKernel (S₁ ∪ S₂) (Φ₁ * Φ₂) := by
  have hdisj : ∀ {F : Finset (Finset (Fin 4))}, Disjoint (lineages F) (S₁ ∪ S₂) →
      Disjoint (lineages F) S₁ ∧ Disjoint (lineages F) S₂ :=
    fun h => disjoint_union_right.1 h
  -- after `Φ₁`, the lineages are those of `F` and `S₁`, still disjoint from `S₂`
  have hmid : ∀ {F H : Finset (Finset (Fin 4))}, IsGood F → Disjoint (lineages F) (S₁ ∪ S₂) →
      Φ₁ F H ≠ 0 → IsGood H ∧ F ⊆ H ∧ Disjoint (lineages H) S₂ ∧
        lineages H = lineages F ∪ S₁ := by
    intro F H hF hFS hH
    obtain ⟨hHg, hFH, hHl⟩ := h₁.support F hF (hdisj hFS).1 H hH
    exact ⟨hHg, hFH, by rw [hHl]; exact disjoint_union_left.2 ⟨(hdisj hFS).2, hS⟩, hHl⟩
  refine ⟨fun σ hσ F G => ?_, fun F hF hFS => ?_, fun F hF hFS G hG => ?_⟩
  · simp only [Matrix.mul_apply]
    rw [← Equiv.sum_comp (relabelFamilyEquiv σ)]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [relabelFamilyEquiv_apply, h₁.relabel σ (fun l hl => hσ l (mem_union_left _ hl)),
      h₂.relabel σ (fun l hl => hσ l (mem_union_right _ hl))]
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm, ← h₁.sum_eq_one F hF (hdisj hFS).1]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [← Finset.mul_sum]
    by_cases hH : Φ₁ F H = 0
    · rw [hH, zero_mul]
    · obtain ⟨hHg, -, hHS, -⟩ := hmid hF hFS hH
      rw [h₂.sum_eq_one H hHg hHS, mul_one]
  · rw [Matrix.mul_apply] at hG
    obtain ⟨H, -, hH⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
    obtain ⟨hHg, hFH, hHS, hHl⟩ := hmid hF hFS (left_ne_zero_of_mul hH)
    obtain ⟨hGg, hHG, hGl⟩ := h₂.support H hHg hHS G (right_ne_zero_of_mul hH)
    exact ⟨hGg, hFH.trans hHG, by rw [hGl, hHl, union_assoc]⟩

theorem niceKernel_kingmanTransition (t : ℝ) : NiceKernel ∅ (kingmanTransition t) := by
  refine ⟨fun σ _ F G => kingmanTransition_relabel σ t F G,
    fun F hF _ => kingmanTransition_row_sum hF.1 t, fun F hF _ G hG => ?_⟩
  obtain ⟨hGg, hFG, hGl⟩ := kingmanTransition_support_isGood hF hG
  exact ⟨hGg, hFG, by rw [hGl, union_empty]⟩

theorem niceKernel_kingmanAbsorption : NiceKernel ∅ kingmanAbsorption := by
  refine ⟨fun σ _ F G => kingmanAbsorption_relabel σ F G,
    fun F hF _ => kingmanAbsorption_row_sum hF.1, fun F hF _ G hG => ?_⟩
  obtain ⟨hGg, hFG, hGl, -⟩ := kingmanAbsorption_support hF hG
  exact ⟨hGg, hFG, by rw [hGl, union_empty]⟩

/-- Adding an independent random forest on the lineages `S`. -/
theorem niceKernel_unionKernel {S : Finset (Fin 4)} {ν : Finset (Finset (Fin 4)) → ℝ}
    (hsum : ∑ E, ν E = 1) (hsupp : ∀ E, ν E ≠ 0 → IsGood E ∧ lineages E = S) :
    NiceKernel S (unionKernel ν) := by
  refine ⟨fun σ hσ F G => ?_, fun F _ _ => ?_, fun F hF hFS G hG => ?_⟩
  · unfold unionKernel
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases hE : ν E = 0
    · simp only [hE, ite_self]
    · -- `σ` fixes the added forest
      have hσE : relabelFamily σ E = E :=
        relabel_eq_self fun l hl => hσ l (by rwa [(hsupp E hE).2] at hl)
      have hFE : relabelFamily σ F ∪ E = relabelFamily σ (F ∪ E) := by
        rw [relabel_union, hσE]
      simp only [hFE, (relabelFamily_injective σ).eq_iff]
  · unfold unionKernel
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hsum
  · unfold unionKernel at hG
    obtain ⟨E, -, hE⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
    by_cases hFE : F ∪ E = G
    · rw [ite_eq_left hFE] at hE
      obtain ⟨hEg, hEl⟩ := hsupp E hE
      subst hFE
      exact ⟨hF.union hEg (by rw [hEl]; exact hFS), subset_union_left,
        by rw [lineages_union, hEl]⟩
    · rw [ite_eq_right hFE] at hE
      exact absurd rfl hE

/-! ### The scores of the three splits -/

/-- The score of the split `A | Aᶜ` of the four lineages, as `Phylogenetics.quartetScore` for the
split `{0, 1} | {2, 3}`. -/
private def ns_splitScore (A : Finset (Fin 4)) (G : Finset (Finset (Fin 4))) : ℝ :=
  if A ∈ G ∨ Aᶜ ∈ G then 1 else if ∃ C ∈ G, #C = 2 then 0 else 1 / 3

private lemma ns_quartetScore_eq (G : Finset (Finset (Fin 4))) :
    quartetScore G = ns_splitScore {0, 1} G := by
  have h : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  unfold quartetScore ns_splitScore
  rw [h]

private lemma ns_splitScore_compl (A : Finset (Fin 4)) (G : Finset (Finset (Fin 4))) :
    ns_splitScore Aᶜ G = ns_splitScore A G := by
  unfold ns_splitScore
  simp only [compl_compl, or_comm]

private lemma ns_map_compl (σ : Equiv.Perm (Fin 4)) (A : Finset (Fin 4)) :
    Aᶜ.map σ.toEmbedding = (A.map σ.toEmbedding)ᶜ := by
  ext x
  simp [Finset.mem_map_equiv]

/-- Relabelling the forest by `σ` relabels the split by `σ⁻¹`. -/
private lemma ns_splitScore_relabel (σ : Equiv.Perm (Fin 4)) (A : Finset (Fin 4))
    (G : Finset (Finset (Fin 4))) :
    ns_splitScore A (relabelFamily σ G) = ns_splitScore (A.map σ.symm.toEmbedding) G := by
  have h2 : (∃ C ∈ relabelFamily σ G, #C = 2) ↔ ∃ C ∈ G, #C = 2 := by
    constructor
    · rintro ⟨C, hC, h⟩
      exact ⟨C.map σ.symm.toEmbedding, mem_relabelFamily.1 hC, by rw [card_map, h]⟩
    · rintro ⟨C, hC, h⟩
      exact ⟨C.map σ.toEmbedding, map_mem_relabelFamily.2 hC, by rw [card_map, h]⟩
  unfold ns_splitScore
  simp only [h2]
  simp only [mem_relabelFamily, ns_map_compl]

/-- Two clusters of two of the four lineages that are nested or disjoint are equal or
complementary. -/
private lemma ns_laminar_two : ∀ A C : Finset (Fin 4), #A = 2 → #C = 2 →
    (A ⊆ C ∨ C ⊆ A ∨ Disjoint A C) → A = C ∨ A = Cᶜ := by
  decide

/-- A cluster of two of the four lineages is a side of exactly one of the three splits. -/
private lemma ns_two_cases : ∀ C : Finset (Fin 4), #C = 2 →
    (if ({0, 1} : Finset (Fin 4)) = C ∨ {0, 1} = Cᶜ then 1 else 0) +
      (if ({0, 2} : Finset (Fin 4)) = C ∨ {0, 2} = Cᶜ then 1 else 0) +
      (if ({0, 3} : Finset (Fin 4)) = C ∨ {0, 3} = Cᶜ then 1 else 0) = (1 : ℕ) := by
  decide

private lemma ns_card_compl_two {A : Finset (Fin 4)} (hA : #A = 2) : #Aᶜ = 2 := by
  rw [card_compl, hA, Fintype.card_fin]

/-- In a forest with a cluster `C` of two lineages, the score of a split is `1` if `C` is one of
its sides and `0` otherwise. -/
private lemma ns_splitScore_of_two {G : Finset (Finset (Fin 4))} (hG : IsForest G)
    {C : Finset (Fin 4)} (hC : C ∈ G) (hC2 : #C = 2) {A : Finset (Fin 4)} (hA2 : #A = 2) :
    ns_splitScore A G = if A = C ∨ A = Cᶜ then 1 else 0 := by
  have key : A ∈ G ∨ Aᶜ ∈ G ↔ A = C ∨ A = Cᶜ := by
    constructor
    · rintro (h | h)
      · exact ns_laminar_two A C hA2 hC2 (hG.2 A h C hC)
      · rcases ns_laminar_two Aᶜ C (ns_card_compl_two hA2) hC2 (hG.2 _ h C hC) with h' | h'
        · exact Or.inr (by rw [← h', compl_compl])
        · exact Or.inl (compl_injective h')
    · rintro (rfl | rfl)
      · exact Or.inl hC
      · exact Or.inr (by rwa [compl_compl])
  unfold ns_splitScore
  by_cases h : A = C ∨ A = Cᶜ
  · rw [ite_eq_left (key.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt key.1 h), ite_eq_right h, ite_eq_left ⟨C, hC, hC2⟩]

/-- On a forest, the scores of the three splits sum to `1`. -/
private lemma ns_splitScore_sum {G : Finset (Finset (Fin 4))} (hG : IsForest G) :
    ns_splitScore {0, 1} G + ns_splitScore {0, 2} G + ns_splitScore {0, 3} G = 1 := by
  by_cases h : ∃ C ∈ G, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h
    rw [ns_splitScore_of_two hG hC hC2 (by decide), ns_splitScore_of_two hG hC hC2 (by decide),
      ns_splitScore_of_two hG hC hC2 (by decide)]
    have := congrArg (Nat.cast : ℕ → ℝ) (ns_two_cases C hC2)
    push_cast at this
    exact this
  · have hs : ∀ A : Finset (Fin 4), #A = 2 → ns_splitScore A G = 1 / 3 := by
      intro A hA
      have hA' : ¬(A ∈ G ∨ Aᶜ ∈ G) := by
        rintro (h' | h')
        · exact h ⟨_, h', hA⟩
        · exact h ⟨_, h', ns_card_compl_two hA⟩
      unfold ns_splitScore
      rw [ite_eq_right hA', ite_eq_right h]
    rw [hs _ (by decide), hs _ (by decide), hs _ (by decide)]
    norm_num

/-! ### Forests without a cluster of two lineages -/

/-- In a good forest, a cluster of at least two lineages contains a cluster of two lineages. -/
private lemma ns_exists_two {L : Type*} [Fintype L] [DecidableEq L] {F : Finset (Finset L)}
    (hF : IsGood F) : ∀ n, ∀ A ∈ F, #A = n → 2 ≤ n → ∃ C ∈ F, #C = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hAn h2
    obtain ⟨B, hB, C, hC, hBC, hBCA⟩ := hF.2 A hA (hAn ▸ h2)
    have hB0 := (hF.1.1 B hB).card_pos
    have hC0 := (hF.1.1 C hC).card_pos
    have hcard : #B + #C = n := by rw [← card_union_of_disjoint hBC, hBCA, hAn]
    by_cases hB2 : 2 ≤ #B
    · exact ih #B (by omega) B hB rfl hB2
    by_cases hC2 : 2 ≤ #C
    · exact ih #C (by omega) C hC rfl hC2
    exact ⟨A, hA, by omega⟩

/-- A forest whose clusters are singletons is fixed by the transposition of two of its
lineages. -/
private lemma ns_relabel_swap {F : Finset (Finset (Fin 4))} (h1 : ∀ A ∈ F, #A = 1) {i j : Fin 4}
    (hi : i ∈ lineages F) (hj : j ∈ lineages F) :
    relabelFamily (Equiv.swap i j) F = F := by
  have hmem : ∀ l ∈ lineages F, {l} ∈ F := by
    intro l hl
    obtain ⟨A, hA, hlA⟩ := mem_lineages.1 hl
    obtain ⟨a, rfl⟩ := card_eq_one.1 (h1 A hA)
    rw [mem_singleton] at hlA
    rwa [hlA]
  have key : ∀ A ∈ F, A.map (Equiv.swap i j).toEmbedding ∈ F := by
    intro A hA
    obtain ⟨a, rfl⟩ := card_eq_one.1 (h1 A hA)
    have ha : a ∈ lineages F := mem_lineages.2 ⟨{a}, hA, mem_singleton_self a⟩
    rw [map_singleton, Equiv.toEmbedding_apply]
    apply hmem
    rcases eq_or_ne a i with rfl | hai
    · rwa [Equiv.swap_apply_left]
    rcases eq_or_ne a j with rfl | haj
    · rwa [Equiv.swap_apply_right]
    rwa [Equiv.swap_apply_of_ne_of_ne hai haj]
  have hinv : ∀ B : Finset (Fin 4),
      (B.map (Equiv.swap i j).toEmbedding).map (Equiv.swap i j).toEmbedding = B := by
    intro B
    ext x
    simp [Finset.mem_map_equiv]
  ext B
  rw [mem_relabelFamily, Equiv.symm_swap]
  constructor
  · intro hB
    rw [← hinv B]
    exact key _ hB
  · exact key B

/-- A set of at least three of the four lineages contains `1` and `2`, or `0` and `3`. -/
private lemma ns_three_a : ∀ T : Finset (Fin 4), 3 ≤ #T → (1 ∈ T ∧ 2 ∈ T) ∨ (0 ∈ T ∧ 3 ∈ T) := by
  decide

/-- A set of at least three of the four lineages contains `1` and `3`, or `0` and `2`. -/
private lemma ns_three_b : ∀ T : Finset (Fin 4), 3 ≤ #T → (1 ∈ T ∧ 3 ∈ T) ∨ (0 ∈ T ∧ 2 ∈ T) := by
  decide

/-- The transpositions of the lineages of a set `T` of at least three of the four lineages connect
the three splits: a function of the sides of the splits that is invariant under them and under
complement takes the same value on the three splits. -/
private lemma ns_chain (E : Finset (Fin 4) → ℝ) {T : Finset (Fin 4)} (hT : 3 ≤ #T)
    (hE : ∀ i ∈ T, ∀ j ∈ T, ∀ A, E (A.map (Equiv.swap i j).toEmbedding) = E A)
    (hc : ∀ A, E Aᶜ = E A) : E {0, 2} = E {0, 1} ∧ E {0, 3} = E {0, 1} := by
  constructor
  · rcases ns_three_a T hT with ⟨h1, h2⟩ | ⟨h0, h3⟩
    · have := hE 1 h1 2 h2 {0, 1}
      rwa [show ({0, 1} : Finset (Fin 4)).map (Equiv.swap 1 2).toEmbedding = {0, 2} by decide]
        at this
    · have := hE 0 h0 3 h3 {0, 1}
      rwa [show ({0, 1} : Finset (Fin 4)).map (Equiv.swap 0 3).toEmbedding = {0, 2}ᶜ by decide,
        hc] at this
  · rcases ns_three_b T hT with ⟨h1, h3⟩ | ⟨h0, h2⟩
    · have := hE 1 h1 3 h3 {0, 1}
      rwa [show ({0, 1} : Finset (Fin 4)).map (Equiv.swap 1 3).toEmbedding = {0, 3} by decide]
        at this
    · have := hE 0 h0 2 h2 {0, 1}
      rwa [show ({0, 1} : Finset (Fin 4)).map (Equiv.swap 0 2).toEmbedding = {0, 3}ᶜ by decide,
        hc] at this

/-- The expected score of a split after a nice kernel is invariant under the relabellings that fix
the added lineages and the starting forest. -/
private lemma ns_expect_relabel {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {F : Finset (Finset (Fin 4))} (σ : Equiv.Perm (Fin 4)) (hσS : ∀ l ∈ S, σ l = l)
    (hσF : relabelFamily σ F = F) (A : Finset (Fin 4)) :
    ∑ G, Φ F G * ns_splitScore (A.map σ.symm.toEmbedding) G =
      ∑ G, Φ F G * ns_splitScore A G := by
  rw [← Equiv.sum_comp (relabelFamilyEquiv σ) (fun G => Φ F G * ns_splitScore A G)]
  refine Finset.sum_congr rfl fun G _ => ?_
  have h := hΦ.relabel σ hσS F G
  rw [hσF] at h
  simp only [relabelFamilyEquiv_apply]
  rw [ns_splitScore_relabel, h]

/-- **The score is invariant.** For a nice kernel `Φ` and a good forest `F` of at least three
lineages, none added by `Φ`, the expected score after `Φ` is the score of `F`: if `F` has a cluster
of two lineages, it stays (and decides the split); if not, the three splits are equally likely by
symmetry. -/
theorem NiceKernel.score {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {F : Finset (Finset (Fin 4))} (hF : IsGood F) (hFS : Disjoint (lineages F) S)
    (h3 : 3 ≤ #(lineages F)) :
    ∑ G, Φ F G * quartetScore G = quartetScore F := by
  by_cases h2 : ∃ C ∈ F, #C = 2
  · -- a cluster of two lineages stays, and decides the split
    obtain ⟨C, hC, hC2⟩ := h2
    have hval : ∀ G, IsGood G → F ⊆ G → quartetScore G = quartetScore F := by
      intro G hG hFG
      rw [ns_quartetScore_eq, ns_quartetScore_eq, ns_splitScore_of_two hG.1 (hFG hC) hC2
        (by decide), ns_splitScore_of_two hF.1 hC hC2 (by decide)]
    calc ∑ G, Φ F G * quartetScore G = ∑ G, Φ F G * quartetScore F := by
          refine Finset.sum_congr rfl fun G _ => ?_
          by_cases hG : Φ F G = 0
          · rw [hG, zero_mul, zero_mul]
          · obtain ⟨hGg, hFG, -⟩ := hΦ.support F hF hFS G hG
            rw [hval G hGg hFG]
      _ = quartetScore F := by rw [← Finset.sum_mul, hΦ.sum_eq_one F hF hFS, one_mul]
  · -- the clusters of `F` are singletons, and the three splits are equally likely
    have h1 : ∀ A ∈ F, #A = 1 := by
      intro A hA
      have hpos := (hF.1.1 A hA).card_pos
      by_contra hne
      exact h2 (ns_exists_two hF #A A hA rfl (by omega))
    have hF3 : quartetScore F = 1 / 3 := by
      have h0123 : ¬(({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F) := by
        rintro (h | h)
        · exact h2 ⟨_, h, by decide⟩
        · exact h2 ⟨_, h, by decide⟩
      unfold quartetScore
      rw [ite_eq_right h0123, ite_eq_right h2]
    set E : Finset (Fin 4) → ℝ := fun A => ∑ G, Φ F G * ns_splitScore A G with hEdef
    have hE : ∀ i ∈ lineages F, ∀ j ∈ lineages F, ∀ A,
        E (A.map (Equiv.swap i j).toEmbedding) = E A := by
      intro i hi j hj A
      have hσS : ∀ l ∈ S, Equiv.swap i j l = l := fun l hl =>
        Equiv.swap_apply_of_ne_of_ne (fun h => disjoint_left.1 hFS (h ▸ hi) hl)
          (fun h => disjoint_left.1 hFS (h ▸ hj) hl)
      have := ns_expect_relabel hΦ (Equiv.swap i j) hσS (ns_relabel_swap h1 hi hj) A
      rwa [Equiv.symm_swap] at this
    have hc : ∀ A, E Aᶜ = E A := fun A => by simp only [hEdef, ns_splitScore_compl]
    obtain ⟨h02, h03⟩ := ns_chain E h3 hE hc
    have hsum : E {0, 1} + E {0, 2} + E {0, 3} = 1 := by
      simp only [hEdef, ← Finset.sum_add_distrib, ← mul_add]
      rw [← hΦ.sum_eq_one F hF hFS]
      refine Finset.sum_congr rfl fun G _ => ?_
      by_cases hG : Φ F G = 0
      · rw [hG, zero_mul]
      · rw [ns_splitScore_sum (hΦ.support F hF hFS G hG).1.1, mul_one]
    have h01 : E {0, 1} = 1 / 3 := by linarith
    rw [hF3, ← h01]
    simp only [hEdef, ns_quartetScore_eq]

end Phylogenetics
