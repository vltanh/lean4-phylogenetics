module

public import Phylogenetics.Coalescent.Absorption
public import Phylogenetics.Hierarchy.Basic

/-!
# Binary forests under Kingman's coalescent

A forest is *binary* when each of its clusters with at least two lineages is the union of two
disjoint clusters. Merging two roots keeps this property, so Kingman's coalescent from a binary
forest stays on binary forests, and above the root it ends in a binary rooted tree.

## Main results

* `IsGoodForest`, a binary forest; `kingmanTransition_support_good`,
  `kingmanAbsorption_support_good`: the supports of the coalescent.
* `IsGoodForest.biUnion`, `isGoodForest_singletons`, `isGoodForest_forestBelow`: the operations of
  the network multispecies coalescent.
* `IsGoodForest.exists_two`, `IsGoodForest.eq_singletons`: a binary forest has a cluster of two
  lineages, or is a forest of singletons.
* `isGoodForest_iff_binaryHierarchy`: the binary rooted trees on `L` are the binary forests with one
  root and all lineages.
* `kingmanAbsorption_singletons_pos`: from the forest of uncoalesced lineages, every binary rooted
  tree has positive probability.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Every cluster with at least two elements is the union of two disjoint clusters. -/
def IsBinaryForest (F : Finset (Finset L)) : Prop :=
  ∀ A ∈ F, 2 ≤ #A → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A

/-- A binary forest: a forest (nonempty clusters, any two nested or disjoint) in which every
cluster with at least two lineages is the union of two disjoint clusters. -/
def IsGoodForest (F : Finset (Finset L)) : Prop :=
  IsForest F ∧ IsBinaryForest F

/-! ### Preservation under the coalescent -/

/-- Merging two roots of a binary forest gives a binary forest. -/
theorem isBinaryForest_merge {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : IsBinaryForest F) (hG : G ∈ merges F) : IsBinaryForest G := by
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hG
  intro C hC hC2
  rcases mem_insert.1 hC with rfl | hC
  · exact ⟨A, mem_insert_of_mem (roots_subset F hA), B, mem_insert_of_mem (roots_subset F hB),
      hF.disjoint_of_mem_roots hA hB hAB, rfl⟩
  · obtain ⟨D, hD, E, hE, hDE, hDEC⟩ := hb C hC hC2
    exact ⟨D, mem_insert_of_mem hD, E, mem_insert_of_mem hE, hDE, hDEC⟩

/-- The jump chain from a binary forest stays on binary forests. -/
theorem isBinaryForest_of_jumpMatrix_pow {F G : Finset (Finset L)} (hF : IsForest F)
    (hb : IsBinaryForest F) {n : ℕ} (h : (jumpMatrix ^ n) F G ≠ 0) :
    IsBinaryForest G := by
  induction n generalizing F with
  | zero =>
    rw [pow_zero] at h
    by_cases hGF : G = F
    · exact hGF ▸ hb
    · exact absurd (Matrix.one_apply_ne (Ne.symm hGF)) h
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero h
    have hJ := left_ne_zero_of_mul hF'
    have hJn := right_ne_zero_of_mul hF'
    by_cases hk : #(roots F) ≤ 1
    · have hF'F : F' = F := by
        by_contra hne
        exact hJ (by simp only [jumpMatrix, hk, hne, ↓reduceIte])
      subst hF'F
      exact ih hF hb hJn
    · have hmem : F' ∈ merges F := by
        by_contra hne
        exact hJ (by rw [jumpMatrix_apply_of_isForest (by omega), ite_eq_right hne])
      exact ih (hF.of_mem_merges hmem).1 (isBinaryForest_merge hF hb hmem) hJn

/-- Kingman's coalescent from a binary forest reaches only binary forests that contain it and have
the same lineages. -/
theorem kingmanTransition_support_good {F G : Finset (Finset L)} (hF : IsGoodForest F) {t : ℝ}
    (h : kingmanTransition t F G ≠ 0) :
    IsGoodForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  obtain ⟨h1, h2, h3, -⟩ := kingmanTransition_support hF.1 h
  rw [kingmanTransition_apply hF.1] at h
  exact ⟨⟨h1, isBinaryForest_of_jumpMatrix_pow hF.1 hF.2 (right_ne_zero_of_mul h)⟩, h2, h3⟩

/-- Above the root, the lineages of a nonempty binary forest coalesce into one binary tree. -/
theorem kingmanAbsorption_support_good {F G : Finset (Finset L)} (hF : IsGoodForest F)
    (h : kingmanAbsorption F G ≠ 0) :
    IsGoodForest G ∧ F ⊆ G ∧ lineages G = lineages F ∧ (F.Nonempty → #(roots G) = 1) := by
  rw [kingmanAbsorption_apply hF.1] at h
  by_cases h0 : #(roots F) = 0
  · rw [ite_eq_left h0] at h
    have hGF : G = F := by
      by_contra hne
      exact h (ite_eq_right hne)
    subst hGF
    exact ⟨hF, Finset.Subset.refl _, rfl,
      fun hne => absurd (card_roots_eq_zero_iff.1 h0) hne.ne_empty⟩
  rw [ite_eq_right h0] at h
  by_cases h1 : #(roots G) = 1
  · rw [ite_eq_left h1] at h
    obtain ⟨h1', h2, h3, -⟩ := jumpMatrix_pow_support hF.1 h
    exact ⟨⟨h1', isBinaryForest_of_jumpMatrix_pow hF.1 hF.2 h⟩, h2, h3, fun _ => h1⟩
  · rw [ite_eq_right h1] at h
    exact absurd rfl h

/-! ### Building binary forests -/

section Building

omit [Fintype L]

theorem isGoodForest_empty : IsGoodForest (∅ : Finset (Finset L)) :=
  ⟨isForest_empty, fun A hA => absurd hA (notMem_empty A)⟩

/-- The forest of the singletons of a set of lineages is binary. -/
theorem isGoodForest_singletons (T : Finset L) :
    IsGoodForest (T.image fun l => ({l} : Finset L)) := by
  refine ⟨?_, fun A hA h2 => ?_⟩
  · simpa using (isForest_empty (L := L)).union_image_singleton T
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    simp at h2

theorem IsGoodForest.union {F G : Finset (Finset L)} (hF : IsGoodForest F) (hG : IsGoodForest G)
    (h : Disjoint (lineages F) (lineages G)) : IsGoodForest (F ∪ G) := by
  refine ⟨hF.1.union_of_disjoint hG.1 h, fun A hA h2 => ?_⟩
  rcases mem_union.1 hA with hA | hA
  · obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA h2
    exact ⟨B, mem_union_left _ hB, C, mem_union_left _ hC, hBC, rfl⟩
  · obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hG.2 A hA h2
    exact ⟨B, mem_union_right _ hB, C, mem_union_right _ hC, hBC, rfl⟩

/-- The union of binary forests on pairwise disjoint sets of lineages is a binary forest. -/
theorem IsGoodForest.biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Finset (Finset L))
    (hf : ∀ i ∈ s, IsGoodForest (f i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (lineages (f i)) (lineages (f j))) :
    IsGoodForest (s.biUnion f) := by
  refine ⟨⟨fun A hA => ?_, fun A hA B hB => ?_⟩, fun A hA h2 => ?_⟩
  · obtain ⟨i, hi, hA⟩ := mem_biUnion.1 hA
    exact (hf i hi).1.1 A hA
  · obtain ⟨i, hi, hA⟩ := mem_biUnion.1 hA
    obtain ⟨j, hj, hB⟩ := mem_biUnion.1 hB
    by_cases hij : i = j
    · subst hij
      exact (hf i hi).1.2 A hA B hB
    · exact Or.inr (Or.inr ((hd i hi j hj hij).mono (subset_lineages hA) (subset_lineages hB)))
  · obtain ⟨i, hi, hA⟩ := mem_biUnion.1 hA
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := (hf i hi).2 A hA h2
    exact ⟨B, mem_biUnion.2 ⟨i, hi, hB⟩, C, mem_biUnion.2 ⟨i, hi, hC⟩, hBC, rfl⟩

theorem mem_forestBelow {F A : Finset (Finset L)} {B : Finset L} :
    B ∈ forestBelow F A ↔ B ∈ F ∧ ∃ C ∈ A, B ⊆ C := by
  unfold forestBelow
  exact mem_filter

/-- The part of a binary forest below the members of any family `A` of clusters is binary. -/
theorem isGoodForest_forestBelow {F A : Finset (Finset L)} (hF : IsGoodForest F) :
    IsGoodForest (forestBelow F A) := by
  refine ⟨hF.1.subset (fun _ h => (mem_forestBelow.1 h).1), fun B hB h2 => ?_⟩
  obtain ⟨hBF, C, hC, hBC⟩ := mem_forestBelow.1 hB
  obtain ⟨D, hD, E, hE, hDE, rfl⟩ := hF.2 B hBF h2
  exact ⟨D, mem_forestBelow.2 ⟨hD, C, hC, subset_union_left.trans hBC⟩, E,
    mem_forestBelow.2 ⟨hE, C, hC, subset_union_right.trans hBC⟩, hDE, rfl⟩

/-- Every lineage of a binary forest is a cluster of it. -/
theorem IsGoodForest.singleton_mem {F : Finset (Finset L)} (hF : IsGoodForest F) {A : Finset L}
    (hA : A ∈ F) {x : L} (hx : x ∈ A) : {x} ∈ F := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases h2 : 2 ≤ #A
    · obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA h2
      have hBne := hF.1.1 B hB
      have hCne := hF.1.1 C hC
      rcases mem_union.1 hx with hx | hx
      · refine ih B ?_ hB hx
        refine (subset_union_left).ssubset_of_ne fun h => ?_
        obtain ⟨y, hy⟩ := hCne
        exact disjoint_left.1 hBC (h ▸ mem_union_right B hy) hy
      · refine ih C ?_ hC hx
        refine (subset_union_right).ssubset_of_ne fun h => ?_
        obtain ⟨y, hy⟩ := hBne
        exact disjoint_right.1 hBC (h ▸ mem_union_left C hy) hy
    · have hcard : #A = 1 := by
        have := card_pos.2 ⟨x, hx⟩
        omega
      obtain ⟨y, rfl⟩ := card_eq_one.1 hcard
      rwa [mem_singleton.1 hx]

end Building

omit [Fintype L] in
/-- In a binary forest, a cluster of at least two lineages contains a cluster of two lineages. -/
theorem IsGoodForest.exists_two {F : Finset (Finset L)} (hF : IsGoodForest F) :
    ∀ A ∈ F, 2 ≤ #A → ∃ C ∈ F, C ⊆ A ∧ #C = 2 := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hA h2
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA h2
    have hB0 := (hF.1.1 B hB).card_pos
    have hC0 := (hF.1.1 C hC).card_pos
    have hcard : #(B ∪ C) = #B + #C := card_union_of_disjoint hBC
    by_cases hB2 : 2 ≤ #B
    · obtain ⟨D, hD, hDB, hDc⟩ := ih B (subset_union_left.ssubset_of_ne fun h => by
        rw [← h] at hcard
        omega) hB hB2
      exact ⟨D, hD, hDB.trans subset_union_left, hDc⟩
    by_cases hC2 : 2 ≤ #C
    · obtain ⟨D, hD, hDC, hDc⟩ := ih C (subset_union_right.ssubset_of_ne fun h => by
        rw [← h] at hcard
        omega) hC hC2
      exact ⟨D, hD, hDC.trans subset_union_right, hDc⟩
    exact ⟨B ∪ C, hA, Subset.refl _, by omega⟩

omit [Fintype L] in
/-- A binary forest without a cluster of two lineages is a forest of singletons. -/
theorem IsGoodForest.eq_singletons {F : Finset (Finset L)} (hF : IsGoodForest F)
    (h : ¬ ∃ C ∈ F, #C = 2) : F = (lineages F).image fun x => ({x} : Finset L) := by
  have h1 : ∀ A ∈ F, #A = 1 := by
    intro A hA
    have hpos := (hF.1.1 A hA).card_pos
    by_contra hne
    obtain ⟨C, hC, -, hC2⟩ := hF.exists_two A hA (by omega)
    exact h ⟨C, hC, hC2⟩
  ext A
  simp only [mem_image, mem_lineages]
  constructor
  · intro hA
    obtain ⟨x, rfl⟩ := card_eq_one.1 (h1 A hA)
    exact ⟨x, ⟨{x}, hA, mem_singleton_self x⟩, rfl⟩
  · rintro ⟨x, ⟨B, hB, hx⟩, rfl⟩
    exact hF.singleton_mem hB hx

/-- The lineages of the part of a forest below some of its roots: the union of those roots. -/
theorem lineages_forestBelow {F A : Finset (Finset L)} (hA : A ⊆ roots F) :
    lineages (forestBelow F A) = A.sup id := by
  ext l
  rw [mem_lineages, Finset.mem_sup]
  constructor
  · rintro ⟨B, hB, hl⟩
    obtain ⟨-, C, hC, hBC⟩ := mem_forestBelow.1 hB
    exact ⟨C, hC, hBC hl⟩
  · rintro ⟨C, hC, hl⟩
    exact ⟨C, mem_forestBelow.2 ⟨roots_subset F (hA hC), C, hC, Finset.Subset.refl _⟩, hl⟩

/-- From a binary forest, the merge of two roots is binary. -/
theorem IsGoodForest.merge {F : Finset (Finset L)} (hF : IsGoodForest F) {A B : Finset L}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) : IsGoodForest (insert (A ∪ B) F) :=
  ⟨hF.1.isForest_merge hA hB,
    isBinaryForest_merge hF.1 hF.2 (mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩)⟩

/-! ### Binary rooted trees -/

/-- In a binary forest, the children of `B ∪ C` are `B` and `C`. -/
private theorem IsGoodForest.childClusters_eq {G : Finset (Finset L)} (hG : IsForest G)
    {B C : Finset L} (hB : B ∈ G) (hC : C ∈ G) (hBC : Disjoint B C) :
    childClusters G (B ∪ C) = {B, C} := by
  have hBne := hG.1 B hB
  have hCne := hG.1 C hC
  have hBA : B ⊂ B ∪ C := subset_union_left.ssubset_of_ne fun h => by
    obtain ⟨y, hy⟩ := hCne
    exact disjoint_left.1 hBC (h ▸ mem_union_right B hy) hy
  have hCA : C ⊂ B ∪ C := subset_union_right.ssubset_of_ne fun h => by
    obtain ⟨y, hy⟩ := hBne
    exact disjoint_right.1 hBC (h ▸ mem_union_left C hy) hy
  -- a cluster strictly between `B` and `B ∪ C` would meet both `B` and `C`
  have between : ∀ {P Q : Finset L}, P ∈ G → Q ∈ G → Disjoint P Q → P.Nonempty →
      ∀ D ∈ G, P ⊂ D → D ⊂ P ∪ Q → False := by
    intro P Q hP hQ hPQ hPne D hD hPD hDA
    obtain ⟨y, hyD, hyP⟩ := not_subset.1 hPD.2
    have hyQ : y ∈ Q := by
      rcases mem_union.1 (hDA.subset hyD) with h | h
      · exact absurd h hyP
      · exact h
    rcases hG.2 D hD Q hQ with h | h | h
    · obtain ⟨z, hz⟩ := hPne
      exact disjoint_left.1 hPQ hz (h (hPD.subset hz))
    · exact hDA.2 (union_subset hPD.subset h)
    · exact disjoint_left.1 h hyD hyQ
  ext D
  rw [mem_childClusters, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hD, hDA, hmax⟩
    obtain ⟨x, hx⟩ := hG.1 D hD
    rcases mem_union.1 (hDA.subset hx) with hxB | hxC
    · left
      rcases hG.2 D hD B hB with h | h | h
      · by_contra hne
        exact hmax B hB (h.ssubset_of_ne hne) hBA
      · by_contra hne
        exact between hB hC hBC hBne D hD (h.ssubset_of_ne (Ne.symm hne)) hDA
      · exact absurd hxB (disjoint_left.1 h hx)
    · right
      rcases hG.2 D hD C hC with h | h | h
      · by_contra hne
        exact hmax C hC (h.ssubset_of_ne hne) hCA
      · by_contra hne
        rw [union_comm] at hDA
        exact between hC hB hBC.symm hCne D hD (h.ssubset_of_ne (Ne.symm hne)) hDA
      · exact absurd hxC (disjoint_left.1 h hx)
  · rintro (rfl | rfl)
    · exact ⟨hB, hBA, fun E hE hDE hEA => between hB hC hBC hBne E hE hDE hEA⟩
    · refine ⟨hC, hCA, fun E hE hDE hEA => ?_⟩
      rw [union_comm] at hEA
      exact between hC hB hBC.symm hCne E hE hDE hEA

/-- The binary rooted trees on the lineages are the binary forests with one root and all the
lineages. -/
theorem isGoodForest_iff_binaryHierarchy [Nonempty L] {G : Finset (Finset L)} :
    IsBinaryHierarchy G ↔ IsGoodForest G ∧ lineages G = univ ∧ #(roots G) = 1 := by
  rw [isBinaryHierarchy_iff_card_childClusters]
  constructor
  · rintro ⟨hH, hbin⟩
    have hlin : lineages G = univ := eq_univ_of_forall fun x =>
      mem_lineages.2 ⟨univ, hH.1, mem_univ x⟩
    refine ⟨⟨⟨hH.2.2.1, hH.2.2.2⟩, fun A hA h2 => ?_⟩, hlin, ?_⟩
    · obtain ⟨B, C, hBC, hch⟩ := card_eq_two.1 (hbin A hA h2)
      have hBm : B ∈ childClusters G A := hch ▸ mem_insert_self _ _
      have hCm : C ∈ childClusters G A := hch ▸ mem_insert_of_mem (mem_singleton_self _)
      refine ⟨B, childClusters_subset G A hBm, C, childClusters_subset G A hCm,
        hH.disjoint_of_mem_childClusters hBm hCm hBC, ?_⟩
      have hs := hH.sup_childClusters h2
      rw [hch] at hs
      simpa using hs
    · refine card_eq_one.2 ⟨univ, ?_⟩
      ext A
      rw [mem_roots, mem_singleton]
      constructor
      · rintro ⟨-, hmax⟩
        exact (hmax univ hH.1 (subset_univ A)).symm
      · rintro rfl
        exact ⟨hH.1, fun B _ hB => eq_univ_of_forall fun x => hB (mem_univ x)⟩
  · rintro ⟨hgood, hlin, hone⟩
    have huniv : univ ∈ G := by
      have := lineages_mem_of_card_roots_eq_one hone
      rwa [hlin] at this
    have hH : IsHierarchy G := by
      refine ⟨huniv, fun x => hgood.singleton_mem huniv (mem_univ x), hgood.1.1, hgood.1.2⟩
    refine ⟨hH, fun A hA h2 => ?_⟩
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hgood.2 A hA h2
    rw [IsGoodForest.childClusters_eq hgood.1 hB hC hBC, card_pair]
    rintro rfl
    obtain ⟨y, hy⟩ := hgood.1.1 B hB
    exact disjoint_left.1 hBC hy hy

/-- A nonempty binary forest on all the lineages can be completed to a binary rooted tree. -/
theorem exists_binary_completion {F : Finset (Finset L)} (hF : IsGoodForest F)
    (hne : F.Nonempty) (hlin : lineages F = univ) :
    ∃ G, F ⊆ G ∧ IsGoodForest G ∧ lineages G = univ ∧ #(roots G) = 1 := by
  obtain ⟨G, hG⟩ : ∃ G, kingmanAbsorption F G ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := kingmanAbsorption_sum hF.1
    simp [h] at h1
  obtain ⟨h1, h2, h3, h4⟩ := kingmanAbsorption_support_good hF hG
  exact ⟨G, h2, h1, h3.trans hlin, h4 hne⟩

/-! ### Positivity of the absorption -/

/-- From a sub-forest of a binary tree `G`, closed under subclusters of `G` and containing all the
singletons, the coalescent above the root reaches `G` with positive probability. -/
private theorem kingmanAbsorption_pos_of_lowerClosed {G : Finset (Finset L)} (hG : IsGoodForest G)
    (hone : #(roots G) = 1) {F : Finset (Finset L)} (hFG : F ⊆ G)
    (hsing : ∀ A ∈ G, #A = 1 → A ∈ F)
    (hlow : ∀ A ∈ F, ∀ B ∈ G, B ⊆ A → B ∈ F) : 0 < kingmanAbsorption F G := by
  induction h : #(G \ F) using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    have hF : IsForest F := hG.1.subset hFG
    by_cases hempty : G \ F = ∅
    · have hFe : F = G := Subset.antisymm hFG (sdiff_eq_empty_iff_subset.1 hempty)
      subst hFe
      rw [kingmanAbsorption_apply hF, ite_eq_right (by omega), ite_eq_left hone, hone,
        Nat.sub_self, pow_zero, Matrix.one_apply_eq]
      exact one_pos
    · -- a smallest cluster of `G` not yet formed
      obtain ⟨A, hA, hmin⟩ := exists_min_image (G \ F) card (nonempty_iff_ne_empty.2 hempty)
      obtain ⟨hAG, hAF⟩ := mem_sdiff.1 hA
      have hA2 : 2 ≤ #A := by
        by_contra hlt
        have hpos := (hG.1.1 A hAG).card_pos
        exact hAF (hsing A hAG (by omega))
      obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hG.2 A hAG hA2
      have hBne := hG.1.1 B hB
      have hCne := hG.1.1 C hC
      have hBA : #B < #(B ∪ C) := card_lt_card (subset_union_left.ssubset_of_ne fun h => by
        obtain ⟨y, hy⟩ := hCne
        exact disjoint_left.1 hBC (h ▸ mem_union_right B hy) hy)
      have hCA : #C < #(B ∪ C) := card_lt_card (subset_union_right.ssubset_of_ne fun h => by
        obtain ⟨y, hy⟩ := hBne
        exact disjoint_right.1 hBC (h ▸ mem_union_left C hy) hy)
      have hsmall : ∀ D ∈ G, #D < #(B ∪ C) → D ∈ F := by
        intro D hD hlt
        by_contra hDF
        exact absurd (hmin D (mem_sdiff.2 ⟨hD, hDF⟩)) (not_le.2 hlt)
      have hBF := hsmall B hB hBA
      have hCF := hsmall C hC hCA
      -- `B` and `C` are roots of `F`
      have hroot : ∀ {P Q : Finset L}, P ∈ F → Q ∈ F → Disjoint P Q → P.Nonempty → Q.Nonempty →
          P ∪ Q ∉ F → P ∪ Q ∈ G → P ∈ roots F := by
        intro P Q hP hQ hPQ hPne hQne hUF hUG
        refine mem_roots.2 ⟨hP, fun D hD hPD => ?_⟩
        by_contra hne
        have hDG := hFG hD
        obtain ⟨z, hz⟩ := hPne
        rcases hG.1.2 D hDG _ hUG with h | h | h
        · obtain ⟨y, hyD, hyP⟩ := not_subset.1 ((hPD.ssubset_of_ne (Ne.symm hne)).2)
          have hyQ : y ∈ Q := by
            rcases mem_union.1 (h hyD) with h' | h'
            · exact absurd h' hyP
            · exact h'
          rcases hG.1.2 D hDG Q (hFG hQ) with h' | h' | h'
          · exact disjoint_left.1 hPQ hz (h' (hPD hz))
          · exact hUF (by
              have : P ∪ Q = D := Subset.antisymm (union_subset hPD h') h
              rwa [this])
          · exact disjoint_left.1 h' hyD hyQ
        · exact hUF (hlow D hD _ hUG h)
        · exact disjoint_left.1 h (hPD hz) (mem_union_left Q hz)
      have hBr : B ∈ roots F := hroot hBF hCF hBC hBne hCne hAF hAG
      have hCr : C ∈ roots F := hroot hCF hBF hBC.symm hCne hBne (by rwa [union_comm])
        (by rwa [union_comm])
      have hne : B ≠ C := by
        rintro rfl
        obtain ⟨y, hy⟩ := hBne
        exact disjoint_left.1 hBC hy hy
      have hk : 2 ≤ #(roots F) := one_lt_card.2 ⟨B, hBr, C, hCr, hne⟩
      have hm : insert (B ∪ C) F ∈ merges F := mem_merges.2 ⟨B, hBr, C, hCr, hne, rfl⟩
      have hpos : 0 < kingmanAbsorption (insert (B ∪ C) F) G := by
        refine ih #(G \ insert (B ∪ C) F) ?_ (insert_subset hAG hFG) ?_ ?_ rfl
        · rw [← h]
          refine card_lt_card ⟨sdiff_subset_sdiff (Finset.Subset.refl _) (subset_insert _ _),
            fun hsub => ?_⟩
          have := hsub hA
          simp at this
        · exact fun D hD hD1 => mem_insert_of_mem (hsing D hD hD1)
        · intro D hD E hE hED
          rcases mem_insert.1 hD with rfl | hD
          · by_cases hEe : E = B ∪ C
            · exact hEe ▸ mem_insert_self _ _
            · exact mem_insert_of_mem (hsmall E hE (card_lt_card (hED.ssubset_of_ne hEe)))
          · exact mem_insert_of_mem (hlow D hD E hE hED)
      rw [kingmanAbsorption_first_step hF hk]
      have hC0 : (0 : ℝ) < ((#(roots F)).choose 2 : ℕ) := by
        exact_mod_cast Nat.choose_pos hk
      refine mul_pos (inv_pos.2 hC0) ?_
      refine lt_of_lt_of_le hpos ?_
      exact single_le_sum (f := fun F' => kingmanAbsorption F' G)
        (fun F' hF' => kingmanAbsorption_nonneg (hF.of_mem_merges hF').1 G) hm

/-- From the forest of uncoalesced lineages, every binary rooted tree has positive probability. -/
theorem kingmanAbsorption_singletons_pos {G : Finset (Finset L)} (hG : IsGoodForest G)
    (hlin : lineages G = univ) (hone : #(roots G) = 1) :
    0 < kingmanAbsorption (univ.image fun l => ({l} : Finset L)) G := by
  have huniv : univ ∈ G := by
    have := lineages_mem_of_card_roots_eq_one hone
    rwa [hlin] at this
  refine kingmanAbsorption_pos_of_lowerClosed hG hone ?_ ?_ ?_
  · intro A hA
    obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    exact hG.singleton_mem huniv (mem_univ l)
  · intro A _ hA1
    obtain ⟨l, rfl⟩ := card_eq_one.1 hA1
    exact mem_image_of_mem _ (mem_univ l)
  · intro A hA B hB hBA
    obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    obtain ⟨y, hy⟩ := hG.1.1 B hB
    have : B = {l} := Subset.antisymm hBA (by
      rw [singleton_subset_iff]
      rwa [mem_singleton.1 (hBA hy)] at hy)
    rw [this]
    exact mem_image_of_mem _ (mem_univ l)

/-- A good forest is the union of its parts below two complementary sets of roots, and these
parts have disjoint lineages. -/
theorem forestBelow_union {F A : Finset (Finset L)} (hF : IsGoodForest F) (hA : A ⊆ roots F) :
    forestBelow F A ∪ forestBelow F (roots F \ A) = F ∧
      Disjoint (lineages (forestBelow F A))
        (lineages (forestBelow F (roots F \ A))) := by
  refine ⟨Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _)) fun B hB => ?_,
    ?_⟩
  · obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    by_cases hRA : R ∈ A
    · exact mem_union_left _ (mem_forestBelow.2 ⟨hB, R, hRA, hBR⟩)
    · exact mem_union_right _ (mem_forestBelow.2 ⟨hB, R, mem_sdiff.2 ⟨hR, hRA⟩, hBR⟩)
  · rw [lineages_forestBelow hA, lineages_forestBelow sdiff_subset, Finset.disjoint_sup_left]
    intro C hC
    rw [Finset.disjoint_sup_right]
    intro D hD
    have hCD : C ≠ D := fun h => (mem_sdiff.1 hD).2 (h ▸ hC)
    exact hF.1.disjoint_of_mem_roots (hA hC) (mem_sdiff.1 hD).1 hCD

/-! ### Deprecated names -/

@[deprecated (since := "2026-10-31")] alias model_IsBinaryForest := IsBinaryForest
@[deprecated (since := "2026-10-31")] alias model_isBinaryForest_merge := isBinaryForest_merge
@[deprecated (since := "2026-10-31")] alias model_isBinaryForest_of_jumpMatrix_pow :=
  isBinaryForest_of_jumpMatrix_pow
@[deprecated (since := "2026-10-31")] alias IsGood := IsGoodForest
@[deprecated (since := "2026-10-31")] alias isGood_empty := isGoodForest_empty
@[deprecated (since := "2026-10-31")] alias isGood_singletons := isGoodForest_singletons
@[deprecated (since := "2026-10-31")] alias IsGood.union := IsGoodForest.union
@[deprecated (since := "2026-10-31")] alias isGood_forestBelow := isGoodForest_forestBelow
@[deprecated (since := "2026-10-31")] alias kingmanTransition_support_isGood :=
  kingmanTransition_support_good
@[deprecated (since := "2026-10-31")] alias kingmanAbsorption_support :=
  kingmanAbsorption_support_good
@[deprecated (since := "2026-10-31")] alias lineages_singletons := lineages_image_singleton

end Phylogenetics
