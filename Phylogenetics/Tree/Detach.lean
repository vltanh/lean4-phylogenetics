module

public import Phylogenetics.Tree.Splice

/-!
# Refining trees, detaching and reattaching taxa, and scores by sets of four taxa

Operations on trees given by the sides of their splits, used by Dai, Han, Molloy (2026).

* `exists_refinement_displays`: a quartet that a tree does not resolve can be resolved, in any of the
  three ways, by a refinement;
* `isBinaryTree_of_forall_displays`: a tree resolving every set of four taxa is binary;
* `exists_ssubset_of_not_isBinaryTree`, `quartetSupport_lt_of_ssubset`: a tree that is not binary has a
  proper refinement, and a proper refinement increases a score with positive weights;
* `exists_mem_multifurcations_isBlockUnion`: refining a tree only resolves its multifurcations;
* `detachReattach a b T`: the tree `T` with the taxon `b` detached and reattached as sister to `a`, as
  the restriction of `T` along the retraction `b ↦ a` with the new pendant edges of `a` and `b`;
  `displays_detachReattach_of_not_mem` and `displays_detachReattach_of_mem` give what it displays;
* `quartetPart`, `sum_ite_eq_sum_powersetCard`, `quartetSupport_eq_sum_quartetPart`,
  `quartetPart_of_displays`, `quartetPart_lt_of_not_displays`: a score as a sum over the sets of four
  taxa.

## References

* J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of
  blobs reconstruction under the network multispecies coalescent*, Genome Res., doi
  10.1101/gr.282203.126.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]


/-! ### Refining a tree at a multifurcation -/

theorem IsBlockUnion.compl {P : Finset (Finset X)} {A : Finset X} (hA : IsBlockUnion P A) :
    IsBlockUnion P Aᶜ := fun B hB => by
  rcases hA B hB with h | h
  · exact Or.inr (disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (h hx))
  · exact Or.inl fun x hx => mem_compl.2 (disjoint_left.1 h hx)

/-- A split that is a union of blocks can be added at a vertex. -/
theorem isBlockFamily_pair {P : Finset (Finset X)} {A : Finset X} (hA : IsBlockUnion P A)
    (hne : A.Nonempty) (hne' : Aᶜ.Nonempty) : IsBlockFamily P {A, Aᶜ} := by
  have hmem : ∀ B ∈ ({A, Aᶜ} : Finset (Finset X)), B = A ∨ B = Aᶜ := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases hmem B hB with rfl | rfl
    · exact hA
    · exact hA.compl
  · intro B hB
    rcases hmem B hB with rfl | rfl
    · exact hne
    · exact hne'
  · intro B hB
    rcases hmem B hB with rfl | rfl
    · exact hne'
    · rwa [compl_compl]
  · intro B hB
    rcases hmem B hB with rfl | rfl <;> simp
  · intro B hB B' hB'
    rcases hmem B hB with rfl | rfl <;> rcases hmem B' hB' with rfl | rfl
    · exact Or.inl (Subset.refl _)
    · exact Or.inr (Or.inr (Or.inl disjoint_compl_right))
    · exact Or.inr (Or.inr (Or.inl disjoint_compl_left))
    · exact Or.inl (Subset.refl _)

/-- A quartet that a tree does not resolve can be resolved, in any of the three ways, by a refinement:
the split of its cherries into two sets of blocks at its centre is compatible with the tree. -/
theorem exists_refinement_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T) (s : QuartetTree X)
    (hstar : ∀ r ∈ treesOn s.taxa, ¬ Displays T r) :
    ∃ T', IsUnrootedTree T' ∧ T ⊆ T' ∧ Displays T' s := by
  obtain ⟨P, ⟨hP, hI⟩, -⟩ := existsUnique_center hT s.card_taxa hstar
  obtain ⟨hV, -⟩ := mem_multifurcations.1 hP
  obtain ⟨C, hC⟩ : ∃ C, C ∈ s.val := card_pos.1 (by rw [s.property.1]; omega)
  have hCc := s.card_of_mem hC
  have hCc' := s.card_of_mem (s.sdiff_mem hC)
  let A : Finset X := (P.filter fun B => (B ∩ C).Nonempty).biUnion id
  have hAmem : ∀ x, x ∈ A ↔ ∃ B ∈ P, (B ∩ C).Nonempty ∧ x ∈ B := by
    intro x
    simp [A, mem_biUnion, and_assoc]
  have hAu : IsBlockUnion P A := by
    intro B hB
    by_cases hBC : (B ∩ C).Nonempty
    · exact Or.inl fun x hx => (hAmem x).2 ⟨B, hB, hBC, hx⟩
    · refine Or.inr (disjoint_left.2 fun x hx hxA => ?_)
      obtain ⟨B', hB', hB'C, hxB'⟩ := (hAmem x).1 hxA
      by_cases he : B = B'
      · exact hBC (he ▸ hB'C)
      · exact disjoint_left.1 (hV.pairwiseDisjoint B hB B' hB' he) hx hxB'
  have htrace : A ∩ s.taxa = C := by
    ext x
    rw [mem_inter]
    constructor
    · rintro ⟨hxA, hxq⟩
      obtain ⟨B, hB, ⟨y, hy⟩, hxB⟩ := (hAmem x).1 hxA
      obtain ⟨hyB, hyC⟩ := mem_inter.1 hy
      have : x = y := card_le_one.1 (hI B hB) x (mem_inter.2 ⟨hxB, hxq⟩) y
        (mem_inter.2 ⟨hyB, s.subset_taxa hC hyC⟩)
      exact this ▸ hyC
    · intro hx
      obtain ⟨B, hB, hxB⟩ := hV.exists_mem_block x
      exact ⟨(hAmem x).2 ⟨B, hB, ⟨x, mem_inter.2 ⟨hxB, hx⟩⟩, hxB⟩, s.subset_taxa hC hx⟩
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < C.card by omega)
    exact ⟨x, (mem_inter.1 (htrace.symm ▸ hx : x ∈ A ∩ s.taxa)).1⟩
  have hAne' : Aᶜ.Nonempty := by
    obtain ⟨y, hy⟩ := card_pos.1 (show 0 < (s.taxa \ C).card by omega)
    obtain ⟨hy1, hy2⟩ := mem_sdiff.1 hy
    exact ⟨y, mem_compl.2 fun hyA => hy2 (htrace ▸ mem_inter.2 ⟨hyA, hy1⟩)⟩
  let L : Finset (Finset X) → Finset (Finset X) := fun P' => if P' = P then {A, Aᶜ} else ∅
  have hL : ∀ P' ∈ multifurcations T, IsBlockFamily P' (L P') := by
    intro P' _
    by_cases he : P' = P
    · subst he
      have hfam : L P' = {A, Aᶜ} := by simp [L]
      rw [hfam]
      exact isBlockFamily_pair hAu hAne hAne'
    · have hfam : L P' = ∅ := by simp [L, he]
      rw [hfam]
      exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨splice T L, splice_isUnrootedTree hT hL, subset_splice T L, A, ?_, htrace ▸ hC⟩
  exact mem_splice.2 (Or.inr ⟨P, hP, by simp [L]⟩)

/-- A tree without multifurcations is binary: its rooting at a taxon. -/
theorem isBinaryTree_of_forall_not_mem_multifurcations {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hnoM : ∀ P, ¬ (P ∈ multifurcations T)) : IsBinaryTree T := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hSF := hT.isSplitFamily hX
    obtain ⟨r⟩ : Nonempty X := Fintype.card_pos_iff.1 (by omega)
    have hH := rootedAt_isHierarchy hSF r
    have hun := unroot_rootedAt hSF r
    refine ⟨rootedAt T r, hH, hun, fun A hA hA2 => ?_⟩
    apply le_antisymm _ (hH.two_le_card_childClusters hA2)
    by_cases hAu : A = univ
    · subst hAu
      have hsub : childClusters (rootedAt T r) univ ⊆ {{r}, {r}ᶜ} := by
        intro B hB
        obtain ⟨hBH, hBu, hmaxB⟩ := mem_childClusters.1 hB
        rcases mem_rootedAt.1 hBH with rfl | rfl | ⟨hBT, hrB⟩
        · exact absurd hBu (ssubset_irrefl _)
        · simp
        · by_cases he : B = {r}ᶜ
          · simp [he]
          · exfalso
            have hBs : B ⊂ {r}ᶜ := ssubset_of_subset_of_ne (fun y hy => by
              simp only [mem_compl, mem_singleton]
              rintro rfl
              exact hrB hy) he
            refine hmaxB {r}ᶜ (mem_rootedAt.2 (Or.inr (Or.inr
              ⟨hSF.compl_mem _ (hSF.singleton_mem r), by simp⟩))) hBs ?_
            refine ssubset_univ_iff.2 fun h => ?_
            have : r ∈ ({r} : Finset X)ᶜ := h ▸ mem_univ r
            simp at this
      exact (card_le_card hsub).trans card_le_two
    · have hVP := hH.isVertexPartition_insert_compl hA hAu hA2
      rw [hun] at hVP
      have hnot4 : ¬ 4 ≤ (insert Aᶜ (childClusters (rootedAt T r) A)).card := fun h =>
        hnoM _ (mem_multifurcations.2 ⟨hVP, h⟩)
      have hnotin : Aᶜ ∉ childClusters (rootedAt T r) A := by
        intro h
        obtain ⟨h1, h2, -⟩ := mem_childClusters.1 h
        obtain ⟨y, hy⟩ := hH.2.2.1 _ h1
        exact mem_compl.1 hy (h2.subset hy)
      rw [card_insert_of_notMem hnotin] at hnot4
      omega
  · obtain ⟨H, hH, hu⟩ := hT
    exact ⟨H, hH, hu, fun A _ hA2 => absurd (hA2.trans (card_le_univ A)) hX⟩

/-- A tree resolving every set of four taxa is binary. -/
theorem isBinaryTree_of_forall_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (h : ∀ q : Finset X, q.card = 4 → ∃ s ∈ treesOn q, Displays T s) : IsBinaryTree T := by
  refine isBinaryTree_of_forall_not_mem_multifurcations hT fun P hP => ?_
  obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
  obtain ⟨x, hx⟩ := exists_isRepTuple fun B hB => hT.nonempty_of_mem (hV.mem B hB)
  have hinj := hx.injective hV.pairwiseDisjoint
  obtain ⟨D, -, hDc⟩ := exists_subset_card_eq (s := (univ : Finset {B // B ∈ P})) (n := 4) (by
    rw [card_univ, Fintype.card_coe]; exact h4)
  obtain ⟨s, hs, hd⟩ := h (D.image x) (by rw [card_image_of_injective _ hinj, hDc])
  have hst := mem_treesOn.1 hs
  exact not_displays_of_inDistinctBlocks hV (s := s)
    (hx.inDistinctBlocks hV.pairwiseDisjoint (by rw [hst]; exact image_subset_image (subset_univ _))) hd

theorem IsBinaryTree.isUnrootedTree {T : Finset (Finset X)} (hT : IsBinaryTree T) :
    IsUnrootedTree T := by
  obtain ⟨H, hH, hu, -⟩ := hT
  exact ⟨H, hH, hu⟩

/-- A tree that is not binary has a proper refinement. -/
theorem exists_ssubset_of_not_isBinaryTree {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (h : ¬ IsBinaryTree T) : ∃ R, IsUnrootedTree R ∧ T ⊂ R := by
  obtain ⟨q, hq, hnot⟩ : ∃ q : Finset X, q.card = 4 ∧ ∀ s ∈ treesOn q, ¬ Displays T s := by
    by_contra hcon
    push Not at hcon
    exact h (isBinaryTree_of_forall_displays hT hcon)
  obtain ⟨C, hCq, hCc⟩ := exists_subset_card_eq (s := q) (n := 2) (by omega)
  let s := quartetOfCherry q C hq hCq hCc
  have hst : s.taxa = q := quartetOfCherry_taxa q C hq hCq hCc
  obtain ⟨R, hR, hsub, hd⟩ := exists_refinement_displays hT s (fun r hr => hnot r (hst ▸ hr))
  refine ⟨R, hR, ssubset_of_subset_of_ne hsub ?_⟩
  rintro rfl
  exact hnot s (mem_treesOn.2 hst) hd

/-- Any proper refinement of a tree increases a score with positive weights. -/
theorem quartetSupport_lt_of_ssubset {w : QuartetTree X → ℝ} (hw : ∀ s, 0 < w s)
    {T T' : Finset (Finset X)} (hT : IsUnrootedTree T) (hT' : IsUnrootedTree T') (h : T ⊂ T') :
    quartetSupport w T < quartetSupport w T' := by
  obtain ⟨s, hs, hnot⟩ : ∃ s, Displays T' s ∧ ¬ Displays T s := by
    by_contra hcon
    push Not at hcon
    exact h.2 (subset_of_forall_displays hT hT' hcon)
  refine sum_lt_sum (fun r _ => ?_) ⟨s, mem_univ _, ?_⟩
  · by_cases hr : Displays T r
    · simp only [hr, hr.mono h.subset, ↓reduceIte, le_refl]
    · simp only [hr, ↓reduceIte]
      split_ifs
      · exact (hw r).le
      · exact le_refl _
  · simp only [hs, hnot, ↓reduceIte]
    exact hw s

/-- A side of a refinement of a tree that is not a side of the tree is a union of blocks at a
multifurcation of the tree: refining a tree only resolves its multifurcations. -/
theorem exists_mem_multifurcations_isBlockUnion {T T' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hT' : IsUnrootedTree T') (hsub : T ⊆ T') {A : Finset X} (hA : A ∈ T') (hnot : A ∉ T) :
    ∃ P ∈ multifurcations T, IsBlockUnion P A := by
  have hSF := hT.isSplitFamily (hT'.two_le_card_of_mem hA)
  have hAne := hT'.nonempty_of_mem hA
  obtain ⟨r, hrA⟩ : ∃ r, r ∉ A := by
    obtain ⟨r, hr⟩ := hT'.nonempty_of_mem (hT'.compl_mem hA)
    exact ⟨r, mem_compl.1 hr⟩
  have hH := rootedAt_isHierarchy hSF r
  obtain ⟨K, hK, hAK, hleast⟩ := hH.exists_least hAne
  have hrc : ({r} : Finset X)ᶜ ∈ rootedAt T r :=
    mem_rootedAt.2 (Or.inr (Or.inr ⟨hSF.compl_mem _ (hSF.singleton_mem r), by simp⟩))
  have hKr : K ⊆ {r}ᶜ := hleast _ hrc fun x hx => by
    simp only [mem_compl, mem_singleton]
    rintro rfl
    exact hrA hx
  have hrK : r ∉ K := fun h => (by simpa using hKr h : r ≠ r) rfl
  have hKu : K ≠ univ := fun h => hrK (h ▸ mem_univ r)
  have hKT : K ∈ T := by
    rcases mem_rootedAt.1 hK with h | h | h
    · exact absurd h hKu
    · exact absurd (h ▸ mem_singleton_self r) hrK
    · exact h.1
  have hAK' : A ⊂ K := ssubset_of_subset_of_ne hAK fun e => hnot (e ▸ hKT)
  have hK2 : 2 ≤ K.card := by
    have h1 := card_lt_card hAK'
    have h2 := card_pos.2 hAne
    omega
  have hVP := hH.isVertexPartition_insert_compl hK hKu hK2
  rw [unroot_rootedAt hSF r] at hVP
  have hchildT : ∀ D ∈ childClusters (rootedAt T r) K, D ∈ T := fun D hD =>
    hVP.mem D (mem_insert_of_mem hD)
  have hchild : ∀ D ∈ childClusters (rootedAt T r) K, D ⊆ A ∨ Disjoint D A := by
    intro D hD
    obtain ⟨hDH, hDK, -⟩ := mem_childClusters.1 hD
    rcases hT'.compatible (hsub (hchildT D hD)) hA with h | h | h | h
    · exact Or.inl h
    · exact absurd (hleast D hDH h) (not_subset_of_ssubset hDK)
    · exact Or.inr h
    · rcases mem_union.1 (h ▸ mem_univ r : r ∈ D ∪ A) with h' | h'
      · exact absurd (hDK.subset h') hrK
      · exact absurd h' hrA
  refine ⟨_, mem_multifurcations.2 ⟨hVP, ?_⟩, fun B hB => ?_⟩
  · -- two children inside `A` and one outside, with the complement of `K`
    have hinside : ∀ {a}, a ∈ A → ∃ D ∈ childClusters (rootedAt T r) K, a ∈ D ∧ D ⊆ A := by
      intro a ha
      obtain ⟨D, hD, haD⟩ := hH.exists_mem_childClusters hK2 (hAK ha)
      exact ⟨D, hD, haD, (hchild D hD).resolve_right fun h => disjoint_left.1 h haD ha⟩
    obtain ⟨a₁, ha₁⟩ := hAne
    obtain ⟨D₁, hD₁, -, hD₁A⟩ := hinside ha₁
    obtain ⟨a₂, ha₂, ha₂D₁⟩ : ∃ a₂ ∈ A, a₂ ∉ D₁ := by
      by_contra hcon
      push Not at hcon
      exact hnot (Subset.antisymm hD₁A hcon ▸ hchildT D₁ hD₁)
    obtain ⟨D₂, hD₂, ha₂D₂, hD₂A⟩ := hinside ha₂
    obtain ⟨y, hyK, hyA⟩ := exists_of_ssubset hAK'
    obtain ⟨D₃, hD₃, hyD₃⟩ := hH.exists_mem_childClusters hK2 hyK
    have h12 : D₁ ≠ D₂ := fun e => ha₂D₁ (e ▸ ha₂D₂)
    have h13 : D₁ ≠ D₃ := fun e => hyA (hD₁A (e ▸ hyD₃))
    have h23 : D₂ ≠ D₃ := fun e => hyA (hD₂A (e ▸ hyD₃))
    have hnotin : Kᶜ ∉ childClusters (rootedAt T r) K := by
      intro h
      obtain ⟨h1, h2, -⟩ := mem_childClusters.1 h
      obtain ⟨z, hz⟩ := hH.2.2.1 _ h1
      exact mem_compl.1 hz (h2.subset hz)
    have hcard : ({D₁, D₂, D₃} : Finset (Finset X)).card = 3 := by
      rw [card_insert_of_notMem (by simp [h12, h13]), card_pair h23]
    have hle : ({D₁, D₂, D₃} : Finset (Finset X)).card ≤
        (childClusters (rootedAt T r) K).card := card_le_card fun D hD => by
      simp only [mem_insert, mem_singleton] at hD
      rcases hD with rfl | rfl | rfl
      · exact hD₁
      · exact hD₂
      · exact hD₃
    rw [card_insert_of_notMem hnotin]
    omega
  · rcases mem_insert.1 hB with rfl | hB
    · exact Or.inr (disjoint_left.2 fun y hy hyA => mem_compl.1 hy (hAK hyA))
    · exact hchild B hB

/-! ### Detaching a taxon and reattaching it as sister to another -/

/-- The retraction `b ↦ a`. -/
def retract (a b : X) : X → X := fun x => if x = b then a else x

omit [Fintype X] in
@[simp] theorem retract_right (a b : X) : retract a b b = a := by simp [retract]

omit [Fintype X] in
theorem retract_of_ne {a b x : X} (h : x ≠ b) : retract a b x = x := by simp [retract, h]

/-- The tree `T` with the taxon `b` detached and reattached as sister to `a`: the restriction of `T`
along the retraction `b ↦ a`, in which the pendant edge of `a` becomes the edge above the cherry `{a, b}`,
with the new pendant edges of `a` and `b`. -/
def detachReattach (a b : X) (T : Finset (Finset X)) : Finset (Finset X) :=
  pullTree (retract a b) T ∪ {{a}, {a}ᶜ, {b}, {b}ᶜ}

private theorem compat_singleton (x : X) (A : Finset X) :
    ({x} : Finset X) ⊆ A ∨ A ⊆ {x} ∨ Disjoint {x} A ∨ {x} ∪ A = univ := by
  by_cases h : x ∈ A
  · exact Or.inl (singleton_subset_iff.2 h)
  · exact Or.inr (Or.inr (Or.inl (disjoint_singleton_left.2 h)))

private theorem compat_compl_singleton (x : X) (A : Finset X) :
    ({x} : Finset X)ᶜ ⊆ A ∨ A ⊆ {x}ᶜ ∨ Disjoint {x}ᶜ A ∨ {x}ᶜ ∪ A = univ := by
  by_cases h : x ∈ A
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
    by_cases hy : y = x
    · exact mem_union_right _ (hy ▸ h)
    · exact mem_union_left _ (by simpa using hy)
  · refine Or.inr (Or.inl fun y hy => ?_)
    simp only [mem_compl, mem_singleton]
    rintro rfl
    exact h hy

theorem mem_detachReattach {a b : X} {T : Finset (Finset X)} {A : Finset X} :
    A ∈ detachReattach a b T ↔ A ∈ pullTree (retract a b) T ∨
      A = {a} ∨ A = {a}ᶜ ∨ A = {b} ∨ A = {b}ᶜ := by
  simp [detachReattach]
  tauto

/-- Detaching and reattaching a taxon gives a tree. -/
theorem detachReattach_isUnrootedTree {a b : X} {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hab : a ≠ b) : IsUnrootedTree (detachReattach a b T) := by
  have hX : 2 ≤ Fintype.card X := by
    have := card_le_univ ({a, b} : Finset X)
    rwa [card_pair hab] at this
  have hSF := hT.isSplitFamily hX
  have hne : ∀ x : X, ({x} : Finset X)ᶜ.Nonempty := fun x => by
    rw [← card_pos, card_compl, card_singleton]
    omega
  have hcases : ∀ A, A ∈ detachReattach a b T → A ∈ pullTree (retract a b) T ∨
      ∃ x, A = {x} ∨ A = {x}ᶜ := by
    intro A hA
    rcases mem_detachReattach.1 hA with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨a, Or.inl h⟩
    · exact Or.inr ⟨a, Or.inr h⟩
    · exact Or.inr ⟨b, Or.inl h⟩
    · exact Or.inr ⟨b, Or.inr h⟩
  refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases hcases A hA with h | ⟨x, rfl | rfl⟩
    · exact (mem_pullTree.1 h).2.1
    · exact singleton_nonempty x
    · exact hne x
  · intro A hA
    rcases hcases A hA with h | ⟨x, rfl | rfl⟩
    · exact (mem_pullTree.1 h).2.2
    · exact hne x
    · simp
  · intro A hA
    rcases mem_detachReattach.1 hA with h | rfl | rfl | rfl | rfl
    · obtain ⟨⟨C, hC, rfl⟩, h1, h2⟩ := mem_pullTree.1 h
      refine mem_detachReattach.2 (Or.inl (mem_pullTree.2 ⟨⟨Cᶜ, hSF.compl_mem C hC, ?_⟩, h2,
        by rwa [compl_compl]⟩))
      ext y
      simp
    · exact mem_detachReattach.2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact mem_detachReattach.2 (Or.inr (Or.inl (compl_compl _)))
    · exact mem_detachReattach.2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact mem_detachReattach.2 (Or.inr (Or.inr (Or.inr (Or.inl (compl_compl _)))))
  · intro x
    by_cases hxa : x = a
    · exact mem_detachReattach.2 (Or.inr (Or.inl (by rw [hxa])))
    by_cases hxb : x = b
    · exact mem_detachReattach.2 (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hxb])))))
    refine mem_detachReattach.2 (Or.inl (mem_pullTree.2 ⟨⟨{x}, hSF.singleton_mem x, ?_⟩,
      singleton_nonempty x, hne x⟩))
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    by_cases hyb : y = b
    · subst hyb
      simp [Ne.symm hxa]
      exact fun h => hxb h.symm
    · rw [retract_of_ne hyb]
  · intro A hA B hB
    rcases hcases A hA with h | ⟨x, rfl | rfl⟩
    · rcases hcases B hB with h' | ⟨y, rfl | rfl⟩
      · obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 h
        obtain ⟨⟨D, hD, rfl⟩, -, -⟩ := mem_pullTree.1 h'
        rcases hSF.compatible C hC D hD with h | h | h | h
        · exact Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩
        · exact Or.inr (Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩)
        · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun y hy hy' =>
            disjoint_left.1 h (mem_filter.1 hy).2 (mem_filter.1 hy').2)))
        · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
          have : retract a b y ∈ C ∪ D := h ▸ mem_univ _
          rcases mem_union.1 this with h' | h'
          · exact mem_union_left _ (mem_filter.2 ⟨mem_univ y, h'⟩)
          · exact mem_union_right _ (mem_filter.2 ⟨mem_univ y, h'⟩)
      · exact compatible_symm (compat_singleton y _)
      · exact compatible_symm (compat_compl_singleton y _)
    · exact compat_singleton x _
    · exact compat_compl_singleton x _

omit [Fintype X] in
private theorem singleton_inter_not_mem (x : X) (s : QuartetTree X) : {x} ∩ s.taxa ∉ s.val := by
  intro h
  have := s.card_of_mem h
  have h2 := card_le_card (inter_subset_left : ({x} : Finset X) ∩ s.taxa ⊆ {x})
  rw [card_singleton] at h2
  omega

private theorem compl_singleton_inter_not_mem (x : X) (s : QuartetTree X) :
    {x}ᶜ ∩ s.taxa ∉ s.val := by
  intro h
  have h1 := s.card_of_mem (s.sdiff_mem h)
  have h2 : s.taxa \ ({x}ᶜ ∩ s.taxa) ⊆ {x} := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_sdiff.1 hy
    by_contra hyx
    exact hy2 (mem_inter.2 ⟨mem_compl.2 hyx, hy1⟩)
  have h3 := card_le_card h2
  rw [card_singleton] at h3
  omega

private theorem not_special_of_mem_val {a b : X} {s : QuartetTree X} {A : Finset X}
    (h : A ∩ s.taxa ∈ s.val) (hA : A = {a} ∨ A = {a}ᶜ ∨ A = {b} ∨ A = {b}ᶜ) : False := by
  rcases hA with rfl | rfl | rfl | rfl
  · exact singleton_inter_not_mem a s h
  · exact compl_singleton_inter_not_mem a s h
  · exact singleton_inter_not_mem b s h
  · exact compl_singleton_inter_not_mem b s h

/-- A cherry and its complement in the taxa give the restriction of `T` a nontrivial side. -/
private theorem mem_pullTree_of_trace {a b : X} {T : Finset (Finset X)} {C : Finset X} (hC : C ∈ T)
    {s : QuartetTree X} (h : (univ.filter fun y => retract a b y ∈ C) ∩ s.taxa ∈ s.val) :
    (univ.filter fun y => retract a b y ∈ C) ∈ pullTree (retract a b) T := by
  have hc := s.card_of_mem h
  have hc' := s.card_of_mem (s.sdiff_mem h)
  refine mem_pullTree.2 ⟨⟨C, hC, rfl⟩, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < _ by omega :
      0 < ((univ.filter fun y => retract a b y ∈ C) ∩ s.taxa).card)
    exact ⟨y, (mem_inter.1 hy).1⟩
  · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < _ by omega :
      0 < (s.taxa \ ((univ.filter fun y => retract a b y ∈ C) ∩ s.taxa)).card)
    obtain ⟨hy1, hy2⟩ := mem_sdiff.1 hy
    exact ⟨y, mem_compl.2 fun hy3 => hy2 (mem_inter.2 ⟨hy3, hy1⟩)⟩

/-- A quartet without `b` is not affected by detaching `b`. -/
theorem displays_detachReattach_of_not_mem {a b : X} {T : Finset (Finset X)} {s : QuartetTree X}
    (hb : b ∉ s.taxa) : Displays (detachReattach a b T) s ↔ Displays T s := by
  have htrace : ∀ C : Finset X, (univ.filter fun y => retract a b y ∈ C) ∩ s.taxa = C ∩ s.taxa := by
    intro C
    ext y
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have hyb : y ≠ b := fun e => hb (e ▸ h2)
      rw [retract_of_ne hyb] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hyb : y ≠ b := fun e => hb (e ▸ h2)
      rw [retract_of_ne hyb]
      exact ⟨h1, h2⟩
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_detachReattach.1 hA with h | h
    · obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 h
      exact ⟨C, hC, htrace C ▸ hAs⟩
    · exact (not_special_of_mem_val hAs h).elim
  · rintro ⟨C, hC, hCs⟩
    have h' := (htrace C).symm ▸ hCs
    exact ⟨_, mem_detachReattach.2 (Or.inl (mem_pullTree_of_trace hC h')), h'⟩

/-- A quartet with `b` and without `a` is displayed after the detachment as the quartet with `a` in
place of `b` was displayed before: `b` is now sister to `a`. -/
theorem displays_detachReattach_of_mem {a b : X} {T : Finset (Finset X)} {s : QuartetTree X}
    (hb : b ∈ s.taxa) (ha : a ∉ s.taxa) :
    Displays (detachReattach a b T) s ↔ Displays T (s.map (Equiv.swap a b).injective) := by
  have hσ : ∀ y ∈ s.taxa, Equiv.swap a b y = retract a b y := by
    intro y hy
    by_cases hyb : y = b
    · subst hyb
      simp
    · have hya : y ≠ a := fun e => ha (e ▸ hy)
      rw [retract_of_ne hyb, Equiv.swap_apply_of_ne_of_ne hya hyb]
  have htrace : ∀ C : Finset X, ((univ.filter fun y => retract a b y ∈ C) ∩ s.taxa).image
      (Equiv.swap a b) = C ∩ s.taxa.image (Equiv.swap a b) := by
    intro C
    ext y
    simp only [mem_image, mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      rw [hσ x h2]
      exact ⟨h1, x, h2, hσ x h2⟩
    · rintro ⟨h1, x, h2, rfl⟩
      rw [hσ x h2] at h1 ⊢
      exact ⟨x, ⟨h1, h2⟩, hσ x h2⟩
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_detachReattach.1 hA with h | h
    · obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 h
      refine ⟨C, hC, ?_⟩
      rw [QuartetTree.map_taxa, ← htrace, QuartetTree.map_val]
      exact mem_image_of_mem _ hAs
    · exact (not_special_of_mem_val hAs h).elim
  · rintro ⟨C, hC, hCs⟩
    rw [QuartetTree.map_taxa, ← htrace, QuartetTree.map_val, mem_image] at hCs
    obtain ⟨D, hD, hDe⟩ := hCs
    have h' : (univ.filter fun y => retract a b y ∈ C) ∩ s.taxa ∈ s.val :=
      image_injective (Equiv.swap a b).injective hDe ▸ hD
    exact ⟨_, mem_detachReattach.2 (Or.inl (mem_pullTree_of_trace hC h')), h'⟩

/-- A side with `a` and without `b` gains `b`. -/
theorem insert_mem_detachReattach {a b : X} {T : Finset (Finset X)} {C : Finset X} (hC : C ∈ T)
    (haC : a ∈ C) (hbC : b ∉ C) (hne : (insert b C)ᶜ.Nonempty) :
    insert b C ∈ detachReattach a b T := by
  have hpre : (univ.filter fun y => retract a b y ∈ C) = insert b C := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hyb : y = b
    · subst hyb
      simpa using haC
    · simp [retract_of_ne hyb, hyb]
  exact mem_detachReattach.2 (Or.inl (mem_pullTree.2 ⟨⟨C, hC, hpre⟩, insert_nonempty _ _, hne⟩))

/-- A side without `a` and `b` stays. -/
theorem mem_detachReattach_of_not_mem {a b : X} {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {C : Finset X} (hC : C ∈ T) (haC : a ∉ C) (hbC : b ∉ C) : C ∈ detachReattach a b T := by
  have hpre : (univ.filter fun y => retract a b y ∈ C) = C := by
    ext y
    simp only [mem_filter, mem_univ, true_and]
    by_cases hyb : y = b
    · subst hyb
      simp [haC, hbC]
    · rw [retract_of_ne hyb]
  exact mem_detachReattach.2 (Or.inl (mem_pullTree.2 ⟨⟨C, hC, hpre⟩, hT.nonempty_of_mem hC,
    hT.nonempty_of_mem (hT.compl_mem hC)⟩))

/-! ### Scores by sets of four taxa -/

/-- What a tree contributes to a score on the set of taxa `q`. -/
def quartetPart (w : QuartetTree X → ℝ) (T : Finset (Finset X)) (q : Finset X) : ℝ :=
  ∑ s ∈ treesOn q, if Displays T s then w s else 0

/-- A sum over quartet trees is a sum over the sets of four taxa. -/
theorem sum_ite_eq_sum_powersetCard (Φ : Finset X → Prop) (w : QuartetTree X → ℝ)
    (T : Finset (Finset X)) :
    (∑ s : QuartetTree X, if Φ s.taxa ∧ Displays T s then w s else 0) =
      ∑ q ∈ powersetCard 4 (univ : Finset X), if Φ q then quartetPart w T q else 0 := by
  have hmaps : ∀ s ∈ (univ : Finset (QuartetTree X)),
      s.taxa ∈ powersetCard 4 (univ : Finset X) := fun s _ =>
    mem_powersetCard.2 ⟨subset_univ _, s.card_taxa⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun q _ => ?_
  have hfil : (univ.filter fun s : QuartetTree X => s.taxa = q) = treesOn q := rfl
  rw [hfil]
  by_cases hΦ : Φ q
  · simp only [hΦ, ↓reduceIte, quartetPart]
    refine sum_congr rfl fun s hs => ?_
    simp only [mem_treesOn.1 hs, hΦ, true_and]
  · simp only [hΦ, ↓reduceIte]
    refine sum_eq_zero fun s hs => ?_
    simp only [mem_treesOn.1 hs, hΦ, false_and, ↓reduceIte]

theorem quartetPart_of_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (w : QuartetTree X → ℝ) {s : QuartetTree X} (hs : Displays T s) :
    quartetPart w T s.taxa = w s := by
  unfold quartetPart
  rw [sum_eq_single_of_mem s (mem_treesOn.2 rfl)]
  · simp only [hs, ↓reduceIte]
  · intro r hr hne
    exact ite_eq_right fun h => hne (hT.displays_unique h hs (mem_treesOn.1 hr))

/-- A tree has at most the largest weight on a set of four taxa, and less if it does not display the
quartet tree of the largest weight. -/
theorem quartetPart_lt_of_not_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {p : QuartetTree X → ℝ} (hp : ∀ s, 0 ≤ p s) {r : QuartetTree X}
    (hr : ∀ r' ∈ r.alternatives, p r' < p r) (hnot : ¬ Displays T r) :
    quartetPart p T r.taxa < p r := by
  unfold quartetPart
  by_cases hex : ∃ s ∈ treesOn r.taxa, Displays T s
  · obtain ⟨s, hs, hds⟩ := hex
    have hsr : s.taxa = r.taxa := mem_treesOn.1 hs
    rw [sum_eq_single_of_mem s hs]
    · simp only [hds, ↓reduceIte]
      refine hr s (QuartetTree.mem_alternatives.2 ⟨hsr, ?_⟩)
      rintro rfl
      exact hnot hds
    · intro s' hs' hne
      exact ite_eq_right fun h => hne (hT.displays_unique h hds
        ((mem_treesOn.1 hs').trans hsr.symm))
  · rw [sum_eq_zero fun s hs => ite_eq_right fun h => hex ⟨s, hs, h⟩]
    obtain ⟨r', hr'⟩ := card_pos.1 (by rw [r.card_alternatives]; omega : 0 < r.alternatives.card)
    exact lt_of_le_of_lt (hp r') (hr r' hr')

/-- The score of a tree is the sum of its parts on the sets of four taxa. -/
theorem quartetSupport_eq_sum_quartetPart (w : QuartetTree X → ℝ) (T : Finset (Finset X)) :
    quartetSupport w T = ∑ q ∈ powersetCard 4 (univ : Finset X), quartetPart w T q := by
  have := sum_ite_eq_sum_powersetCard (fun _ => True) w T
  simpa [quartetSupport] using this

end Phylogenetics
