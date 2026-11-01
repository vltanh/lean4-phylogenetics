module

public import Phylogenetics.Coalescent.Trace
public import Phylogenetics.Hierarchy.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Matrix.Normed

/-!
# Lumpability of Kingman's coalescent, along an embedding of the lineages

[E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862]

Kingman's coalescent is consistent: restricting a forest on `L` to a type of lineages `L'`, along an
embedding `e : L' ↪ L`, lumps the chain into Kingman's coalescent on `L'`. The generators intertwine,
`Q M = M Q'` on the rows of forests, where `M` is the restriction map: merging two roots that both
meet the range of `e` merges their traces, and the other merges do not change the restriction.
`Phylogenetics.Coalescent.Trace` has the same statement with the lineages kept in `L`.

* `restrictForest e F`: the restriction of a forest on `L` to the lineages `L'`.
* `restrictUnrooted e T`: the restriction of an unrooted tree (given by the sides of its splits)
  to the lineages `L'`.

## Main results

* `kingmanTransition_lump`, `kingmanAbsorption_lump`: lumpability of Kingman's coalescent.
* `image_map_restrictForest`: the link with `traceForest`.
* `unroot_restrictForest`: unrooting commutes with restricting (for any family of clusters).
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*} [Fintype L'] [DecidableEq L']

/-- The restriction of a forest on `L` to the lineages `L'`, along an embedding `e : L' ↪ L`: the
nonempty traces of its clusters. -/
def restrictForest (e : L' ↪ L) (F : Finset (Finset L)) : Finset (Finset L') :=
  (F.filter fun A => ∃ l, e l ∈ A).image fun A => univ.filter fun l => e l ∈ A

/-! ### Restricting forests -/

omit [Fintype L] in
theorem mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  unfold restrictForest
  simp only [mem_image, mem_filter, and_assoc]

omit [Fintype L] in
private theorem marg_tr_mem_restrictForest (e : L' ↪ L) {F : Finset (Finset L)} {A : Finset L}
    (hA : A ∈ F) (hmeet : ∃ l, e l ∈ A) :
    (univ.filter fun l => e l ∈ A) ∈ restrictForest e F :=
  (mem_restrictForest e).2 ⟨A, hA, hmeet, rfl⟩

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_mono (e : L' ↪ L) {A B : Finset L} (h : A ⊆ B) :
    (univ.filter fun l => e l ∈ A) ⊆ univ.filter fun l => e l ∈ B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_disjoint (e : L' ↪ L) {A B : Finset L} (h : Disjoint A B) :
    Disjoint (univ.filter fun l => e l ∈ A) (univ.filter fun l => e l ∈ B) :=
  disjoint_left.2 fun _ hlA hlB => disjoint_left.1 h (mem_filter.1 hlA).2 (mem_filter.1 hlB).2

omit [Fintype L] in
private theorem marg_tr_union (e : L' ↪ L) (A B : Finset L) :
    (univ.filter fun l => e l ∈ A ∪ B) =
      (univ.filter fun l => e l ∈ A) ∪ univ.filter fun l => e l ∈ B := by
  ext l
  simp

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_eq_empty (e : L' ↪ L) {A : Finset L} (h : ¬ ∃ l, e l ∈ A) :
    (univ.filter fun l => e l ∈ A) = ∅ := by
  ext l
  simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
  exact fun hl => h ⟨l, hl⟩

omit [Fintype L] in
theorem IsForest.restrictForest {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    IsForest (restrictForest e F) := by
  refine ⟨fun D hD => ?_, fun D hD D' hD' => ?_⟩
  · obtain ⟨A, -, ⟨l, hl⟩, rfl⟩ := (mem_restrictForest e).1 hD
    exact ⟨l, mem_filter.2 ⟨mem_univ l, hl⟩⟩
  · obtain ⟨A, hA, -, rfl⟩ := (mem_restrictForest e).1 hD
    obtain ⟨B, hB, -, rfl⟩ := (mem_restrictForest e).1 hD'
    rcases hF.2 A hA B hB with h | h | h
    · exact Or.inl (marg_tr_mono e h)
    · exact Or.inr (Or.inl (marg_tr_mono e h))
    · exact Or.inr (Or.inr (marg_tr_disjoint e h))

omit [Fintype L] in
private theorem marg_restrictForest_insert (e : L' ↪ L) (C : Finset L) (F : Finset (Finset L)) :
    restrictForest e (insert C F) =
      if ∃ l, e l ∈ C then insert (univ.filter fun l => e l ∈ C) (restrictForest e F)
      else restrictForest e F := by
  unfold restrictForest
  rw [filter_insert]
  split_ifs <;> simp [image_insert]

omit [Fintype L'] [DecidableEq L'] in
/-- Two roots of a forest whose traces share a lineage are equal. -/
private theorem marg_eq_of_tr {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) {l : L'} (hlA : e l ∈ A)
    (hlB : e l ∈ B) : A = B :=
  hF.eq_of_mem_roots_of_mem hA hB hlA hlB

omit [DecidableEq L'] in
/-- The trace is injective on the roots meeting the range of `e`. -/
private theorem marg_tr_inj {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hmeet : ∃ l, e l ∈ A)
    (h : (univ.filter fun l => e l ∈ A) = univ.filter fun l => e l ∈ B) : A = B := by
  obtain ⟨l, hl⟩ := hmeet
  have hlB : l ∈ univ.filter fun l => e l ∈ B := h ▸ mem_filter.2 ⟨mem_univ l, hl⟩
  exact marg_eq_of_tr hF e hA hB hl (mem_filter.1 hlB).2

/-- The roots of the restriction of a forest are the traces of its roots meeting the range. -/
private theorem marg_mem_roots_restrictForest {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {D : Finset L'} :
    D ∈ roots (restrictForest e F) ↔
      ∃ A ∈ roots F, (∃ l, e l ∈ A) ∧ (univ.filter fun l => e l ∈ A) = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, hmeet, rfl⟩ := (mem_restrictForest e).1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    obtain ⟨l, hl⟩ := hmeet
    have hRmeet : ∃ l, e l ∈ R := ⟨l, hAR hl⟩
    refine ⟨R, hR, hRmeet, ?_⟩
    exact hmax _ (marg_tr_mem_restrictForest e (roots_subset F hR) hRmeet) (marg_tr_mono e hAR)
  · rintro ⟨A, hA, hmeet, rfl⟩
    refine mem_roots.2 ⟨marg_tr_mem_restrictForest e (roots_subset F hA) hmeet, fun D hD hAD => ?_⟩
    obtain ⟨B, hB, hBmeet, rfl⟩ := (mem_restrictForest e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    obtain ⟨l, hl⟩ := hmeet
    have hlB : e l ∈ B := (mem_filter.1 (hAD (mem_filter.2 ⟨mem_univ l, hl⟩))).2
    have hAR : A = R := marg_eq_of_tr hF e hA hR hl (hBR hlB)
    subst hAR
    exact subset_antisymm (marg_tr_mono e hBR) hAD

/-- The restriction of a merge: merging two roots that both meet the range of `e` merges their
traces; otherwise the restriction does not change. -/
private theorem marg_restrictForest_merge {F : Finset (Finset L)} (e : L' ↪ L)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) :
    restrictForest e (insert (A ∪ B) F) =
      if (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) then
        insert ((univ.filter fun l => e l ∈ A) ∪ univ.filter fun l => e l ∈ B)
          (restrictForest e F)
      else restrictForest e F := by
  rw [marg_restrictForest_insert, marg_tr_union]
  by_cases hAm : ∃ l, e l ∈ A <;> by_cases hBm : ∃ l, e l ∈ B
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_left ⟨hAm, hBm⟩]
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hAm; ⟨l, mem_union_left _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hBm h.2), marg_tr_eq_empty e hBm, union_empty]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hA) hAm)
  · have hU : ∃ l, e l ∈ A ∪ B := let ⟨l, hl⟩ := hBm; ⟨l, mem_union_right _ hl⟩
    rw [ite_eq_left hU, ite_eq_right (fun h => hAm h.1), marg_tr_eq_empty e hAm, empty_union]
    exact insert_eq_of_mem (marg_tr_mem_restrictForest e (roots_subset F hB) hBm)
  · have hU : ¬ ∃ l, e l ∈ A ∪ B := by
      rintro ⟨l, hl⟩
      rcases mem_union.1 hl with h | h
      · exact hAm ⟨l, h⟩
      · exact hBm ⟨l, h⟩
    rw [ite_eq_right hU, ite_eq_right (fun h => hAm h.1)]


/-- The merges of `F` whose restriction differs from the restriction of `F`: the merges of two
roots that both meet the range of `e`. -/
private theorem marg_mem_merges_ne {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    {H : Finset (Finset L)} :
    (H ∈ merges F ∧ restrictForest e H ≠ restrictForest e F) ↔
      ∃ A ∈ roots F, ∃ B ∈ roots F, A ≠ B ∧ (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B) ∧
        H = insert (A ∪ B) F := by
  constructor
  · rintro ⟨hH, hne⟩
    obtain ⟨A, hA, B, hB, hAB, rfl⟩ := mem_merges.1 hH
    rw [marg_restrictForest_merge e hA hB] at hne
    by_cases h : (∃ l, e l ∈ A) ∧ (∃ l, e l ∈ B)
    · exact ⟨A, hA, B, hB, hAB, h.1, h.2, rfl⟩
    · rw [ite_eq_right h] at hne
      exact absurd rfl hne
  · rintro ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩
    refine ⟨mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩, ?_⟩
    rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
    intro h
    have hrA := (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    have hrB := (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩
    have hne : (univ.filter fun l => e l ∈ A) ≠ univ.filter fun l => e l ∈ B :=
      fun h' => hAB (marg_tr_inj hF e hA hB hAm h')
    exact union_not_mem_of_mem_roots hrA hrB hne (h ▸ mem_insert_self _ _)

/-- The key count behind lumpability: summing a function of the restriction over the merges of
`F` gives the sum over the merges of the restriction, plus the merges that do not change the
restriction. -/
private theorem marg_sum_merges {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (u : Finset (Finset L') → ℝ) :
    -((#(roots F)).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H ∈ merges F, u (restrictForest e H) =
      -((#(roots (restrictForest e F))).choose 2 : ℝ) * u (restrictForest e F) +
        ∑ H' ∈ merges (restrictForest e F), u H' := by
  set rF := restrictForest e F with hrF
  have hrFf : IsForest rF := hF.restrictForest e
  set M₂ := (merges F).filter fun H => restrictForest e H ≠ rF with hM₂
  -- the restriction maps `M₂` onto the merges of `rF`
  have himage : M₂.image (restrictForest e) = merges rF := by
    ext H'
    rw [mem_image]
    constructor
    · rintro ⟨H, hH, rfl⟩
      obtain ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩ :=
        (marg_mem_merges_ne hF e).1 (mem_filter.1 hH)
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
      exact mem_merges.2 ⟨_, (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩, _,
        (marg_mem_roots_restrictForest hF e).2 ⟨B, hB, hBm, rfl⟩,
        fun h' => hAB (marg_tr_inj hF e hA hB hAm h'), rfl⟩
    · intro hH'
      obtain ⟨A', hA', B', hB', hAB', rfl⟩ := mem_merges.1 hH'
      obtain ⟨A, hA, hAm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hA'
      obtain ⟨B, hB, hBm, rfl⟩ := (marg_mem_roots_restrictForest hF e).1 hB'
      have hAB : A ≠ B := by
        rintro rfl
        exact hAB' rfl
      refine ⟨insert (A ∪ B) F, mem_filter.2 ((marg_mem_merges_ne hF e).2
        ⟨A, hA, B, hB, hAB, hAm, hBm, rfl⟩), ?_⟩
      rw [marg_restrictForest_merge e hA hB, ite_eq_left ⟨hAm, hBm⟩]
  -- and is injective on `M₂`
  have hinj : Set.InjOn (restrictForest e) (M₂ : Set (Finset (Finset L))) := by
    intro H₁ hH₁ H₂ hH₂ h12
    obtain ⟨A₁, hA₁, B₁, hB₁, hAB₁, hA₁m, hB₁m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₁))
    obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂, hA₂m, hB₂m, rfl⟩ :=
      (marg_mem_merges_ne hF e).1 (mem_filter.1 (mem_coe.1 hH₂))
    rw [marg_restrictForest_merge e hA₁ hB₁, ite_eq_left ⟨hA₁m, hB₁m⟩,
      marg_restrictForest_merge e hA₂ hB₂, ite_eq_left ⟨hA₂m, hB₂m⟩] at h12
    have hr := fun {A} (hA : A ∈ roots F) (hAm : ∃ l, e l ∈ A) =>
      (marg_mem_roots_restrictForest hF e).2 ⟨A, hA, hAm, rfl⟩
    have hU : ((univ.filter fun l => e l ∈ A₁) ∪ univ.filter fun l => e l ∈ B₁) =
        (univ.filter fun l => e l ∈ A₂) ∪ univ.filter fun l => e l ∈ B₂ := by
      have hmem := h12 ▸ mem_insert_self ((univ.filter fun l => e l ∈ A₁) ∪
        univ.filter fun l => e l ∈ B₁) rF
      rcases mem_insert.1 hmem with h | h
      · exact h
      · exact absurd h (union_not_mem_of_mem_roots (hr hA₁ hA₁m) (hr hB₁ hB₁m)
          (fun h' => hAB₁ (marg_tr_inj hF e hA₁ hB₁ hA₁m h')))
    -- each of `A₁`, `B₁` is one of `A₂`, `B₂`
    have hin : ∀ {C}, C ∈ roots F → (∃ l, e l ∈ C) →
        (univ.filter fun l => e l ∈ C) ⊆
          ((univ.filter fun l => e l ∈ A₂) ∪ (univ.filter fun l => e l ∈ B₂)) →
        C = A₂ ∨ C = B₂ := by
      intro C hC hCm hsub
      obtain ⟨l, hl⟩ := hCm
      rcases mem_union.1 (hsub (mem_filter.2 ⟨mem_univ l, hl⟩)) with h | h
      · exact Or.inl (marg_eq_of_tr hF e hC hA₂ hl (mem_filter.1 h).2)
      · exact Or.inr (marg_eq_of_tr hF e hC hB₂ hl (mem_filter.1 h).2)
    have h1 := hin hA₁ hA₁m (hU ▸ subset_union_left)
    have h2 := hin hB₁ hB₁m (hU ▸ subset_union_right)
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hAB₁
    · rfl
    · rw [union_comm]
    · exact absurd rfl hAB₁
  have hcard₂ : #M₂ = (#(roots rF)).choose 2 := by
    rw [← card_image_of_injOn hinj, himage, hrFf.card_merges]
  have hcard : #((merges F).filter fun H => restrictForest e H = rF) + #M₂ =
      (#(roots F)).choose 2 := by
    rw [hM₂, card_filter_add_card_filter_not, hF.card_merges]
  have hsum : ∑ H ∈ merges F, u (restrictForest e H) =
      #((merges F).filter fun H => restrictForest e H = rF) * u rF + ∑ H' ∈ merges rF, u H' := by
    rw [← sum_filter_add_sum_filter_not (merges F) (fun H => restrictForest e H = rF)]
    congr 1
    · rw [sum_congr rfl fun H hH => by rw [(mem_filter.1 hH).2], sum_const, nsmul_eq_mul]
    · rw [← himage, sum_image hinj]
  rw [hsum]
  have hcard' : ((#((merges F).filter fun H => restrictForest e H = rF) : ℕ) : ℝ) =
      ((#(roots F)).choose 2 : ℝ) - ((#(roots rF)).choose 2 : ℝ) := by
    rw [← hcard, ← hcard₂]
    push_cast
    ring
  rw [hcard']
  ring

/-- Intertwining of the generators: `Q M = M Q'` on the rows of forests, tested against `w`. -/
private theorem marg_sum_kingmanGenerator {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanGenerator F G * w (restrictForest e G) =
      ∑ G', kingmanGenerator (restrictForest e F) G' * w G' := by
  rw [hF.sum_kingmanGenerator_mul (fun G => w (restrictForest e G)),
    (hF.restrictForest e).sum_kingmanGenerator_mul w]
  exact marg_sum_merges hF e w

/-- Lumpability of Kingman's coalescent, tested against a function `w` of the restriction. -/
theorem sum_kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanTransition t F G * w (restrictForest e G) =
      ∑ G', kingmanTransition t (restrictForest e F) G' * w G' :=
  sum_kingmanTransition_comp (fun _ hF' w => marg_sum_kingmanGenerator hF' e w) hF t w

/-- Consistency of Kingman's coalescent (lumpability). -/
theorem kingmanTransition_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) (t : ℝ)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanTransition t F G else 0) =
      kingmanTransition t (restrictForest e F) G' :=
  kingmanTransition_comp (fun _ hF' w => marg_sum_kingmanGenerator hF' e w) hF t G'

theorem kingmanAbsorption_lump {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then kingmanAbsorption F G else 0) =
      kingmanAbsorption (restrictForest e F) G' :=
  kingmanAbsorption_comp (fun _ hF' w => marg_sum_kingmanGenerator hF' e w) hF
    (hF.restrictForest e) G'

omit [Fintype L] in
theorem restrictForest_union (e : L' ↪ L) (F₁ F₂ : Finset (Finset L)) :
    restrictForest e (F₁ ∪ F₂) = restrictForest e F₁ ∪ restrictForest e F₂ := by
  unfold restrictForest
  rw [filter_union, image_union]

omit [Fintype L] in
/-- The two forms of restriction agree: the restriction along `e`, mapped back along `e`, is the trace
on the range of `e` (`Phylogenetics.Coalescent.Trace`). -/
theorem image_map_restrictForest (e : L' ↪ L) (F : Finset (Finset L)) :
    (restrictForest e F).image (fun A => A.map e) = traceForest (univ.map e) F := by
  ext D
  simp only [mem_image, mem_traceForest, mem_restrictForest]
  constructor
  · rintro ⟨_, ⟨A, hA, ⟨l, hl⟩, rfl⟩, rfl⟩
    refine ⟨A, hA, ⟨e l, by simp [hl]⟩, ?_⟩
    ext x
    simp only [mem_inter, mem_map, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨hx, l', rfl⟩
      exact ⟨l', hx, rfl⟩
    · rintro ⟨l', hl', rfl⟩
      exact ⟨hl', l', rfl⟩
  · rintro ⟨A, hA, ⟨x, hx⟩, rfl⟩
    obtain ⟨hxA, hxZ⟩ := mem_inter.1 hx
    obtain ⟨l, -, rfl⟩ := mem_map.1 hxZ
    refine ⟨_, ⟨A, hA, ⟨l, hxA⟩, rfl⟩, ?_⟩
    ext x
    simp only [mem_inter, mem_map, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨l', hl', rfl⟩
      exact ⟨hl', l', rfl⟩
    · rintro ⟨hx, l', rfl⟩
      exact ⟨l', hx, rfl⟩

/-! ### Unrooting -/

/-- The restriction of an unrooted tree (given by the sides of its splits, as in
`Phylogenetics.unroot`) to the lineages `L'`, along an embedding `e : L' ↪ L`: the splits whose two
sides both meet the range of `e`, restricted to `L'`. -/
def restrictUnrooted (e : L' ↪ L) (T : Finset (Finset L)) : Finset (Finset L') :=
  (T.filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image fun A => univ.filter fun l => e l ∈ A

private theorem marg_tr_compl (e : L' ↪ L) (A : Finset L) :
    (univ.filter fun l => e l ∈ A)ᶜ = univ.filter fun l => e l ∈ Aᶜ := by
  ext l
  simp

omit [Fintype L] [DecidableEq L'] in
private theorem marg_tr_ne_univ (e : L' ↪ L) {A : Finset L} :
    (univ.filter fun l => e l ∈ A) ≠ univ ↔ ∃ l, e l ∉ A := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (filter_true_of_mem fun l _ => h' l)
  · rintro ⟨l, hl⟩ h
    have hl' : l ∈ univ.filter fun l => e l ∈ A := by
      rw [h]
      exact mem_univ l
    exact hl (mem_filter.1 hl').2

/-- Unrooting commutes with restricting to a subset of the lineages, for any family of clusters. -/
theorem restrictForest_unroot_aux (e : L' ↪ L) (G : Finset (Finset L)) :
    unroot (restrictForest e G) = restrictUnrooted e (unroot G) := by
  ext D
  rw [mem_unroot]
  unfold restrictUnrooted
  rw [mem_image]
  simp only [mem_filter, mem_unroot]
  constructor
  · rintro (⟨hD, hDu⟩ | ⟨hD, hDu⟩)
    · obtain ⟨A, hA, hAm, rfl⟩ := (mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 hDu
      have hAu : A ≠ univ := by
        rintro rfl
        obtain ⟨l, hl⟩ := hout
        exact hl (mem_univ _)
      exact ⟨A, ⟨Or.inl ⟨hA, hAu⟩, hAm, hout⟩, rfl⟩
    · obtain ⟨A, hA, hAm, hAD⟩ := (mem_restrictForest e).1 hD
      have hout := (marg_tr_ne_univ e).1 (hAD ▸ hDu)
      have hAu : A ≠ univ := by
        rintro rfl
        obtain ⟨l, hl⟩ := hout
        exact hl (mem_univ _)
      refine ⟨Aᶜ, ⟨Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩, ?_, ?_⟩, ?_⟩
      · obtain ⟨l, hl⟩ := hout
        exact ⟨l, mem_compl.2 hl⟩
      · obtain ⟨l, hl⟩ := hAm
        exact ⟨l, fun h => mem_compl.1 h hl⟩
      · rw [← marg_tr_compl, hAD, compl_compl]
  · rintro ⟨A, ⟨hA, hAm, hout⟩, rfl⟩
    rcases hA with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact Or.inl ⟨marg_tr_mem_restrictForest e hA hAm, (marg_tr_ne_univ e).2 hout⟩
    · right
      rw [marg_tr_compl]
      have hAcm : ∃ l, e l ∈ Aᶜ := let ⟨l, hl⟩ := hout; ⟨l, mem_compl.2 hl⟩
      refine ⟨marg_tr_mem_restrictForest e hA hAcm, (marg_tr_ne_univ e).2 ?_⟩
      obtain ⟨l, hl⟩ := hAm
      exact ⟨l, fun h => mem_compl.1 h hl⟩

/-- Unrooting commutes with restricting a complete gene tree to a subset of the lineages. -/
theorem unroot_restrictForest {G : Finset (Finset L)}     (e : L' ↪ L) [Nonempty L'] :
    unroot (restrictForest e G) =
      ((unroot G).filter fun A => (∃ l, e l ∈ A) ∧ ∃ l, e l ∉ A).image
        fun A => univ.filter fun l => e l ∈ A :=
  restrictForest_unroot_aux e G

end Phylogenetics
