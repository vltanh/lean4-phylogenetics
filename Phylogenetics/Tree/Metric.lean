module

public import Phylogenetics.Tree.Splits

/-!
# Tree metrics through split families

The metric `treeMetric T w` of a split family `T` with positive weights `w`, through the four-point
expression `d(a,c) + d(b,e) - d(a,b) - d(c,e)`. This expression is twice the weight of the splits
`ab|ce` minus twice the weight of the splits `ac|be` (`TreeMetric.fourPoint_treeMetric`). Hence the
quartet trees displayed on `T`, and so `T` and `w`, can be read off from the metric (Buneman 1971).

## Main definitions and results

* `treeMetric`, `TreeBuilder`, `IsExactBuilder`.
* In the namespace `Phylogenetics.TreeMetric`: `card_four_of_ne`, `exists_eq_quartetTree`,
  `displays_quartetTree_iff`, `fourPoint_treeMetric`, `displays_iff_fourPoint`,
  `exists_pair_not_in_proper`, `eq_of_treeMetric_eq`.
* For the nodes on the path between two taxa: `blockOf`, `pathNodes`, `otherBlocks`, `JoinsAt`,
  `pathNodes_order`, `JoinsAt.unique`, `exists_joinsAt`, `sum_card_otherBlocks`, `nodeOfSide`,
  `nodeOfSide_compl_block`.

## References

* P. Buneman, *The recovery of trees from measures of dissimilarity*, in Mathematics in the Archaeological
  and Historical Sciences, Edinburgh University Press (1971) 387–395.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The tree metric of the tree with sides `T` and edge weights `w`: the total weight of the splits
separating two taxa. -/
def treeMetric (T : Finset (Finset X)) (w : Finset X → ℝ) (x y : X) : ℝ :=
  ∑ A ∈ T.filter (fun A => x ∈ A ∧ y ∉ A), w A

/-- A distance-based tree building method (NJ, FastME, …), returning sides of splits and
edge weights. -/
abbrev TreeBuilder (X : Type*) := (X → X → ℝ) → Finset (Finset X) × (Finset X → ℝ)

/-- The method recovers the tree from an exact tree metric, whose edge weights are positive and agree
on the two sides of an edge: it returns a tree resolving it with the same weights, and any further
edges have weight at most zero. Neighbor joining is of this kind: on the metric of a tree with a
polytomy it returns a binary tree with edges of length zero. -/
def IsExactBuilder (M : TreeBuilder X) : Prop :=
  ∀ (T : Finset (Finset X)) (w : Finset X → ℝ), IsUnrootedTree T →
    (∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) →
    IsUnrootedTree (M (treeMetric T w)).1 ∧ T ⊆ (M (treeMetric T w)).1 ∧
      (∀ A ∈ T, (M (treeMetric T w)).2 A = w A) ∧
      ∀ A ∈ (M (treeMetric T w)).1, A ∉ T → (M (treeMetric T w)).2 A ≤ 0

end Phylogenetics

namespace Phylogenetics.TreeMetric

variable {X : Type*} [DecidableEq X]

theorem card_four_of_ne {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset X).card = 4 := by
  rw [card_insert_of_notMem (by simp [*]), card_insert_of_notMem (by simp [*]), card_pair hcd]

section

variable [Fintype X]

omit [Fintype X] in
/-- Every quartet tree is `ab|cd` for four distinct taxa. -/
theorem exists_eq_quartetTree (s : QuartetTree X) :
    ∃ a b c d : X, ∃ h : ({a, b, c, d} : Finset X).card = 4, s = quartetTree a b c d h := by
  obtain ⟨s, h2, hc, hd⟩ := s
  obtain ⟨B, C, hBC, rfl⟩ := Finset.card_eq_two.mp h2
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hc B (by simp))
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp (hc C (by simp))
  have hdis := hd {a, b} (by simp) {c, d} (by simp) hBC
  have hdis' := Finset.disjoint_left.mp hdis
  have : ({a, b, c, d} : Finset X).card = 4 :=
    card_four_of_ne hab (fun h => hdis' (a := a) (by simp) (by simp [h]))
      (fun h => hdis' (a := a) (by simp) (by simp [h]))
      (fun h => hdis' (a := b) (by simp) (by simp [h]))
      (fun h => hdis' (a := b) (by simp) (by simp [h])) hcd
  exact ⟨a, b, c, d, this, rfl⟩

/-- A split family displays `ab|cd` exactly when one of its sides contains `a, b` and not `c, d`. -/
theorem displays_quartetTree_iff {T : Finset (Finset X)} (hT : IsSplitFamily T) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    Displays T (quartetTree a b c d h) ↔ ∃ A ∈ T, a ∈ A ∧ b ∈ A ∧ c ∉ A ∧ d ∉ A := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  constructor
  · rintro ⟨A, hA, hs⟩
    simp only [quartetTree_taxa, quartetTree_val, mem_insert, mem_singleton] at hs
    rcases hs with hs | hs
    · have hmem := fun z => Finset.ext_iff.mp hs z
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨A, hA, ((hmem a).mpr (Or.inl rfl)).1, ((hmem b).mpr (Or.inr rfl)).1, fun h' => ?_,
        fun h' => ?_⟩
      · rcases (hmem c).mp ⟨h', by simp⟩ with h'' | h''
        · exact hac h''.symm
        · exact hbc h''.symm
      · rcases (hmem d).mp ⟨h', by simp⟩ with h'' | h''
        · exact had h''.symm
        · exact hbd h''.symm
    · have hmem := fun z => Finset.ext_iff.mp hs z
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨Aᶜ, hT.compl_mem A hA, mem_compl.mpr fun h' => ?_, mem_compl.mpr fun h' => ?_,
        fun h' => mem_compl.mp h' ((hmem c).mpr (Or.inl rfl)).1,
        fun h' => mem_compl.mp h' ((hmem d).mpr (Or.inr rfl)).1⟩
      · rcases (hmem a).mp ⟨h', by simp⟩ with h'' | h''
        · exact hac h''
        · exact had h''
      · rcases (hmem b).mp ⟨h', by simp⟩ with h'' | h''
        · exact hbc h''
        · exact hbd h''
  · rintro ⟨A, hA, ha, hb, hc, hd⟩
    refine ⟨A, hA, ?_⟩
    simp only [quartetTree_taxa, quartetTree_val, mem_insert, mem_singleton]
    left
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hx hc
      · exact absurd hx hd
    · rintro (rfl | rfl)
      · exact ⟨ha, Or.inl rfl⟩
      · exact ⟨hb, Or.inr (Or.inl rfl)⟩

omit [Fintype X] in
/-- The quartet tree on a set of four taxa with a given cherry. -/
theorem exists_quartetTree_of_subset {q B : Finset X} (hq : q.card = 4) (hB : B ⊆ q)
    (hB2 : B.card = 2) : ∃ s : QuartetTree X, s.taxa = q ∧ s.val = {B, q \ B} := by
  have hc : (q \ B).card = 2 := by rw [Finset.card_sdiff_of_subset hB]; omega
  have hdis : Disjoint B (q \ B) := Finset.disjoint_sdiff
  have hne : B ≠ q \ B := by
    intro h
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    exact Finset.disjoint_left.mp hdis hx (h ▸ hx)
  have hs : IsQuartetTree ({B, q \ B} : Finset (Finset X)) := by
    refine ⟨Finset.card_pair hne, ?_, ?_⟩
    · intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl <;> assumption
    · intro C hC D hD hCD
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC hD
      rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
      · exact absurd rfl hCD
      · exact hdis
      · exact hdis.symm
      · exact absurd rfl hCD
  refine ⟨⟨_, hs⟩, ?_, rfl⟩
  simp only [QuartetTree.taxa, Finset.sup_insert, Finset.sup_singleton, id]
  exact Finset.union_sdiff_of_subset hB

omit [Fintype X] in
/-- A quartet tree is determined by its taxa and one cherry. -/
theorem val_eq_of_mem {s : QuartetTree X} {B : Finset X} (hB : B ∈ s.val) :
    s.val = {B, s.taxa \ B} := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_quartetTree s
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [quartetTree_taxa]
  simp only [quartetTree_val, mem_insert, mem_singleton] at hB ⊢
  rcases hB with rfl | rfl
  · have : ({a, b, c, d} : Finset X) \ {a, b} = {c, d} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [this]
  · have : ({a, b, c, d} : Finset X) \ {c, d} = {a, b} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton]
      grind
    rw [this, Finset.pair_comm]

omit [Fintype X] in
theorem eq_of_mem_of_taxa_eq {s s' : QuartetTree X} {B : Finset X} (hB : B ∈ s.val)
    (hB' : B ∈ s'.val) (h : s.taxa = s'.taxa) : s = s' :=
  Subtype.ext (by rw [val_eq_of_mem hB, val_eq_of_mem hB', h])

omit [Fintype X] in
/-- The count of a predicate on four distinct taxa. -/
theorem card_filter_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (P : X → Prop) :
    (({a, b, c, d} : Finset X).filter P).card =
      (if P a then 1 else 0) + (if P b then 1 else 0) + (if P c then 1 else 0) +
        (if P d then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [Finset.card_filter, Finset.sum_insert (by simp [*]), Finset.sum_insert (by simp [*]),
    Finset.sum_pair hcd]
  ring

omit [Fintype X] in
/-- The count of the four distinct taxa in a set. -/
theorem card_inter_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) (A : Finset X) :
    (A ∩ {a, b, c, d}).card =
      (if a ∈ A then 1 else 0) + (if b ∈ A then 1 else 0) + (if c ∈ A then 1 else 0) +
        (if d ∈ A then 1 else 0) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter,
    Finset.sum_insert (by simp [*]), Finset.sum_insert (by simp [*]), Finset.sum_pair hcd]
  ring

/-- A family of sides does not resolve the four taxa `q` exactly when none has two of them. -/
theorem forall_not_displays_iff {T : Finset (Finset X)} {q : Finset X} (hq : q.card = 4) :
    (∀ s ∈ treesOn q, ¬ Displays T s) ↔ ∀ A ∈ T, (A ∩ q).card ≠ 2 := by
  constructor
  · intro h A hA h2
    obtain ⟨s, hst, hsv⟩ := exists_quartetTree_of_subset hq Finset.inter_subset_right h2
    refine h s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst⟩) ⟨A, hA, ?_⟩
    rw [hst, hsv]
    simp
  · rintro h s hs ⟨A, hA, hmem⟩
    have hst : s.taxa = q := (Finset.mem_filter.mp hs).2
    rw [hst] at hmem
    exact h A hA (s.2.2.1 _ hmem)

/-- The four-point expression of a dissimilarity. -/
def fourPoint (δ : X → X → ℝ) (a b c e : X) : ℝ := δ a c + δ b e - δ a b - δ c e

/-- The total weight of the sides containing `a, b` and neither of `c, e`. -/
def sideWeight (T : Finset (Finset X)) (w : Finset X → ℝ) (a b c e : X) : ℝ :=
  ∑ C ∈ T.filter (fun C => a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C), w C

/-- The tree metric as a sum over the sides avoiding a chosen taxon, one for each split. -/
theorem treeMetric_eq_sum_avoiding {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hw : ∀ A ∈ T, w Aᶜ = w A) (u v r : X) :
    treeMetric T w u v = ∑ C ∈ T.filter (fun C => r ∉ C), if (u ∈ C ↔ v ∈ C) then 0 else w C := by
  have hsplit : ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∈ C then w C else 0) =
      ∑ C ∈ T, (if v ∈ C ∧ u ∉ C ∧ r ∉ C then w C else 0) := by
    refine Finset.sum_nbij' compl compl (fun C hC => hT.compl_mem C hC)
      (fun C hC => hT.compl_mem C hC) (by simp) (by simp) ?_
    intro C hC
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr, hw C hC]
  have h1 : treeMetric T w u v = ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∉ C then w C else 0) +
      ∑ C ∈ T, (if u ∈ C ∧ v ∉ C ∧ r ∈ C then w C else 0) := by
    rw [treeMetric, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr]
  rw [h1, hsplit, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases hu : u ∈ C <;> by_cases hv : v ∈ C <;> by_cases hr : r ∈ C <;> simp [hu, hv, hr]

/-- **The four-point formula.** -/
theorem fourPoint_treeMetric {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hw : ∀ A ∈ T, w Aᶜ = w A) (a b c e : X) :
    fourPoint (treeMetric T w) a b c e = 2 * sideWeight T w a b c e - 2 * sideWeight T w a c b e := by
  have hW : ∀ x y z : X, sideWeight T w x y z e =
      ∑ C ∈ T.filter (fun C => e ∉ C), if x ∈ C ∧ y ∈ C ∧ z ∉ C then w C else 0 := by
    intro x y z
    rw [sideWeight, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> by_cases hz : z ∈ C <;> by_cases he : e ∈ C <;>
      simp [hx, hy, hz, he]
  rw [fourPoint, treeMetric_eq_sum_avoiding hT hw a c e, treeMetric_eq_sum_avoiding hT hw b e e,
    treeMetric_eq_sum_avoiding hT hw a b e, treeMetric_eq_sum_avoiding hT hw c e e, hW, hW,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun C hC => ?_
  have he : e ∉ C := (Finset.mem_filter.mp hC).2
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> by_cases hc : c ∈ C <;> simp [ha, hb, hc, he] <;>
    ring

omit [Fintype X] in
theorem sideWeight_nonneg {T : Finset (Finset X)} {w : Finset X → ℝ} (hw : ∀ A ∈ T, 0 < w A)
    (a b c e : X) : 0 ≤ sideWeight T w a b c e :=
  Finset.sum_nonneg fun C hC => (hw C (Finset.mem_filter.mp hC).1).le

/-- The four-point characterization of the quartet trees displayed on a split family. -/
theorem displays_iff_fourPoint {T : Finset (Finset X)} (hT : IsSplitFamily T)
    {w : Finset X → ℝ} (hpos : ∀ A ∈ T, 0 < w A) (hw : ∀ A ∈ T, w Aᶜ = w A) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    Displays T (quartetTree a b c d h) ↔ 0 < fourPoint (treeMetric T w) a b c d := by
  rw [displays_quartetTree_iff hT, fourPoint_treeMetric hT hw]
  constructor
  · rintro ⟨A, hA, ha, hb, hc, hd⟩
    have h0 : sideWeight T w a c b d = 0 := by
      refine Finset.sum_eq_zero fun C hC => ?_
      obtain ⟨hCT, haC, hcC, hbC, hdC⟩ := Finset.mem_filter.mp hC
      exfalso
      rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
      · exact hbC (hsub hb)
      · exact hc (hsub hcC)
      · exact Finset.disjoint_left.mp hsub ha haC
      · have : d ∈ A ∪ C := hsub ▸ Finset.mem_univ d
        rcases Finset.mem_union.mp this with h' | h'
        · exact hd h'
        · exact hdC h'
    have hpos' : 0 < sideWeight T w a b c d :=
      lt_of_lt_of_le (hpos A hA) (Finset.single_le_sum (f := w)
        (fun C hC => (hpos C (Finset.mem_filter.mp hC).1).le)
        (Finset.mem_filter.mpr ⟨hA, ha, hb, hc, hd⟩))
    rw [h0]
    linarith
  · intro h'
    have h0 := sideWeight_nonneg hpos a c b d
    have h1 : 0 < sideWeight T w a b c d := by linarith
    obtain ⟨A, hA, -⟩ := Finset.exists_lt_of_sum_lt (s := T.filter
      (fun C => a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ d ∉ C)) (f := fun _ => (0 : ℝ)) (g := w)
      (by simpa [sideWeight] using h1)
    obtain ⟨hAT, hmem⟩ := Finset.mem_filter.mp hA
    exact ⟨A, hAT, hmem⟩

/-- Taxa on either side of a maximal side `C₀` properly inside the side `A` lie in no common side
properly inside `A`. -/
theorem not_mem_proper_of_maximal {T : Finset (Finset X)} (hT : IsSplitFamily T) {A C₀ : Finset X}
    (hA : A ∈ T) (hC₀ : C₀ ∈ T) (hlt : C₀ ⊂ A) (hmax : ∀ C ∈ T, C ⊂ A → C.card ≤ C₀.card) {u z : X}
    (hu : u ∈ C₀) (hzC : z ∉ C₀) : ∀ C ∈ T, C ⊂ A → ¬ (u ∈ C ∧ z ∈ C) := by
  rintro C hC hCA ⟨huC, hzC'⟩
  rcases hT.compatible C hC C₀ hC₀ with hsub | hsub | hsub | hsub
  · exact hzC (hsub hzC')
  · have : C₀ ⊂ C := ⟨hsub, fun h => hzC (h hzC')⟩
    exact absurd (Finset.card_lt_card this) (not_lt.mpr (hmax C hC hCA))
  · exact Finset.disjoint_left.mp hsub huC hu
  · obtain ⟨t, ht⟩ := hT.compl_nonempty A hA
    have ht' : t ∈ C ∪ C₀ := hsub ▸ Finset.mem_univ t
    have : t ∈ A := by
      rcases Finset.mem_union.mp ht' with h' | h'
      · exact hCA.1 h'
      · exact hlt.1 h'
    exact (Finset.mem_compl.mp ht) this

/-- A side `A` has two taxa, possibly equal, in no side properly inside `A`. -/
theorem exists_pair_not_in_proper {T : Finset (Finset X)} (hT : IsSplitFamily T) {A : Finset X}
    (hA : A ∈ T) : ∃ x ∈ A, ∃ x' ∈ A, ∀ C ∈ T, C ⊂ A → ¬ (x ∈ C ∧ x' ∈ C) := by
  by_cases hne : (T.filter fun C => C ⊂ A).Nonempty
  · obtain ⟨C₀, hC₀, hmax⟩ := Finset.exists_max_image _ Finset.card hne
    obtain ⟨hC₀T, hC₀A⟩ := Finset.mem_filter.mp hC₀
    obtain ⟨u, hu⟩ := hT.nonempty C₀ hC₀T
    obtain ⟨z, hz, hzC⟩ := Finset.exists_of_ssubset hC₀A
    exact ⟨u, hC₀A.1 hu, z, hz, not_mem_proper_of_maximal hT hA hC₀T hC₀A
      (fun C hC hCA => hmax C (Finset.mem_filter.mpr ⟨hC, hCA⟩)) hu hzC⟩
  · obtain ⟨x, hx⟩ := hT.nonempty A hA
    refine ⟨x, hx, x, hx, fun C hC hCA => ?_⟩
    exact absurd (Finset.mem_filter.mpr ⟨hC, hCA⟩) (fun h => hne ⟨C, h⟩)

/-- Weights can be read off from the metric. -/
theorem weight_eq_fourPoint {T : Finset (Finset X)} (hT : IsSplitFamily T) {A : Finset X}
    (hA : A ∈ T) : ∃ x x' y y' : X, ∀ {w : Finset X → ℝ}, (∀ A ∈ T, w Aᶜ = w A) →
      fourPoint (treeMetric T w) x x' y y' = 2 * w A := by
  obtain ⟨x, hx, x', hx', hxx⟩ := exists_pair_not_in_proper hT hA
  obtain ⟨y, hy, y', hy', hyy⟩ := exists_pair_not_in_proper hT (hT.compl_mem A hA)
  refine ⟨x, x', y, y', fun {w} hw => ?_⟩
  have hy₀ := Finset.mem_compl.mp hy
  have hy₀' := Finset.mem_compl.mp hy'
  have h0 : sideWeight T w x y x' y' = 0 := by
    refine Finset.sum_eq_zero fun C hC => ?_
    obtain ⟨hCT, hxC, hyC, hxC', hyC'⟩ := Finset.mem_filter.mp hC
    exfalso
    rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
    · exact hxC' (hsub hx')
    · exact hy₀ (hsub hyC)
    · exact Finset.disjoint_left.mp hsub hx hxC
    · have : y' ∈ A ∪ C := hsub ▸ Finset.mem_univ y'
      rcases Finset.mem_union.mp this with h' | h'
      · exact hy₀' h'
      · exact hyC' h'
  have h1 : sideWeight T w x x' y y' = w A := by
    have : T.filter (fun C => x ∈ C ∧ x' ∈ C ∧ y ∉ C ∧ y' ∉ C) = {A} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_filter.mpr ⟨hA, hx, hx', hy₀, hy₀'⟩, fun C hC => ?_⟩
      obtain ⟨hCT, hxC, hxC', hyC, hyC'⟩ := Finset.mem_filter.mp hC
      rcases hT.compatible A hA C hCT with hsub | hsub | hsub | hsub
      · by_contra hne
        have hlt : Cᶜ ⊂ Aᶜ := by
          refine ⟨Finset.compl_subset_compl.mpr hsub, fun h => hne ?_⟩
          exact Finset.Subset.antisymm (Finset.compl_subset_compl.mp h) hsub
        exact hyy Cᶜ (hT.compl_mem C hCT) hlt
          ⟨Finset.mem_compl.mpr hyC, Finset.mem_compl.mpr hyC'⟩
      · by_contra hne
        exact hxx C hCT ⟨hsub, fun h => hne (Finset.Subset.antisymm hsub h)⟩ ⟨hxC, hxC'⟩
      · exact absurd hxC (Finset.disjoint_left.mp hsub hx)
      · have : y ∈ A ∪ C := hsub ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp this with h' | h'
        · exact absurd h' hy₀
        · exact absurd h' hyC
    rw [sideWeight, this, Finset.sum_singleton]
  rw [fourPoint_treeMetric hT hw, h0, h1]
  ring

/-- **Buneman's theorem**: a tree metric with positive weights determines the tree and its weights. -/
theorem eq_of_treeMetric_eq (hX : 2 ≤ Fintype.card X) {T T' : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hT' : IsUnrootedTree T') {w w' : Finset X → ℝ}
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (hw' : ∀ A ∈ T', 0 < w' A ∧ w' Aᶜ = w' A)
    (h : treeMetric T w = treeMetric T' w') : T = T' ∧ ∀ A ∈ T, w A = w' A := by
  have hS := (isUnrootedTree_iff hX T).mp hT
  have hS' := (isUnrootedTree_iff hX T').mp hT'
  have hdisp : ∀ s : QuartetTree X, Displays T s ↔ Displays T' s := by
    intro s
    obtain ⟨a, b, c, d, hq, rfl⟩ := exists_eq_quartetTree s
    rw [displays_iff_fourPoint hS (fun A hA => (hw A hA).1) (fun A hA => (hw A hA).2),
      displays_iff_fourPoint hS' (fun A hA => (hw' A hA).1) (fun A hA => (hw' A hA).2), h]
  have hTT : T = T' := Finset.Subset.antisymm
    (subset_of_forall_displays hT' hT fun s hs => (hdisp s).mp hs)
    (subset_of_forall_displays hT hT' fun s hs => (hdisp s).mpr hs)
  refine ⟨hTT, fun A hA => ?_⟩
  subst hTT
  obtain ⟨x, x', y, y', hf⟩ := weight_eq_fourPoint hS hA
  have h1 := hf (w := w) fun A hA => (hw A hA).2
  have h2 := hf (w := w') fun A hA => (hw' A hA).2
  rw [h, h2] at h1
  linarith

/-- With fewer than two taxa, the only tree is empty. -/
theorem eq_empty_of_card_lt_two (hX : Fintype.card X < 2) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) : T = ∅ := by
  obtain ⟨H, ⟨-, -, hne, -⟩, rfl⟩ := hT
  have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have huniv : ∀ A ∈ H, A = univ := by
    intro A hA
    obtain ⟨x, hx⟩ := hne A hA
    ext y
    simpa [Subsingleton.elim y x] using hx
  have : H.erase univ = ∅ := by
    ext A
    simp only [mem_erase, notMem_empty, iff_false, not_and]
    exact fun h hA => h (huniv A hA)
  simp [unroot, this]

/-! ### The nodes on the path between two taxa

A vertex of a tree of degree at least three is a `IsVertexPartition`. The nodes other than `x, y` on the
path between the taxa `x` and `y` are the vertices with `x, y` in distinct blocks (`pathNodes`); at such
a node the other blocks hold the taxa whose paths to `x` or `y` join the path there (`JoinsAt`). -/

/-- The block of `P` containing the taxon `z`. -/
def blockOf (P : Finset (Finset X)) (z : X) : Finset X := (P.filter (z ∈ ·)).sup id

theorem eq_of_mem_block {T P : Finset (Finset X)} (hP : IsVertexPartition T P) {B C : Finset X}
    {z : X} (hB : B ∈ P) (hC : C ∈ P) (hzB : z ∈ B) (hzC : z ∈ C) : B = C := by
  by_contra hne
  exact Finset.disjoint_left.mp (hP.pairwiseDisjoint B hB C hC hne) hzB hzC

theorem blockOf_eq {T P : Finset (Finset X)} (hP : IsVertexPartition T P) {B : Finset X}
    {z : X} (hB : B ∈ P) (hz : z ∈ B) : blockOf P z = B := by
  have : P.filter (z ∈ ·) = {B} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hB, hz⟩, fun C hC => ?_⟩
    obtain ⟨hCP, hzC⟩ := Finset.mem_filter.mp hC
    exact eq_of_mem_block hP hCP hB hzC hz
  simp [blockOf, this]

theorem blockOf_mem {T P : Finset (Finset X)} (hP : IsVertexPartition T P) (z : X) :
    blockOf P z ∈ P := by
  obtain ⟨B, hB, hz⟩ := hP.exists_mem_block z
  rwa [blockOf_eq hP hB hz]

theorem mem_blockOf {T P : Finset (Finset X)} (hP : IsVertexPartition T P) (z : X) :
    z ∈ blockOf P z := by
  obtain ⟨B, hB, hz⟩ := hP.exists_mem_block z
  rwa [blockOf_eq hP hB hz]

/-- The nodes other than `x, y` on the path between `x` and `y`: the vertices of the tree whose
deletion separates `x` from `y`, each given by the partition of the taxa it determines. -/
def pathNodes (T : Finset (Finset X)) (x y : X) : Finset (Finset (Finset X)) :=
  univ.filter fun P => IsVertexPartition T P ∧ ∀ B ∈ P, x ∈ B → y ∉ B

theorem mem_pathNodes {T P : Finset (Finset X)} {x y : X} :
    P ∈ pathNodes T x y ↔ IsVertexPartition T P ∧ ∀ B ∈ P, x ∈ B → y ∉ B := by
  simp [pathNodes]

theorem pathNodes_comm (T : Finset (Finset X)) (x y : X) : pathNodes T y x = pathNodes T x y := by
  ext P
  simp only [mem_pathNodes]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => by tauto

/-- The blocks of `P` containing neither `x` nor `y`. -/
def otherBlocks (P : Finset (Finset X)) (x y : X) : Finset (Finset X) :=
  P.filter fun B => x ∉ B ∧ y ∉ B

omit [Fintype X] in
theorem otherBlocks_comm (P : Finset (Finset X)) (x y : X) :
    otherBlocks P y x = otherBlocks P x y := by
  simp only [otherBlocks, and_comm]

/-- The path from the taxon `z` to `x` or `y` joins the path between `x` and `y` at the node `P`:
`z` is in neither the block of `x` nor that of `y`. -/
def JoinsAt (P : Finset (Finset X)) (x y z : X) : Prop :=
  z ∉ blockOf P x ∧ z ∉ blockOf P y

theorem JoinsAt.not_mem {T P : Finset (Finset X)} {x y z : X} (hz : JoinsAt P x y z)
    (hP : IsVertexPartition T P) {B : Finset X} (hB : B ∈ P) (hzB : z ∈ B) : x ∉ B ∧ y ∉ B := by
  refine ⟨fun h => hz.1 ?_, fun h => hz.2 ?_⟩
  · rwa [blockOf_eq hP hB h]
  · rwa [blockOf_eq hP hB h]

theorem mem_sup_otherBlocks {T P : Finset (Finset X)} (hP : IsVertexPartition T P)
    {x y z : X} : z ∈ (otherBlocks P x y).sup id ↔ JoinsAt P x y z := by
  constructor
  · intro h
    obtain ⟨C, hC, hzC⟩ := Finset.mem_sup.mp h
    obtain ⟨hCP, hxC, hyC⟩ := Finset.mem_filter.mp hC
    refine ⟨fun hz => hxC ?_, fun hz => hyC ?_⟩
    · rw [eq_of_mem_block hP hCP (blockOf_mem hP x) hzC hz]
      exact mem_blockOf hP x
    · rw [eq_of_mem_block hP hCP (blockOf_mem hP y) hzC hz]
      exact mem_blockOf hP y
  · intro hz
    exact Finset.mem_sup.mpr ⟨blockOf P z, Finset.mem_filter.mpr ⟨blockOf_mem hP z,
      hz.not_mem hP (blockOf_mem hP z) (mem_blockOf hP z)⟩, mem_blockOf hP z⟩

/-- A taxon in the block of `y` at a node on the path is not in the block of `x`. -/
theorem not_mem_blockOf_of_mem {T P : Finset (Finset X)} {x y z : X}
    (hP : P ∈ pathNodes T x y) (hz : z ∈ blockOf P y) : z ∉ blockOf P x := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  intro hz'
  have e := eq_of_mem_block hV (blockOf_mem hV x) (blockOf_mem hV y) hz' hz
  exact hd _ (blockOf_mem hV x) (mem_blockOf hV x) (e ▸ mem_blockOf hV y)

/-- Two distinct nodes on the path are ordered: if `u` joins the path at `P` and `z` at `P'`, then
either `P` comes first from `x`, so that `z` lies beyond `P` towards `y` and `u` before `P'` towards
`x`, or `P'` does. -/
theorem pathNodes_order {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T) {x y u z : X}
    (hP : P ∈ pathNodes T x y) (hP' : P' ∈ pathNodes T x y) (hne : P ≠ P')
    (hu : JoinsAt P x y u) (hz : JoinsAt P' x y z) :
    (z ∈ blockOf P y ∧ u ∈ blockOf P' x) ∨ (z ∈ blockOf P x ∧ u ∈ blockOf P' y) := by
  obtain ⟨hV, hd⟩ := mem_pathNodes.1 hP
  obtain ⟨hV', hd'⟩ := mem_pathNodes.1 hP'
  obtain ⟨B, hB, B', hB', hun⟩ := hV.exists_union_eq_univ hT hV' hne
  have hm : ∀ t, t ∈ B ∨ t ∈ B' := fun t => Finset.mem_union.1 (hun ▸ Finset.mem_univ t)
  rcases hm x with hxB | hxB'
  · have hyB' : y ∈ B' := (hm y).resolve_left (hd B hB hxB)
    have e1 := blockOf_eq hV hB hxB
    have e2 := blockOf_eq hV' hB' hyB'
    have hu1 := hu.1
    have hz2 := hz.2
    rw [e1] at hu1
    rw [e2] at hz2
    right
    rw [e1, e2]
    exact ⟨(hm z).resolve_right hz2, (hm u).resolve_left hu1⟩
  · have hyB : y ∈ B := (hm y).resolve_right (hd' B' hB' hxB')
    have e1 := blockOf_eq hV hB hyB
    have e2 := blockOf_eq hV' hB' hxB'
    have hu2 := hu.2
    have hz1 := hz.1
    rw [e1] at hu2
    rw [e2] at hz1
    left
    rw [e1, e2]
    exact ⟨(hm z).resolve_right hz1, (hm u).resolve_left hu2⟩

/-- A taxon joins the path at one node only. -/
theorem JoinsAt.unique {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T) {x y u : X}
    (hP : P ∈ pathNodes T x y) (hP' : P' ∈ pathNodes T x y)
    (hu : JoinsAt P x y u) (hu' : JoinsAt P' x y u) : P = P' := by
  by_contra hne
  rcases pathNodes_order hT hP hP' hne hu hu' with h | h
  · exact hu.2 h.1
  · exact hu.1 h.1

/-- A vertex has a block other than two given sets. -/
theorem exists_block_ne {T P : Finset (Finset X)} (hP : IsVertexPartition T P)
    (B D : Finset X) : ∃ E ∈ P, E ≠ B ∧ E ≠ D := by
  have h0 : 0 < ((P.erase B).erase D).card := by
    have h1 := Finset.pred_card_le_card_erase (s := P) (a := B)
    have h2 := Finset.pred_card_le_card_erase (s := P.erase B) (a := D)
    have h3 := hP.three_le
    omega
  obtain ⟨E, hE⟩ := Finset.card_pos.mp h0
  obtain ⟨hED, hEB, hEP⟩ := by simpa only [Finset.mem_erase] using hE
  exact ⟨E, hEP, hEB, hED⟩

/-- A block is properly inside the complement of another. -/
theorem block_ssubset_compl {T P : Finset (Finset X)} (hS : IsSplitFamily T)
    (hP : IsVertexPartition T P) {B D : Finset X} (hB : B ∈ P) (hD : D ∈ P) (hne : D ≠ B) :
    D ⊂ Bᶜ := by
  have hdis := hP.pairwiseDisjoint D hD B hB hne
  refine ⟨fun t ht => Finset.mem_compl.mpr (Finset.disjoint_left.mp hdis ht), fun h => ?_⟩
  obtain ⟨E, hE, hEB, hED⟩ := exists_block_ne hP B D
  obtain ⟨t, ht⟩ := hS.nonempty E (hP.mem E hE)
  have htD : t ∈ D := h (Finset.mem_compl.mpr
    (Finset.disjoint_left.mp (hP.pairwiseDisjoint E hE B hB hEB) ht))
  exact Finset.disjoint_left.mp (hP.pairwiseDisjoint E hE D hD hED) ht htD

/-- The node at the end, on the side `A`, of the edge with side `A`, where `y ∉ A`: the blocks are
`Aᶜ` and the maximal sides properly inside `A`. -/
def nodeOfSide (T : Finset (Finset X)) (y : X) (A : Finset X) : Finset (Finset X) :=
  insert Aᶜ (childClusters (rootedAt T y) A)

theorem isVertexPartition_nodeOfSide {T : Finset (Finset X)} (hS : IsSplitFamily T)
    {y : X} {A : Finset X} (hA : A ∈ T) (hy : y ∉ A) (h2 : 2 ≤ A.card) :
    IsVertexPartition T (nodeOfSide T y A) := by
  have h := (rootedAt_isHierarchy hS y).isVertexPartition_insert_compl (K := A)
    (mem_rootedAt.2 (Or.inr (Or.inr ⟨hA, hy⟩))) (fun h => hy (h ▸ Finset.mem_univ y)) h2
  rwa [unroot_rootedAt hS y] at h

theorem nodeOfSide_mem_pathNodes {T : Finset (Finset X)} (hS : IsSplitFamily T)
    {x y : X} {A : Finset X} (hA : A ∈ T) (hxA : x ∈ A) (hyA : y ∉ A) (h2 : 2 ≤ A.card) :
    nodeOfSide T y A ∈ pathNodes T x y := by
  refine mem_pathNodes.2 ⟨isVertexPartition_nodeOfSide hS hA hyA h2, fun B hB hxB hyB => ?_⟩
  rcases Finset.mem_insert.1 hB with rfl | hB
  · exact Finset.mem_compl.mp hxB hxA
  · exact hyA ((mem_childClusters.1 hB).2.1.1 hyB)

/-- A cluster of the rooting at `y` that avoids `y` is a side of the tree. -/
theorem mem_of_mem_rootedAt {T : Finset (Finset X)} {y : X} {D : Finset X}
    (hD : D ∈ rootedAt T y) (hy : y ∉ D) : D ∈ T := by
  rcases mem_rootedAt.1 hD with rfl | rfl | ⟨h, -⟩
  · exact absurd (Finset.mem_univ y) hy
  · exact absurd (Finset.mem_singleton_self y) hy
  · exact h

/-- A node is recovered from its block containing `y`. -/
theorem nodeOfSide_compl_block {T P : Finset (Finset X)} (hS : IsSplitFamily T)
    (hP : IsVertexPartition T P) {y : X} {B : Finset X} (hB : B ∈ P) (hy : y ∈ B) :
    nodeOfSide T y Bᶜ = P := by
  have hnot : ∀ {D}, D ∈ P → D ≠ B → y ∉ D := fun hD hne hyD =>
    Finset.disjoint_left.mp (hP.pairwiseDisjoint _ hD B hB hne) hyD hy
  -- a set `E` properly inside `Bᶜ` does not have `Eᶜ` inside a block
  have hcompl : ∀ {E F}, E ⊂ Bᶜ → F ∈ P → Eᶜ ⊆ F → False := by
    intro E F hEB hF hsub
    have hBE : B ⊆ Eᶜ := fun t ht => Finset.mem_compl.mpr fun h =>
      Finset.mem_compl.mp (hEB.1 h) ht
    have hFB : F = B := eq_of_mem_block hP hF hB (hsub (hBE hy)) hy
    subst hFB
    exact not_subset_of_ssubset hEB (fun t ht => by
      by_contra hn
      exact Finset.mem_compl.mp ht (hsub (Finset.mem_compl.mpr hn)))
  ext D
  simp only [nodeOfSide, compl_compl, Finset.mem_insert, mem_childClusters]
  constructor
  · rintro (rfl | ⟨hDH, hDlt, hmax⟩)
    · exact hB
    · have hyD : y ∉ D := fun h => Finset.mem_compl.mp (hDlt.1 h) hy
      have hDT : D ∈ T := mem_of_mem_rootedAt hDH hyD
      rcases hP.edge_in_block D hDT with ⟨F, hF, hsub⟩ | ⟨F, hF, hsub⟩
      · have hne : F ≠ B := by
          rintro rfl
          obtain ⟨t, ht⟩ := hS.nonempty D hDT
          exact Finset.mem_compl.mp (hDlt.1 ht) (hsub ht)
        have hFlt := block_ssubset_compl hS hP hB hF hne
        have hFH : F ∈ rootedAt T y :=
          mem_rootedAt.2 (Or.inr (Or.inr ⟨hP.mem F hF, hnot hF hne⟩))
        by_cases hDF : D = F
        · exact hDF ▸ hF
        · exact absurd hFlt (hmax F hFH (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hDF⟩))
      · exact (hcompl hDlt hF hsub).elim
  · intro hD
    by_cases hDB : D = B
    · exact Or.inl hDB
    · refine Or.inr ⟨mem_rootedAt.2 (Or.inr (Or.inr ⟨hP.mem D hD, hnot hD hDB⟩)),
        block_ssubset_compl hS hP hB hD hDB, fun E hE hDE hEB => ?_⟩
      have hyE : y ∉ E := fun h => Finset.mem_compl.mp (hEB.1 h) hy
      rcases hP.edge_in_block E (mem_of_mem_rootedAt hE hyE) with ⟨F, hF, hsub⟩ | ⟨F, hF, hsub⟩
      · obtain ⟨t, ht⟩ := hS.nonempty D (hP.mem D hD)
        have hFD : F = D := eq_of_mem_block hP hF hD (hsub (hDE.1 ht)) ht
        subst hFD
        exact not_subset_of_ssubset hDE hsub
      · exact hcompl hEB hF hsub

/-- Every taxon `z` other than `x, y` joins the path at some node: root the tree at `y`, and take the
node at the least cluster containing `x, z`. -/
theorem exists_joinsAt {T : Finset (Finset X)} (hS : IsSplitFamily T) {x y z : X}
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) : ∃ P ∈ pathNodes T x y, JoinsAt P x y z := by
  obtain ⟨K, hK, hxzK, hleast⟩ := (rootedAt_isHierarchy hS y).exists_least (A := {x, z}) ⟨x, by simp⟩
  have hyc : ({y} : Finset X)ᶜ ∈ rootedAt T y :=
    mem_rootedAt.2 (Or.inr (Or.inr ⟨hS.compl_mem _ (hS.singleton_mem y), by simp⟩))
  have hKy : K ⊆ {y}ᶜ := hleast _ hyc (fun t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simpa)
  have hyK : y ∉ K := fun h => by simpa using hKy h
  have hxK : x ∈ K := hxzK (by simp)
  have hzK : z ∈ K := hxzK (by simp)
  have hKT : K ∈ T := mem_of_mem_rootedAt hK hyK
  have h2 : 2 ≤ K.card := Finset.one_lt_card.2 ⟨x, hxK, z, hzK, hzx.symm⟩
  have hP := nodeOfSide_mem_pathNodes hS hKT hxK hyK h2
  have hV := (mem_pathNodes.1 hP).1
  refine ⟨_, hP, fun hzA => ?_, fun hzB => ?_⟩
  · have hxA := mem_blockOf hV x
    rcases Finset.mem_insert.1 (blockOf_mem hV x) with hh | hh
    · rw [hh] at hxA
      exact Finset.mem_compl.1 hxA hxK
    · obtain ⟨hAH, hAlt, -⟩ := mem_childClusters.1 hh
      refine not_subset_of_ssubset hAlt (hleast _ hAH fun t ht => ?_)
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hxA
      · exact hzA
  · rw [blockOf_eq hV (Finset.mem_insert_self _ _) (Finset.mem_compl.2 hyK)] at hzB
    exact Finset.mem_compl.1 hzB hzK

omit [Fintype X] in
theorem card_sup_eq_sum {F : Finset (Finset X)}
    (hF : ∀ B ∈ F, ∀ C ∈ F, B ≠ C → Disjoint B C) : (F.sup id).card = ∑ C ∈ F, C.card := by
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion]
  · rfl
  · exact fun B hB C hC hBC => hF B hB C hC hBC

/-- Every taxon other than `x, y` lies in the other blocks of exactly one node on the path, so the
sizes of these blocks add up to `N - 2`. -/
theorem sum_card_otherBlocks {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hS : IsSplitFamily T) {x y : X} (hxy : x ≠ y) :
    ∑ P ∈ pathNodes T x y, ∑ C ∈ otherBlocks P x y, C.card + 2 = Fintype.card X := by
  have hdis : ∀ P ∈ pathNodes T x y, ∀ C ∈ otherBlocks P x y, ∀ D ∈ otherBlocks P x y, C ≠ D →
      Disjoint C D := fun P hP C hC D hD =>
    (mem_pathNodes.1 hP).1.pairwiseDisjoint C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1
  have hun : (pathNodes T x y).biUnion (fun P => (otherBlocks P x y).sup id) =
      (univ.erase x).erase y := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨P, hP, hz⟩
      obtain ⟨hV, -⟩ := mem_pathNodes.1 hP
      have hJ := (mem_sup_otherBlocks hV).1 hz
      exact ⟨fun e => hJ.2 (e ▸ mem_blockOf hV y), fun e => hJ.1 (e ▸ mem_blockOf hV x)⟩
    · rintro ⟨hzy, hzx⟩
      obtain ⟨P, hP, hJ⟩ := exists_joinsAt hS hxy hzx hzy
      exact ⟨P, hP, (mem_sup_otherBlocks (mem_pathNodes.1 hP).1).2 hJ⟩
  have hcard : ((pathNodes T x y).biUnion (fun P => (otherBlocks P x y).sup id)).card =
      ∑ P ∈ pathNodes T x y, ∑ C ∈ otherBlocks P x y, C.card := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun P hP => card_sup_eq_sum (hdis P hP)
    · intro P hP P' hP' hne
      refine Finset.disjoint_left.mpr fun z hz hz' => hne ?_
      exact JoinsAt.unique hT hP hP'
        ((mem_sup_otherBlocks (mem_pathNodes.1 hP).1).1 hz)
        ((mem_sup_otherBlocks (mem_pathNodes.1 hP').1).1 hz')
  rw [← hcard, hun, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩),
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have h1 : 2 ≤ Fintype.card X := by
    have := Finset.card_le_univ ({x, y} : Finset X)
    rwa [Finset.card_pair hxy] at this
  omega

end

end Phylogenetics.TreeMetric
