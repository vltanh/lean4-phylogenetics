module

public import Phylogenetics.Tree.NeighborJoining
public import Phylogenetics.Tree.Metric

/-!
# The four-point condition

Tree-like distances are characterized by the
4-point condition, on the three sums of pairs `SP_xy|zt = D(x,y) + D(z,t)`, with a trivial 4-blob (a star)
corresponding to equal sums, and a cut edge to `SP_ab|cd < SP_ac|bd = SP_ad|bc`.

* `sumOfPairs_of_displays`, `sumOfPairs_of_star`: the two shapes, on the metric of a tree.
* `isFourPoint_treeMetric`, `two_largest_treeMetric`: the two larger sums of pairs of a tree metric are equal.
* `exists_tree_of_isFourPoint`, `isFourPoint_iff`: **Buneman's four-point theorem** (P. Buneman, *The recovery of trees
  from measures of dissimilarity*, in Mathematics in the Archaeological and Historical Sciences, 1971, 387-395; *A note
  on the metric properties of trees*, J. Combin. Theory Ser. B 17 (1974), 48-50): a symmetric function vanishing on
  the diagonal with the four-point condition is the metric of a tree with nonnegative weights, positive on the
  internal edges.

The proof of Buneman's theorem here is not Buneman's: it is by induction on the number of nodes, joining neighbours as
in neighbor joining, on the clusters of `Phylogenetics.Tree.NeighborJoining`. The neighbours are a pair maximizing
the Gromov product with a fixed node (`exists_nbr_pair`), rather than a pair minimizing `Q`; the four-point condition
passes to the joined nodes (`IsClusterFP.join`), and a tree for these gives one for the nodes (`IsModel.of_join`).
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.FourPoint

open TreeMetric NJ

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The sum of pairs `SP_xy|zt = D(x,y) + D(z,t)`. -/
def sumOfPairs (δ : X → X → ℝ) (x y z t : X) : ℝ := δ x y + δ z t

/-- The four-point condition, for all taxa, not necessarily distinct: `D(a,b) + D(c,d)` is at most the larger of
the other two sums of pairs. -/
def IsFourPoint (δ : X → X → ℝ) : Prop :=
  ∀ a b c d, δ a b + δ c d ≤ max (δ a c + δ b d) (δ a d + δ b c)

/-- The two larger of the three sums of pairs are equal. -/
def TwoLargestEq (δ : X → X → ℝ) (a b c d : X) : Prop :=
  (sumOfPairs δ a b c d ≤ sumOfPairs δ a c b d ∧ sumOfPairs δ a c b d = sumOfPairs δ a d b c) ∨
    (sumOfPairs δ a c b d ≤ sumOfPairs δ a d b c ∧ sumOfPairs δ a d b c = sumOfPairs δ a b c d) ∨
    (sumOfPairs δ a d b c ≤ sumOfPairs δ a b c d ∧ sumOfPairs δ a b c d = sumOfPairs δ a c b d)

omit [Fintype X] [DecidableEq X] in
/-- For a symmetric function, the four-point condition says that the two larger sums of pairs are equal. -/
theorem isFourPoint_iff_twoLargestEq {δ : X → X → ℝ} (hs : ∀ x y, δ x y = δ y x) :
    IsFourPoint δ ↔ ∀ a b c d, TwoLargestEq δ a b c d := by
  constructor
  · intro h a b c d
    have h1 := le_max_iff.1 (h a b c d)
    have h2 := le_max_iff.1 (h a c b d)
    have h3 := le_max_iff.1 (h a d b c)
    rw [hs c b] at h2
    rw [hs d c, hs d b] at h3
    simp only [TwoLargestEq, sumOfPairs]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first
        | (left; constructor <;> linarith)
        | (right; left; constructor <;> linarith)
        | (right; right; constructor <;> linarith)
  · intro h a b c d
    rw [le_max_iff]
    rcases h a b c d with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inr h1.ge
    · exact Or.inl h1.le

/-! ### The metric of a tree -/

section Tree

variable {T : Finset (Finset X)} {w : Finset X → ℝ}

theorem treeMetric_comm (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A) (x y : X) :
    treeMetric T w x y = treeMetric T w y x := by
  rw [treeMetric_eq_clusterDist, treeMetric_eq_clusterDist, clusterDist_comm hT hw]

omit [Fintype X] in
theorem sideWeight_comm (T : Finset (Finset X)) (w : Finset X → ℝ) (a b c d : X) :
    sideWeight T w a b c d = sideWeight T w a b d c := by
  simp only [sideWeight, and_comm (a := c ∉ _)]

/-- A side with `a, b` in and `c, d` out leaves no weight on the splits `ac|bd`. -/
theorem sideWeight_eq_zero (hc : ∀ S ∈ T, ∀ S' ∈ T, Compat S S') {A : Finset X} (hA : A ∈ T)
    {a b c d : X} (ha : a ∈ A) (hb : b ∈ A) (hcA : c ∉ A) (hdA : d ∉ A) :
    sideWeight T w a c b d = 0 := by
  refine sum_eq_zero fun C hC => ?_
  obtain ⟨hCT, haC, hcC, hbC, hdC⟩ := mem_filter.1 hC
  exfalso
  rcases hc A hA C hCT with h | h | h | h
  · exact hbC (h hb)
  · exact hcA (h hcC)
  · exact disjoint_left.1 h ha haC
  · have : d ∈ A ∪ C := h ▸ mem_univ d
    rcases mem_union.1 this with h' | h'
    · exact hdA h'
    · exact hdC h'

/-- The sums of pairs of a tree metric, against the weights of the three shapes of split. -/
theorem sumOfPairs_sub (hS : IsSplitFamily T) (hw : ∀ A ∈ T, w Aᶜ = w A) (a b c d : X) :
    sumOfPairs (treeMetric T w) a c b d - sumOfPairs (treeMetric T w) a b c d =
        2 * sideWeight T w a b c d - 2 * sideWeight T w a c b d ∧
      sumOfPairs (treeMetric T w) a d b c - sumOfPairs (treeMetric T w) a b c d =
        2 * sideWeight T w a b c d - 2 * sideWeight T w a d b c := by
  have h1 := fourPoint_treeMetric hS hw a b c d
  have h2 := fourPoint_treeMetric hS hw a b d c
  rw [sideWeight_comm T w a b d c, fourPoint, treeMetric_comm hS.compl_mem hw d c] at h2
  rw [fourPoint] at h1
  simp only [sumOfPairs]
  constructor <;> linarith

/-- **A cut edge**: on a tree displaying `ab|cd`, `SP_ab|cd < SP_ac|bd = SP_ad|bc`. -/
theorem sumOfPairs_of_displays (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hd : Displays T (quartetTree a b c d h)) :
    sumOfPairs (treeMetric T w) a b c d < sumOfPairs (treeMetric T w) a c b d ∧
      sumOfPairs (treeMetric T w) a c b d = sumOfPairs (treeMetric T w) a d b c := by
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  obtain ⟨A, hA, ha, hb, hc, hd'⟩ := (displays_quartetTree_iff hS h).1 hd
  have hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S' := fun S hS' S' hS'' => hS.compatible S hS' S' hS''
  have h0 := sideWeight_eq_zero (w := w) hcT hA ha hb hc hd'
  have h0' := sideWeight_eq_zero (w := w) hcT hA ha hb hd' hc
  have hpos : 0 < sideWeight T w a b c d := by
    refine lt_of_lt_of_le (hw A hA).1 (single_le_sum (f := w)
      (fun C hC => (hw C (mem_filter.1 hC).1).1.le) (mem_filter.2 ⟨hA, ha, hb, hc, hd'⟩))
  obtain ⟨h1, h2⟩ := sumOfPairs_sub hS hw' a b c d
  rw [h0] at h1
  rw [h0'] at h2
  constructor <;> linarith

/-- **A star**: on a tree with no quartet tree displayed on `a, b, c, d`, the three sums of pairs are equal. -/
theorem sumOfPairs_of_star (hS : IsSplitFamily T) (hw : ∀ A ∈ T, w Aᶜ = w A) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) (hstar : ∀ s ∈ treesOn {a, b, c, d}, ¬ Displays T s) :
    sumOfPairs (treeMetric T w) a b c d = sumOfPairs (treeMetric T w) a c b d ∧
      sumOfPairs (treeMetric T w) a c b d = sumOfPairs (treeMetric T w) a d b c := by
  have hzero : ∀ {x y z t : X} (hq : ({x, y, z, t} : Finset X).card = 4),
      ({x, y, z, t} : Finset X) = {a, b, c, d} → sideWeight T w x y z t = 0 := by
    intro x y z t hq he
    refine sum_eq_zero fun C hC => ?_
    obtain ⟨hCT, h1, h2, h3, h4⟩ := mem_filter.1 hC
    exact absurd ((displays_quartetTree_iff hS hq).2 ⟨C, hCT, h1, h2, h3, h4⟩)
      (hstar _ (mem_treesOn.2 (by rw [quartetTree_taxa, he])))
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ne_of_card_four h
  have h1 := hzero h rfl
  have h2 := hzero (x := a) (y := c) (z := b) (t := d) (card_four_of_ne hac hab had hbc.symm hcd hbd)
    (by ext z; simp only [mem_insert, mem_singleton]; tauto)
  have h3 := hzero (x := a) (y := d) (z := b) (t := c) (card_four_of_ne had hab hac hbd.symm hcd.symm hbc)
    (by ext z; simp only [mem_insert, mem_singleton]; tauto)
  obtain ⟨e1, e2⟩ := sumOfPairs_sub hS hw a b c d
  rw [h1, h2] at e1
  rw [h1, h3] at e2
  constructor <;> linarith

/-- **The two larger sums of pairs of a tree metric are equal**, on any taxa. -/
theorem twoLargestEq_of_isSplitFamily (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 ≤ w A ∧ w Aᶜ = w A)
    (a b c d : X) : TwoLargestEq (treeMetric T w) a b c d := by
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  have hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S' := fun S hS' S' hS'' => hS.compatible S hS' S' hS''
  have hnn : ∀ x y z t : X, 0 ≤ sideWeight T w x y z t := fun x y z t =>
    sum_nonneg fun C hC => (hw C (mem_filter.1 hC).1).1
  -- a side realizing a shape, when its weight is nonzero
  have hex : ∀ x y z t : X, sideWeight T w x y z t = 0 ∨
      ∃ A ∈ T, x ∈ A ∧ y ∈ A ∧ z ∉ A ∧ t ∉ A := by
    intro x y z t
    by_cases hne : (T.filter fun C => x ∈ C ∧ y ∈ C ∧ z ∉ C ∧ t ∉ C).Nonempty
    · obtain ⟨A, hA⟩ := hne
      obtain ⟨hAT, h⟩ := mem_filter.1 hA
      exact Or.inr ⟨A, hAT, h⟩
    · left
      rw [sideWeight, not_nonempty_iff_eq_empty.1 hne, sum_empty]
  obtain ⟨e1, e2⟩ := sumOfPairs_sub hS hw' a b c d
  have h1 := hnn a b c d
  have h2 := hnn a c b d
  have h3 := hnn a d b c
  simp only [TwoLargestEq]
  rcases hex a b c d with z1 | ⟨A, hA, ha, hb, hc, hd⟩
  · rcases hex a c b d with z2 | ⟨A, hA, ha, hc, hb, hd⟩
    · rcases hex a d b c with z3 | ⟨A, hA, ha, hd, hb, hc⟩
      · left
        rw [z1, z2] at e1
        rw [z1, z3] at e2
        constructor <;> linarith
      · -- the shape `ad|bc`
        right; right
        rw [z1, z2] at e1
        rw [z1] at e2
        constructor <;> linarith
    · -- the shape `ac|bd`
      have z3 := sideWeight_eq_zero (w := w) hcT hA ha hc hd hb
      rw [← sideWeight_comm T w a d b c] at z3
      right; left
      rw [z1] at e1
      rw [z1, z3] at e2
      constructor <;> linarith
  · -- the shape `ab|cd`
    have z2 := sideWeight_eq_zero (w := w) hcT hA ha hb hc hd
    have z3 := sideWeight_eq_zero (w := w) hcT hA ha hb hd hc
    left
    rw [z2] at e1
    rw [z3] at e2
    constructor <;> linarith

/-- A tree metric on at most one taxon vanishes. -/
theorem treeMetric_of_card_lt_two (hX : ¬ 2 ≤ Fintype.card X) (hT : IsUnrootedTree T) (x y : X) :
    treeMetric T w x y = 0 := by
  have hT0 : T = ∅ := eq_empty_of_forall_notMem fun A hA => hX (hT.two_le_card_of_mem hA)
  simp [treeMetric, hT0]

/-- **The four-point condition for the metric of a tree** with nonnegative weights: the two larger sums of pairs
are equal, on any taxa. -/
theorem two_largest_treeMetric (hT : IsUnrootedTree T) (hw : ∀ A ∈ T, 0 ≤ w A ∧ w Aᶜ = w A) (a b c d : X) :
    TwoLargestEq (treeMetric T w) a b c d := by
  by_cases hX : 2 ≤ Fintype.card X
  · exact twoLargestEq_of_isSplitFamily (hT.isSplitFamily hX) hw a b c d
  · simp [TwoLargestEq, sumOfPairs, treeMetric_of_card_lt_two hX hT]

/-- **The four-point condition for the metric of a tree**. -/
theorem isFourPoint_treeMetric (hT : IsUnrootedTree T) (hw : ∀ A ∈ T, 0 ≤ w A ∧ w Aᶜ = w A) :
    IsFourPoint (treeMetric T w) :=
  (isFourPoint_iff_twoLargestEq (treeMetric_comm (fun _ h => hT.compl_mem h)
    fun A hA => (hw A hA).2)).2 (two_largest_treeMetric hT hw)

/-- The quartet tree `ab|cd` is displayed exactly when `SP_ab|cd` is the strictly smallest sum of pairs. -/
theorem displays_iff_sumOfPairs_lt (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) {a b c d : X}
    (h : ({a, b, c, d} : Finset X).card = 4) :
    Displays T (quartetTree a b c d h) ↔
      sumOfPairs (treeMetric T w) a b c d < sumOfPairs (treeMetric T w) a c b d := by
  rw [displays_iff_fourPoint hS (fun A hA => (hw A hA).1) (fun A hA => (hw A hA).2), fourPoint]
  simp only [sumOfPairs]
  constructor <;> intro h' <;> linarith

end Tree

/-! ### Buneman's four-point theorem -/

section Buneman

/-- The four-point condition on clusters. -/
structure IsClusterFP (P : Finset (Finset X)) (D : Finset X → Finset X → ℝ) : Prop where
  zero : ∀ E ∈ P, D E E = 0
  symm : ∀ E ∈ P, ∀ F ∈ P, D E F = D F E
  four : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P,
    D a b + D c d ≤ D a c + D b d ∨ D a b + D c d ≤ D a d + D b c

variable {P : Finset (Finset X)} {D : Finset X → Finset X → ℝ}

namespace IsClusterFP

omit [Fintype X] [DecidableEq X] in
/-- The triangle inequality, from the four-point condition with repeated nodes. -/
theorem triangle (h : IsClusterFP P D) {a b c : Finset X} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) :
    D a c ≤ D a b + D b c := by
  have h1 := h.four a ha c hc b hb b hb
  rw [h.zero b hb, h.symm c hc b hb] at h1
  rcases h1 with h1 | h1 <;> linarith

omit [Fintype X] [DecidableEq X] in
theorem nonneg (h : IsClusterFP P D) {a b : Finset X} (ha : a ∈ P) (hb : b ∈ P) : 0 ≤ D a b := by
  have h1 := h.four a ha a ha b hb b hb
  rw [h.zero a ha, h.zero b hb] at h1
  rcases h1 with h1 | h1 <;> linarith

end IsClusterFP

omit [Fintype X] in
/-- **A pair maximizing the Gromov product with a fixed node are neighbours**, in that the difference of their
distances to the other nodes is constant. -/
theorem exists_nbr_pair (hP : 3 ≤ P.card) (h : IsClusterFP P D) :
    ∃ A ∈ P, ∃ B ∈ P, A ≠ B ∧ ∃ r : ℝ, ∀ C ∈ (P.erase A).erase B, D A C - D B C = r := by
  obtain ⟨R, hR⟩ : P.Nonempty := card_pos.1 (by omega)
  have hne : (P.erase R).offDiag.Nonempty := by
    have h2 : 1 < (P.erase R).card := by
      rw [card_erase_of_mem hR]
      omega
    obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.1 h2
    exact ⟨(A, B), mem_offDiag.2 ⟨hA, hB, hAB⟩⟩
  obtain ⟨p, hp, hmax⟩ := exists_max_image (P.erase R).offDiag
    (fun p => D p.1 R + D p.2 R - D p.1 p.2) hne
  obtain ⟨hA, hB, hAB⟩ := mem_offDiag.1 hp
  obtain ⟨hAR, hAP⟩ := mem_erase.1 hA
  obtain ⟨hBR, hBP⟩ := mem_erase.1 hB
  refine ⟨p.1, hAP, p.2, hBP, hAB, D p.1 R - D p.2 R, fun C hC => ?_⟩
  obtain ⟨hCB, hCA, hCP⟩ : C ≠ p.2 ∧ C ≠ p.1 ∧ C ∈ P := by
    simpa only [mem_erase] using hC
  by_cases hCR : C = R
  · rw [hCR]
  have hC' : C ∈ P.erase R := mem_erase.2 ⟨hCR, hCP⟩
  have h1 := hmax (p.1, C) (mem_offDiag.2 ⟨hA, hC', hCA.symm⟩)
  have h2 := hmax (p.2, C) (mem_offDiag.2 ⟨hB, hC', hCB.symm⟩)
  simp only at h1 h2
  have h3 := h.four p.1 hAP C hCP p.2 hBP R hR
  have h4 := h.four p.1 hAP R hR p.2 hBP C hCP
  rw [h.symm C hCP p.2 hBP] at h3
  rw [h.symm R hR C hCP, h.symm R hR p.2 hBP] at h4
  rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> linarith

omit [Fintype X] in
/-- The four-point condition passes to the joined nodes. -/
theorem IsClusterFP.join (h : IsClusterFP P D) (hP : IsClusters P) {A B : Finset X} (hA : A ∈ P)
    {r : ℝ} (hB : B ∈ P) (hr : ∀ C ∈ (P.erase A).erase B, D A C - D B C = r) :
    IsClusterFP (insert (A ∪ B) ((P.erase A).erase B)) (State.joinedDist D A B) := by
  set a := (D A B + r) / 2 with ha_def
  have hrest : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → C ≠ B ∧ C ≠ A ∧ C ∈ P :=
    fun hC => by simpa only [mem_erase] using hC
  have hne : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → C ≠ A ∪ B := fun hC => hP.ne_union hA hC
  have fuu : State.joinedDist D A B (A ∪ B) (A ∪ B) = 0 := by simp [State.joinedDist]
  have fu : ∀ {C : Finset X}, C ∈ (P.erase A).erase B →
      State.joinedDist D A B (A ∪ B) C = D A C - a := by
    intro C hC
    have := hr C hC
    simp only [State.joinedDist, ite_true, hne hC, ite_false, ha_def]
    linarith
  have fu' : ∀ {C : Finset X}, C ∈ (P.erase A).erase B →
      State.joinedDist D A B C (A ∪ B) = D A C - a := by
    intro C hC
    have := hr C hC
    obtain ⟨-, -, hCP⟩ := hrest hC
    simp only [State.joinedDist, ite_true, hne hC, ite_false, ha_def]
    rw [h.symm C hCP A hA, h.symm C hCP B hB]
    linarith
  have fr : ∀ {E F : Finset X}, E ∈ (P.erase A).erase B → F ∈ (P.erase A).erase B →
      State.joinedDist D A B E F = D E F := by
    intro E F hE hF
    simp [State.joinedDist, hne hE, hne hF]
  have hbr : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → D B C = D A C - r := by
    intro C hC
    have := hr C hC
    linarith
  refine ⟨fun E hE => ?_, fun E hE F hF => ?_, fun p hp q hq u hu v hv => ?_⟩
  · rcases mem_insert.1 hE with rfl | hE
    · exact fuu
    · rw [fr hE hE]
      exact h.zero E (hrest hE).2.2
  · rcases mem_insert.1 hE with rfl | hE <;> rcases mem_insert.1 hF with rfl | hF
    · rfl
    · rw [fu hF, fu' hF]
    · rw [fu hE, fu' hE]
    · rw [fr hE hF, fr hF hE]
      exact h.symm E (hrest hE).2.2 F (hrest hF).2.2
  · have base := h.four
    rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq <;>
      rcases mem_insert.1 hu with rfl | hu <;> rcases mem_insert.1 hv with rfl | hv
    · exact Or.inl le_rfl
    · exact Or.inl le_rfl
    · rw [fuu, fu hu, fu' hu]
      exact Or.inl (by linarith)
    · have h1 := base A hA B hB u (hrest hu).2.2 v (hrest hv).2.2
      rw [hbr hv, hbr hu] at h1
      rw [fuu, fu hu, fu hv, fr hu hv, ha_def]
      refine Or.inl ?_
      rcases h1 with h1 | h1 <;> linarith
    · rw [fuu, fu hq, fu' hq]
      exact Or.inl (by linarith)
    · rw [fu hq, fu' hq]
      exact Or.inr (by linarith)
    · rw [fu hq, fu' hq, fu hu, fu' hu]
      exact Or.inl (by linarith)
    · have h1 := base A hA q (hrest hq).2.2 u (hrest hu).2.2 v (hrest hv).2.2
      rw [fu hq, fu hu, fu hv, fr hq hu, fr hq hv, fr hu hv]
      rcases h1 with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · exact Or.inl le_rfl
    · exact Or.inl le_rfl
    · rw [fu hu, fu' hu]
      exact Or.inr (by linarith)
    · have h1 := base p (hrest hp).2.2 A hA u (hrest hu).2.2 v (hrest hv).2.2
      rw [h.symm p (hrest hp).2.2 A hA] at h1
      rw [fu' hp, fu hu, fu hv, fr hp hu, fr hp hv, fr hu hv]
      rcases h1 with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have h1 := base A hA B hB p (hrest hp).2.2 q (hrest hq).2.2
      rw [hbr hq, hbr hp] at h1
      rw [fuu, fu' hp, fu' hq, fr hp hq, ha_def]
      refine Or.inl ?_
      rcases h1 with h1 | h1 <;> linarith
    · have h1 := base p (hrest hp).2.2 q (hrest hq).2.2 A hA v (hrest hv).2.2
      rw [h.symm p (hrest hp).2.2 A hA, h.symm q (hrest hq).2.2 A hA] at h1
      rw [fr hp hq, fu hv, fu' hp, fu' hq, fr hp hv, fr hq hv]
      rcases h1 with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have h1 := base p (hrest hp).2.2 q (hrest hq).2.2 u (hrest hu).2.2 A hA
      rw [h.symm p (hrest hp).2.2 A hA, h.symm q (hrest hq).2.2 A hA, h.symm u (hrest hu).2.2 A hA] at h1
      rw [fr hp hq, fu' hu, fu' hp, fu' hq, fr hp hu, fr hq hu]
      rcases h1 with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · have h1 := base p (hrest hp).2.2 q (hrest hq).2.2 u (hrest hu).2.2 v (hrest hv).2.2
      rw [fr hp hq, fr hu hv, fr hp hu, fr hq hv, fr hp hv, fr hq hu]
      exact h1

/-- A tree with its weights fitting the distances between clusters: its sides are unions of clusters, and each
cluster is a side, with its pendant edge. -/
structure IsModel (P : Finset (Finset X)) (D : Finset X → Finset X → ℝ) (T : Finset (Finset X))
    (w : Finset X → ℝ) : Prop where
  nonempty : ∀ S ∈ T, S.Nonempty
  compl_nonempty : ∀ S ∈ T, Sᶜ.Nonempty
  compl_mem : ∀ S ∈ T, Sᶜ ∈ T
  relevant : ∀ S ∈ T, Relevant P S
  compat : ∀ S ∈ T, ∀ S' ∈ T, Compat S S'
  blocks : ∀ C ∈ P, C ≠ univ → C ∈ T
  nonneg : ∀ S ∈ T, 0 ≤ w S
  weight_compl : ∀ S ∈ T, w Sᶜ = w S
  dist : ∀ E ∈ P, ∀ F ∈ P, D E F = clusterDist T w E F

omit [Fintype X] in
/-- Adding a side to the tree adds its weight to the distances it separates. -/
theorem clusterDist_insert {T : Finset (Finset X)} {S : Finset X} (w : Finset X → ℝ) (hS : S ∉ T)
    (E F : Finset X) :
    clusterDist (insert S T) w E F =
      (if E ⊆ S ∧ Disjoint F S then w S else 0) + clusterDist T w E F := by
  rw [clusterDist, clusterDist, sum_filter, sum_filter, sum_insert hS]

/-- **The induction step**: a model of the joined nodes gives a model of the nodes. -/
theorem IsModel.of_join (h : IsClusterFP P D) (hP : IsClusters P) (h3 : 3 ≤ P.card) {A B : Finset X}
    (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) {r : ℝ}
    (hr : ∀ C ∈ (P.erase A).erase B, D A C - D B C = r) {T' : Finset (Finset X)} {w' : Finset X → ℝ}
    (hm : IsModel (insert (A ∪ B) ((P.erase A).erase B)) (State.joinedDist D A B) T' w') :
    ∃ T w, IsModel P D T w := by
  have hrest : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → C ≠ B ∧ C ≠ A ∧ C ∈ P :=
    fun hC => by simpa only [mem_erase] using hC
  have hmemrest : ∀ {C : Finset X}, C ∈ P → C ≠ A → C ≠ B → C ∈ (P.erase A).erase B := fun hC h1 h2 =>
    mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, hC⟩⟩
  have hne : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → C ≠ A ∪ B := fun hC => hP.ne_union hA hC
  have hd := hP.disjoint A hA B hB hAB
  obtain ⟨x, hx⟩ := hP.nonempty A hA
  obtain ⟨y, hy⟩ := hP.nonempty B hB
  have hxy : x ∉ B := disjoint_left.1 hd hx
  have hyx : y ∉ A := disjoint_right.1 hd hy
  -- a third node
  obtain ⟨C₀, hC₀⟩ : ((P.erase A).erase B).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_erase.2 ⟨hAB.symm, hB⟩), card_erase_of_mem hA]
    omega
  obtain ⟨hC₀B, hC₀A, hC₀P⟩ := hrest hC₀
  obtain ⟨z, hz⟩ := hP.nonempty C₀ hC₀P
  have hzA : z ∉ A := disjoint_left.1 (hP.disjoint C₀ hC₀P A hA hC₀A) hz
  have hzB : z ∉ B := disjoint_left.1 (hP.disjoint C₀ hC₀P B hB hC₀B) hz
  -- the weights of the two pendant edges
  set a := (D A B + r) / 2 with ha_def
  set b := (D A B - r) / 2 with hb_def
  have hab : a + b = D A B := by
    rw [ha_def, hb_def]
    ring
  have hr0 := hr C₀ hC₀
  have ha0 : 0 ≤ a := by
    have t1 := h.triangle hB hA hC₀P
    have t2 := h.symm B hB A hA
    rw [ha_def]
    linarith
  have hb0 : 0 ≤ b := by
    have t1 := h.triangle hA hB hC₀P
    rw [hb_def]
    linarith
  -- the sides of the tree do not separate `A, B`
  have hrel : ∀ S ∈ T', A ∪ B ⊆ S ∨ Disjoint (A ∪ B) S := fun S hS =>
    hm.relevant S hS (A ∪ B) (mem_insert_self _ _)
  have hAin : ∀ S ∈ T', A ⊆ S → B ⊆ S := fun S hS hAS => by
    rcases hrel S hS with h1 | h1
    · exact subset_union_right.trans h1
    · exact absurd (hAS hx) (disjoint_left.1 h1 (mem_union_left _ hx))
  have hBin : ∀ S ∈ T', B ⊆ S → A ⊆ S := fun S hS hBS => by
    rcases hrel S hS with h1 | h1
    · exact subset_union_left.trans h1
    · exact absurd (hBS hy) (disjoint_left.1 h1 (mem_union_right _ hy))
  have hAnot : A ∉ T' := fun hS => hyx (hAin A hS (Subset.refl _) hy)
  have hBnot : B ∉ T' := fun hS => hxy (hBin B hS (Subset.refl _) hx)
  have hAcnot : Aᶜ ∉ T' := fun hS => by
    have := hBin Aᶜ hS (subset_compl_iff_disjoint_left.2 hd) hx
    exact mem_compl.1 this hx
  have hBcnot : Bᶜ ∉ T' := fun hS => by
    have := hAin Bᶜ hS (subset_compl_iff_disjoint_right.2 hd) hy
    exact mem_compl.1 this hy
  -- the four new sides are distinct
  have hAAc : A ≠ Aᶜ := fun e => hyx (e ▸ mem_compl.2 hyx)
  have hAB' : A ≠ Bᶜ := fun e => hzA (e ▸ mem_compl.2 hzB)
  have hAcB : Aᶜ ≠ B := fun e => hzB (e ▸ mem_compl.2 hzA)
  have hAcBc : Aᶜ ≠ Bᶜ := fun e => hxy (by
    have : x ∈ Aᶜᶜ := by simpa using hx
    rw [e, compl_compl] at this
    exact this)
  have hBBc : B ≠ Bᶜ := fun e => hxy (e ▸ mem_compl.2 hxy)
  -- the tree and its weights
  let w : Finset X → ℝ := fun S =>
    if S = A ∨ S = Aᶜ then a else if S = B ∨ S = Bᶜ then b else w' S
  have hwA : w A = a := by simp [w]
  have hwAc : w Aᶜ = a := by simp [w]
  have hwB : w B = b := by simp [w, hAB.symm, hAcB.symm]
  have hwBc : w Bᶜ = b := by simp [w, hAB'.symm, hAcBc.symm]
  have hwT : ∀ S ∈ T', w S = w' S := fun S hS => by
    have h1 : S ≠ A := fun e => hAnot (e ▸ hS)
    have h2 : S ≠ Aᶜ := fun e => hAcnot (e ▸ hS)
    have h3 : S ≠ B := fun e => hBnot (e ▸ hS)
    have h4 : S ≠ Bᶜ := fun e => hBcnot (e ▸ hS)
    simp [w, h1, h2, h3, h4]
  let T : Finset (Finset X) := insert A (insert Aᶜ (insert B (insert Bᶜ T')))
  have hmemT : ∀ {S : Finset X}, S ∈ T ↔ (S = A ∨ S = Aᶜ) ∨ (S = B ∨ S = Bᶜ) ∨ S ∈ T' := by
    intro S
    simp only [T, mem_insert]
    tauto
  have h2n : B ∉ insert Bᶜ T' := by
    rw [mem_insert]
    exact not_or.2 ⟨hBBc, hBnot⟩
  have h3n : Aᶜ ∉ insert B (insert Bᶜ T') := by
    simp only [mem_insert, not_or]
    exact ⟨hAcB, hAcBc, hAcnot⟩
  have h4n : A ∉ insert Aᶜ (insert B (insert Bᶜ T')) := by
    simp only [mem_insert, not_or]
    exact ⟨hAAc, hAB, hAB', hAnot⟩
  have hT'eq : ∀ E F : Finset X, clusterDist T' w E F = clusterDist T' w' E F := fun E F =>
    sum_congr rfl fun S hS => hwT S (mem_filter.1 hS).1
  -- the distances in the new tree
  have hdist : ∀ E F : Finset X, clusterDist T w E F =
      (if E ⊆ A ∧ Disjoint F A then a else 0) + ((if E ⊆ Aᶜ ∧ Disjoint F Aᶜ then a else 0) +
        ((if E ⊆ B ∧ Disjoint F B then b else 0) + ((if E ⊆ Bᶜ ∧ Disjoint F Bᶜ then b else 0) +
          clusterDist T' w' E F))) := by
    intro E F
    simp only [T]
    rw [clusterDist_insert w h4n, clusterDist_insert w h3n, clusterDist_insert w h2n,
      clusterDist_insert w hBcnot, hwA, hwAc, hwB, hwBc, hT'eq]
  have hrelP : ∀ S ∈ T', Relevant P S := by
    intro S hS C hC
    by_cases hCA : C = A
    · subst hCA
      rcases hrel S hS with h1 | h1
      · exact Or.inl (subset_union_left.trans h1)
      · exact Or.inr (h1.mono_left subset_union_left)
    · by_cases hCB : C = B
      · subst hCB
        rcases hrel S hS with h1 | h1
        · exact Or.inl (subset_union_right.trans h1)
        · exact Or.inr (h1.mono_left subset_union_right)
      · exact hm.relevant S hS C (mem_insert_of_mem (hmemrest hC hCA hCB))
  have hrelA : ∀ {E : Finset X}, E ∈ P → Relevant P E := by
    intro E hE C hC
    by_cases hCE : C = E
    · exact Or.inl (hCE ▸ Subset.refl _)
    · exact Or.inr (hP.disjoint C hC E hE hCE)
  -- comparing sides
  have hAc : ∀ S ∈ T', Compat A S := fun S hS => by
    rcases hrelP S hS A hA with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  have hBc : ∀ S ∈ T', Compat B S := fun S hS => by
    rcases hrelP S hS B hB with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
  have hAAcomp : Compat A A := Or.inl (Subset.refl _)
  have hBBcomp : Compat B B := Or.inl (Subset.refl _)
  have hABcomp : Compat A B := Or.inr (Or.inr (Or.inl hd))
  have hcmpl : ∀ {U₀ U V : Finset X}, (U = U₀ ∨ U = U₀ᶜ) → Compat U₀ V → Compat U V := by
    rintro U₀ U V (rfl | rfl) h'
    · exact h'
    · exact h'.compl_left
  have hcmpr : ∀ {V₀ U V : Finset X}, (V = V₀ ∨ V = V₀ᶜ) → Compat U V₀ → Compat U V := by
    rintro V₀ U V (rfl | rfl) h'
    · exact h'
    · exact h'.compl_right
  -- the value of a side and its complement
  have hTcompl : ∀ S ∈ T, Sᶜ ∈ T := by
    intro S hS'
    rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · exact hmemT.2 (Or.inl (Or.inr rfl))
    · exact hmemT.2 (Or.inl (Or.inl (compl_compl _)))
    · exact hmemT.2 (Or.inr (Or.inl (Or.inr rfl)))
    · exact hmemT.2 (Or.inr (Or.inl (Or.inl (compl_compl _))))
    · exact hmemT.2 (Or.inr (Or.inr (hm.compl_mem S hS')))
  have hwcompl : ∀ S ∈ T, w Sᶜ = w S := by
    intro S hS'
    rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · rw [hwA, hwAc]
    · rw [compl_compl, hwA, hwAc]
    · rw [hwB, hwBc]
    · rw [compl_compl, hwB, hwBc]
    · rw [hwT S hS', hwT _ (hm.compl_mem S hS'), hm.weight_compl S hS']
  -- facts on subsets of clusters
  have hnot : ∀ {E C : Finset X}, E ∈ P → C ∈ P → E ≠ C → ¬ E ⊆ C := fun hE hC hne' hs =>
    hne' (hP.eq_of_subset hE hC hs)
  have hndc : ∀ {E C : Finset X}, E ∈ P → C ∈ P → E ≠ C → ¬ Disjoint E Cᶜ := fun hE hC hne' hs =>
    hnot hE hC hne' (disjoint_compl_right_iff.1 hs)
  have hnself : ∀ {E : Finset X}, E ∈ P → ¬ E ⊆ Eᶜ := fun hE hs => by
    obtain ⟨e, he⟩ := hP.nonempty _ hE
    exact mem_compl.1 (hs he) he
  have hsubc : ∀ {E C : Finset X}, E ∈ P → C ∈ P → E ≠ C → E ⊆ Cᶜ := fun hE hC hne' =>
    subset_compl_iff_disjoint_right.2 (hP.disjoint _ hE _ hC hne')
  have hdisj : ∀ {E C : Finset X}, E ∈ P → C ∈ P → E ≠ C → Disjoint E C := fun hE hC hne' =>
    hP.disjoint _ hE _ hC hne'
  -- the distance from the new node
  have hD' : ∀ {F : Finset X}, F ∈ (P.erase A).erase B →
      clusterDist T' w' (A ∪ B) F = (D A F + D B F - D A B) / 2 := by
    intro F hF
    rw [← hm.dist (A ∪ B) (mem_insert_self _ _) F (mem_insert_of_mem hF)]
    simp [State.joinedDist, hne hF]
  have hcdA : ∀ F : Finset X, clusterDist T' w' A F = clusterDist T' w' (A ∪ B) F := by
    intro F
    refine sum_congr (filter_congr fun S hS => ?_) fun _ _ => rfl
    refine and_congr_left fun _ => ⟨fun hs => union_subset hs (hAin S hS hs), subset_union_left.trans⟩
  have hcdB : ∀ F : Finset X, clusterDist T' w' B F = clusterDist T' w' (A ∪ B) F := by
    intro F
    refine sum_congr (filter_congr fun S hS => ?_) fun _ _ => rfl
    refine and_congr_left fun _ => ⟨fun hs => union_subset (hBin S hS hs) hs, subset_union_right.trans⟩
  have hdAF : ∀ {F : Finset X}, F ∈ (P.erase A).erase B → D A F = clusterDist T w A F := by
    intro F hF
    obtain ⟨hFB, hFA, hFP⟩ := hrest hF
    have hrF := hr F hF
    rw [hdist, ite_eq_left ⟨Subset.refl _, hdisj hFP hA hFA⟩, ite_eq_right fun h' => hnself hA h'.1,
      ite_eq_right fun h' => hnot hA hB hAB h'.1, ite_eq_right fun h' => hndc hFP hB hFB h'.2,
      hcdA, hD' hF, ha_def]
    linarith
  have hdBF : ∀ {F : Finset X}, F ∈ (P.erase A).erase B → D B F = clusterDist T w B F := by
    intro F hF
    obtain ⟨hFB, hFA, hFP⟩ := hrest hF
    have hrF := hr F hF
    rw [hdist, ite_eq_right fun h' => hnot hB hA hAB.symm h'.1, ite_eq_right fun h' => hndc hFP hA hFA h'.2,
      ite_eq_left ⟨Subset.refl _, hdisj hFP hB hFB⟩, ite_eq_right fun h' => hnself hB h'.1,
      hcdB, hD' hF, hb_def]
    linarith
  have hdAB : D A B = clusterDist T w A B := by
    have h0 : clusterDist T' w' A B = 0 := by
      refine sum_eq_zero fun S hS => ?_
      obtain ⟨hS', h1, h2⟩ := mem_filter.1 hS
      exact absurd (hAin S hS' h1 hy) (disjoint_left.1 h2 hy)
    rw [hdist, ite_eq_left ⟨Subset.refl _, hd.symm⟩, ite_eq_right fun h' => hnself hA h'.1,
      ite_eq_right fun h' => hnot hA hB hAB h'.1,
      ite_eq_left ⟨hsubc hA hB hAB, disjoint_left.2 fun t ht ht' => mem_compl.1 ht' ht⟩, h0, add_zero,
      zero_add, zero_add, hab]
  have hdEF : ∀ {E F : Finset X}, E ∈ (P.erase A).erase B → F ∈ (P.erase A).erase B →
      D E F = clusterDist T w E F := by
    intro E F hE hF
    obtain ⟨hEB, hEA, hEP⟩ := hrest hE
    obtain ⟨hFB, hFA, hFP⟩ := hrest hF
    rw [hdist, ite_eq_right fun h' => hnot hEP hA hEA h'.1, ite_eq_right fun h' => hndc hFP hA hFA h'.2,
      ite_eq_right fun h' => hnot hEP hB hEB h'.1, ite_eq_right fun h' => hndc hFP hB hFB h'.2,
      zero_add, zero_add, zero_add, zero_add,
      ← hm.dist E (mem_insert_of_mem hE) F (mem_insert_of_mem hF)]
    simp [State.joinedDist, hne hE, hne hF]
  refine ⟨T, w, fun S hS' => ?_, fun S hS' => ?_, hTcompl, fun S hS' => ?_, fun S hS' S' hS'' => ?_,
    fun C hC hCu => ?_, fun S hS' => ?_, hwcompl, fun E hE F hF => ?_⟩
  · rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · exact ⟨x, hx⟩
    · exact ⟨y, mem_compl.2 hyx⟩
    · exact ⟨y, hy⟩
    · exact ⟨x, mem_compl.2 hxy⟩
    · exact hm.nonempty S hS'
  · rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · exact ⟨y, mem_compl.2 hyx⟩
    · exact ⟨x, by simpa using hx⟩
    · exact ⟨x, mem_compl.2 hxy⟩
    · exact ⟨y, by simpa using hy⟩
    · exact hm.compl_nonempty S hS'
  · rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · exact hrelA hA
    · exact (hrelA hA).compl
    · exact hrelA hB
    · exact (hrelA hB).compl
    · exact hrelP S hS'
  · rcases hmemT.1 hS' with hS' | hS' | hS' <;> rcases hmemT.1 hS'' with hS'' | hS'' | hS''
    · exact hcmpl hS' (hcmpr hS'' hAAcomp)
    · exact hcmpl hS' (hcmpr hS'' hABcomp)
    · exact hcmpl hS' (hAc S' hS'')
    · exact hcmpl hS' (hcmpr hS'' hABcomp.symm)
    · exact hcmpl hS' (hcmpr hS'' hBBcomp)
    · exact hcmpl hS' (hBc S' hS'')
    · exact (hcmpl hS'' (hAc S hS')).symm
    · exact (hcmpl hS'' (hBc S hS')).symm
    · exact hm.compat S hS' S' hS''
  · by_cases hCA : C = A
    · exact hmemT.2 (Or.inl (Or.inl hCA))
    · by_cases hCB : C = B
      · exact hmemT.2 (Or.inr (Or.inl (Or.inl hCB)))
      · exact hmemT.2 (Or.inr (Or.inr (hm.blocks C (mem_insert_of_mem (hmemrest hC hCA hCB)) hCu)))
  · rcases hmemT.1 hS' with (rfl | rfl) | (rfl | rfl) | hS'
    · rwa [hwA]
    · rwa [hwAc]
    · rwa [hwB]
    · rwa [hwBc]
    · rw [hwT S hS']
      exact hm.nonneg S hS'
  · have hcomm : ∀ U V : Finset X, clusterDist T w U V = clusterDist T w V U :=
      fun U V => clusterDist_comm hTcompl hwcompl U V
    by_cases hEF : E = F
    · subst hEF
      rw [h.zero E hE, clusterDist_self (hP.nonempty E hE)]
    by_cases hEA : E = A
    · subst hEA
      by_cases hFB : F = B
      · rw [hFB]
        exact hdAB
      · exact hdAF (hmemrest hF (Ne.symm hEF) hFB)
    by_cases hEB : E = B
    · subst hEB
      by_cases hFA : F = A
      · rw [hFA, h.symm E hE A hA, hcomm]
        exact hdAB
      · exact hdBF (hmemrest hF hFA (Ne.symm hEF))
    have hE' := hmemrest hE hEA hEB
    by_cases hFA : F = A
    · rw [hFA, h.symm E hE A hA, hcomm]
      exact hdAF hE'
    by_cases hFB : F = B
    · rw [hFB, h.symm E hE B hB, hcomm]
      exact hdBF hE'
    exact hdEF hE' (hmemrest hF hFA hFB)

/-- At most two nodes: the last edge. -/
theorem IsModel.of_card_le_two (h : IsClusterFP P D) (hP : IsClusters P) (h2 : P.card ≤ 2) :
    ∃ T w, IsModel P D T w := by
  by_cases h1 : P.card ≤ 1
  · refine ⟨∅, fun _ => 0, ⟨by simp, by simp, by simp, by simp, by simp, fun C hC hCu => ?_, by simp, by simp,
      fun E hE F hF => ?_⟩⟩
    · refine absurd (eq_univ_iff_forall.2 fun x => ?_) hCu
      obtain ⟨C', hC', hx⟩ := hP.cover x
      rw [card_le_one.1 h1 C hC C' hC']
      exact hx
    · rw [card_le_one.1 h1 E hE F hF, h.zero F hF]
      simp [clusterDist]
  · obtain ⟨E, F, hEF, hact⟩ := card_eq_two.1 (by omega : P.card = 2)
    have hE : E ∈ P := by simp [hact]
    have hF : F ∈ P := by simp [hact]
    have hd := hP.disjoint E hE F hF hEF
    obtain ⟨e, he⟩ := hP.nonempty E hE
    obtain ⟨f, hf⟩ := hP.nonempty F hF
    have hcE : Eᶜ = F := by
      refine Subset.antisymm (fun x hx => ?_) (subset_compl_iff_disjoint_left.2 hd)
      obtain ⟨C, hC, hxC⟩ := hP.cover x
      rw [hact, mem_insert, mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact absurd hxC (mem_compl.1 hx)
      · exact hxC
    have hcF : Fᶜ = E := by rw [← hcE, compl_compl]
    have hmemT : ∀ {S : Finset X}, S ∈ ({E, F} : Finset (Finset X)) ↔ S = E ∨ S = F := by
      intro S
      rw [mem_insert, mem_singleton]
    have hrelA : ∀ {U : Finset X}, U ∈ P → Relevant P U := by
      intro U hU C hC
      by_cases hCU : C = U
      · exact Or.inl (hCU ▸ Subset.refl _)
      · exact Or.inr (hP.disjoint C hC U hU hCU)
    have hEF' : Compat E F := Or.inr (Or.inr (Or.inl hd))
    have hval : clusterDist {E, F} (fun _ => D E F) E F = D E F := by
      rw [clusterDist, sum_filter, sum_pair hEF, ite_eq_left ⟨Subset.refl _, hd.symm⟩,
        ite_eq_right fun h' => disjoint_left.1 hd he (h'.1 he), add_zero]
    have hval' : clusterDist {E, F} (fun _ => D E F) F E = D E F := by
      rw [clusterDist, sum_filter, sum_pair hEF, ite_eq_right fun h' => disjoint_left.1 hd (h'.1 hf) hf,
        ite_eq_left ⟨Subset.refl _, hd⟩, zero_add]
    refine ⟨{E, F}, fun _ => D E F, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_,
      fun S hS S' hS' => ?_, fun C hC _ => ?_, fun _ _ => h.nonneg hE hF, fun _ _ => rfl, fun U hU V hV => ?_⟩
    · rcases hmemT.1 hS with rfl | rfl
      · exact ⟨e, he⟩
      · exact ⟨f, hf⟩
    · rcases hmemT.1 hS with rfl | rfl
      · exact hcE ▸ ⟨f, hf⟩
      · exact hcF ▸ ⟨e, he⟩
    · rcases hmemT.1 hS with rfl | rfl
      · exact hmemT.2 (Or.inr hcE)
      · exact hmemT.2 (Or.inl hcF)
    · rcases hmemT.1 hS with rfl | rfl
      · exact hrelA hE
      · exact hrelA hF
    · rcases hmemT.1 hS with rfl | rfl <;> rcases hmemT.1 hS' with rfl | rfl
      · exact Or.inl (Subset.refl _)
      · exact hEF'
      · exact hEF'.symm
      · exact Or.inl (Subset.refl _)
    · rw [hact] at hC
      exact hC
    · rw [hact, mem_insert, mem_singleton] at hU hV
      rcases hU with rfl | rfl <;> rcases hV with rfl | rfl
      · rw [h.zero _ hE, clusterDist_self ⟨e, he⟩]
      · exact hval.symm
      · rw [h.symm _ hF _ hE]
        exact hval'.symm
      · rw [h.zero _ hF, clusterDist_self ⟨f, hf⟩]

/-- **The four-point condition gives a tree**, on clusters, by induction on their number. -/
theorem exists_model (n : ℕ) : ∀ {P : Finset (Finset X)} {D : Finset X → Finset X → ℝ},
    P.card = n → IsClusters P → IsClusterFP P D → ∃ T w, IsModel P D T w := by
  induction n with
  | zero =>
    intro P D hc hP h
    exact IsModel.of_card_le_two h hP (by omega)
  | succ n ih =>
    intro P D hc hP h
    by_cases h3 : 3 ≤ P.card
    · obtain ⟨A, hA, B, hB, hAB, r, hr⟩ := exists_nbr_pair h3 h
      have hc' := hP.card_join hA hB hAB
      obtain ⟨T', w', hm⟩ := ih (by omega) (hP.join hA hB) (h.join hP hA hB hr)
      exact IsModel.of_join h hP h3 hA hB hAB hr hm
    · exact IsModel.of_card_le_two h hP (by omega)

/-- **Buneman's four-point theorem.** A symmetric function vanishing on the diagonal, with the four-point
condition, is the metric of a tree with nonnegative weights, positive on its internal edges. Weights may vanish on
pendant edges: the function need not separate points. -/
theorem exists_tree_of_isFourPoint [Nonempty X] {δ : X → X → ℝ} (h0 : ∀ x, δ x x = 0)
    (hs : ∀ x y, δ x y = δ y x) (h4 : IsFourPoint δ) :
    ∃ (T : Finset (Finset X)) (w : Finset X → ℝ), IsUnrootedTree T ∧ (∀ A ∈ T, 0 ≤ w A ∧ w Aᶜ = w A) ∧
      (∀ A ∈ internalSides T, 0 < w A) ∧ treeMetric T w = δ := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hFP : IsClusterFP (init δ).active (init δ).dist := by
      refine ⟨fun E hE => ?_, fun E hE F hF => ?_, fun a ha b hb c hc d hd => ?_⟩
      · obtain ⟨x, -, rfl⟩ := mem_image.1 hE
        simp [init, h0]
      · obtain ⟨x, -, rfl⟩ := mem_image.1 hE
        obtain ⟨y, -, rfl⟩ := mem_image.1 hF
        simpa [init] using hs x y
      · obtain ⟨x, -, rfl⟩ := mem_image.1 ha
        obtain ⟨y, -, rfl⟩ := mem_image.1 hb
        obtain ⟨z, -, rfl⟩ := mem_image.1 hc
        obtain ⟨t, -, rfl⟩ := mem_image.1 hd
        simpa [init, le_max_iff] using h4 x y z t
    obtain ⟨T, w, hm⟩ := exists_model _ rfl (isClusters_init δ) hFP
    have hsing : ∀ x : X, ({x} : Finset X) ∈ T := by
      intro x
      refine hm.blocks _ (mem_image_of_mem _ (mem_univ x)) fun e => ?_
      have := congrArg card e
      rw [card_singleton, card_univ] at this
      omega
    -- drop the internal edges of weight zero
    let T₀ : Finset (Finset X) := T.filter fun S => 0 < w S ∨ S.card = 1 ∨ Sᶜ.card = 1
    have hT₀ : ∀ {S : Finset X}, S ∈ T₀ → S ∈ T := fun hS => (mem_filter.1 hS).1
    have hS₀ : IsSplitFamily T₀ := by
      refine ⟨fun S hS => hm.nonempty S (hT₀ hS), fun S hS => hm.compl_nonempty S (hT₀ hS), fun S hS => ?_,
        fun x => mem_filter.2 ⟨hsing x, Or.inr (Or.inl (card_singleton x))⟩, fun S hS S' hS' =>
          hm.compat S (hT₀ hS) S' (hT₀ hS')⟩
      obtain ⟨hS, h'⟩ := mem_filter.1 hS
      refine mem_filter.2 ⟨hm.compl_mem S hS, ?_⟩
      rw [hm.weight_compl S hS, compl_compl]
      tauto
    refine ⟨T₀, w, (isUnrootedTree_iff hX T₀).2 hS₀, fun A hA => ⟨hm.nonneg A (hT₀ hA),
      hm.weight_compl A (hT₀ hA)⟩, fun A hA => ?_, ?_⟩
    · obtain ⟨hA, h2, h2'⟩ := mem_filter.1 hA
      obtain ⟨-, h'⟩ := mem_filter.1 hA
      rcases h' with h' | h' | h'
      · exact h'
      · omega
      · omega
    · funext x y
      have h1 : δ x y = (init δ).dist {x} {y} := by simp [init]
      rw [h1, hm.dist _ (mem_image_of_mem _ (mem_univ x)) _ (mem_image_of_mem _ (mem_univ y)),
        ← treeMetric_eq_clusterDist, treeMetric, treeMetric]
      refine sum_subset (fun S hS => ?_) fun S hS hnS => ?_
      · obtain ⟨hS, h'⟩ := mem_filter.1 hS
        exact mem_filter.2 ⟨hT₀ hS, h'⟩
      · obtain ⟨hST, h'⟩ := mem_filter.1 hS
        have hnot : ¬ (0 < w S ∨ S.card = 1 ∨ Sᶜ.card = 1) := fun hc =>
          hnS (mem_filter.2 ⟨mem_filter.2 ⟨hST, hc⟩, h'⟩)
        have hpos : ¬ 0 < w S := fun hc => hnot (Or.inl hc)
        exact le_antisymm (not_lt.1 hpos) (hm.nonneg S hST)
  · have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    obtain ⟨x⟩ := ‹Nonempty X›
    have huniv : ∀ y : X, ({y} : Finset X) = univ := fun y => eq_univ_iff_forall.2 fun z => by
      simp [Subsingleton.elim z y]
    refine ⟨∅, fun _ => 0, ⟨{univ}, ⟨mem_singleton_self _, fun y => by simp [huniv y], fun A hA => ?_,
      fun A hA B hB => ?_⟩, by simp [unroot]⟩, by simp, by simp [internalSides], ?_⟩
    · rw [mem_singleton.1 hA]
      exact ⟨x, mem_univ x⟩
    · rw [mem_singleton.1 hA, mem_singleton.1 hB]
      exact Or.inl (Subset.refl _)
    · funext a b
      rw [Subsingleton.elim a b, h0]
      simp [treeMetric]

/-- **Buneman's four-point theorem**, both ways: a symmetric function vanishing on the diagonal has the four-point
condition exactly when it is the metric of a tree with nonnegative weights. -/
theorem isFourPoint_iff [Nonempty X] {δ : X → X → ℝ} (h0 : ∀ x, δ x x = 0) (hs : ∀ x y, δ x y = δ y x) :
    IsFourPoint δ ↔ ∃ (T : Finset (Finset X)) (w : Finset X → ℝ), IsUnrootedTree T ∧
      (∀ A ∈ T, 0 ≤ w A ∧ w Aᶜ = w A) ∧ treeMetric T w = δ := by
  constructor
  · intro h4
    obtain ⟨T, w, h1, h2, -, h3⟩ := exists_tree_of_isFourPoint h0 hs h4
    exact ⟨T, w, h1, h2, h3⟩
  · rintro ⟨T, w, h1, h2, rfl⟩
    exact isFourPoint_treeMetric h1 h2

end Buneman

end Phylogenetics.FourPoint
