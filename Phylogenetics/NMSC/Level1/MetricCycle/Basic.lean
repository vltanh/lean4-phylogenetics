module

public import Phylogenetics.NMSC.Level1.Defs
/-!
# The metric cycle: basic lemmas

Lemmas on the quartet CFs of the components of a metric cycle (`Phylogenetics.cycleCF`): path
lengths, the symmetries of the CF formulas, their values when the hybrid component is absent or
present, and their positivity. `posCF Ω` is the CF of the components labelled by their positions. -/

@[expose] public noncomputable section

open Finset

namespace Phylogenetics

variable {d : ℕ}

/-- The component CF of the cycle `Ω` with components labelled by their positions. -/
def posCF (Ω : MetricCycle d) : Fin d → Fin d → Fin d → Fin d → ℝ :=
  fun a b c e => cycleCF Ω a b c e

/-- `toRightEnd d` moves only position `0`. -/
theorem toRightEnd_of_ne_zero {a : ℕ} (ha : a ≠ 0) : toRightEnd d a = a := by
  simp [toRightEnd, ha]

/-! ### Path lengths -/

theorem pathLen_add (w : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    pathLen w a c = pathLen w a b + pathLen w b c :=
  (Finset.sum_Ico_consecutive w hab hbc).symm

theorem pathLen_self (w : ℕ → ℝ) (a : ℕ) : pathLen w a a = 0 := by
  simp [pathLen]

theorem pathLen_succ (w : ℕ → ℝ) (a : ℕ) : pathLen w a (a + 1) = w a := by
  simp [pathLen]

/-- Paths inside the cycle have positive length. -/
theorem pathLen_pos (Ω : MetricCycle d) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ d - 1) :
    0 < pathLen Ω.w a b := by
  unfold pathLen
  refine Finset.sum_pos (fun m hm => ?_) ⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩
  rw [Finset.mem_Ico] at hm
  exact Ω.w_pos m (by omega) (by omega)

theorem pathLen_nonneg (Ω : MetricCycle d) {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ d - 1) :
    0 ≤ pathLen Ω.w a b := by
  unfold pathLen
  refine Finset.sum_nonneg (fun m hm => ?_)
  rw [Finset.mem_Ico] at hm
  exact (Ω.w_pos m (by omega) (by omega)).le

/-! ### Symmetries and values of the quartet CFs -/

/-- `pathCF` with the end points `lo` and `hi` of its internal path named. -/
theorem mb_pathCF_eq (w : ℕ → ℝ) (a b c e lo hi : ℕ)
    (hlo : min (max (min a b) (min c e)) (min (max a b) (max c e)) = lo)
    (hhi : max (max (min a b) (min c e)) (min (max a b) (max c e)) = hi) :
    pathCF w a b c e = if max a b < min c e ∨ max c e < min a b then
      1 - 2 / 3 * Real.exp (-pathLen w lo hi) else 1 / 3 * Real.exp (-pathLen w lo hi) := by
  rw [pathCF, hlo, hhi]

theorem pathCF_swap_left (w : ℕ → ℝ) (a b c e : ℕ) : pathCF w b a c e = pathCF w a b c e := by
  simp only [pathCF, min_comm b a, max_comm b a]

theorem pathCF_swap_right (w : ℕ → ℝ) (a b c e : ℕ) : pathCF w a b e c = pathCF w a b c e := by
  simp only [pathCF, min_comm e c, max_comm e c]

theorem pathCF_swap_pairs (w : ℕ → ℝ) (a b c e : ℕ) : pathCF w c e a b = pathCF w a b c e := by
  rw [mb_pathCF_eq w c e a b _ _ rfl rfl, mb_pathCF_eq w a b c e _ _ rfl rfl,
    max_comm (min c e) (min a b), min_comm (max c e) (max a b)]
  by_cases h : max a b < min c e ∨ max c e < min a b
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]

/-- The three quartet CFs of four taxa hanging from a path at positions `a < b < c < e`. -/
theorem pathCF_of_lt (w : ℕ → ℝ) {a b c e : ℕ} (hab : a < b) (hbc : b < c) (hce : c < e) :
    pathCF w a b c e = 1 - 2 / 3 * Real.exp (-pathLen w b c) ∧
    pathCF w a c b e = 1 / 3 * Real.exp (-pathLen w b c) ∧
    pathCF w a e b c = 1 / 3 * Real.exp (-pathLen w b c) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mb_pathCF_eq w a b c e b c (by omega) (by omega), ite_eq_left (by omega)]
  · rw [mb_pathCF_eq w a c b e b c (by omega) (by omega), ite_eq_right (by omega)]
  · rw [mb_pathCF_eq w a e b c b c (by omega) (by omega), ite_eq_right (by omega)]

theorem cycleCF_swap_left (Ω : MetricCycle d) (a b c e : ℕ) :
    cycleCF Ω b a c e = cycleCF Ω a b c e := by
  unfold cycleCF
  rw [pathCF_swap_left Ω.w a b c e,
    pathCF_swap_left Ω.w (toRightEnd d a) (toRightEnd d b) (toRightEnd d c) (toRightEnd d e)]
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0
  · rw [ite_eq_left h, ite_eq_left (by tauto)]
  · rw [ite_eq_right h, ite_eq_right (by tauto)]

theorem cycleCF_swap_right (Ω : MetricCycle d) (a b c e : ℕ) :
    cycleCF Ω a b e c = cycleCF Ω a b c e := by
  unfold cycleCF
  rw [pathCF_swap_right Ω.w a b c e,
    pathCF_swap_right Ω.w (toRightEnd d a) (toRightEnd d b) (toRightEnd d c) (toRightEnd d e)]
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0
  · rw [ite_eq_left h, ite_eq_left (by tauto)]
  · rw [ite_eq_right h, ite_eq_right (by tauto)]

theorem cycleCF_swap_pairs (Ω : MetricCycle d) (a b c e : ℕ) :
    cycleCF Ω c e a b = cycleCF Ω a b c e := by
  unfold cycleCF
  rw [pathCF_swap_pairs Ω.w a b c e,
    pathCF_swap_pairs Ω.w (toRightEnd d a) (toRightEnd d b) (toRightEnd d c) (toRightEnd d e)]
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0
  · rw [ite_eq_left h, ite_eq_left (by tauto)]
  · rw [ite_eq_right h, ite_eq_right (by tauto)]

/-- A quartet of non-hybrid components induces a tree quarnet. -/
theorem cycleCF_of_ne_zero (Ω : MetricCycle d) {a b c e : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (he : e ≠ 0) : cycleCF Ω a b c e = pathCF Ω.w a b c e := by
  rw [cycleCF, ite_eq_right (by tauto)]

/-- A quartet containing the hybrid component induces a network quarnet: the mixture of its two
displayed trees. -/
theorem cycleCF_zero (Ω : MetricCycle d) (b c e : ℕ) :
    cycleCF Ω 0 b c e = Ω.γ * pathCF Ω.w 0 b c e +
      (1 - Ω.γ) * pathCF Ω.w d (toRightEnd d b) (toRightEnd d c) (toRightEnd d e) := by
  rw [cycleCF, ite_eq_left (Or.inl rfl), show toRightEnd d 0 = d from ite_eq_left rfl]

/-- A quartet tree on four distinct positions of the path `0, 1, …, d` has a positive CF: its
internal path joins the two middle positions, so it lies inside `1, …, d - 1` and has
nonnegative length. -/
private theorem mb_pathCF_pos (Ω : MetricCycle d) {a b c e : ℕ} (ha : a ≤ d) (hb : b ≤ d)
    (hc : c ≤ d) (he : e ≤ d) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e) : 0 < pathCF Ω.w a b c e := by
  rw [mb_pathCF_eq Ω.w a b c e _ _ rfl rfl]
  have ht := pathLen_nonneg Ω
    (a := min (max (min a b) (min c e)) (min (max a b) (max c e)))
    (b := max (max (min a b) (min c e)) (min (max a b) (max c e))) (by omega) (by omega)
  have h1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h2 := Real.exp_pos (-pathLen Ω.w (min (max (min a b) (min c e)) (min (max a b) (max c e)))
    (max (max (min a b) (min c e)) (min (max a b) (max c e))))
  split_ifs <;> linarith

private theorem mb_toRightEnd_le {x : ℕ} (hx : x < d) : toRightEnd d x ≤ d := by
  unfold toRightEnd; split_ifs <;> omega

private theorem mb_toRightEnd_ne {x y : ℕ} (hx : x < d) (hy : y < d) (hxy : x ≠ y) :
    toRightEnd d x ≠ toRightEnd d y := by
  unfold toRightEnd; split_ifs <;> omega

/-- Quartet CFs of distinct components are positive. -/
theorem cycleCF_pos (Ω : MetricCycle d) {a b c e : ℕ} (ha : a < d) (hb : b < d) (hc : c < d)
    (he : e < d) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e)
    (hce : c ≠ e) : 0 < cycleCF Ω a b c e := by
  unfold cycleCF
  split_ifs
  · exact add_pos
      (mul_pos Ω.γ_pos (mb_pathCF_pos Ω ha.le hb.le hc.le he.le hab hac hae hbc hbe hce))
      (mul_pos (sub_pos.mpr Ω.γ_lt_one)
        (mb_pathCF_pos Ω (mb_toRightEnd_le ha) (mb_toRightEnd_le hb) (mb_toRightEnd_le hc)
          (mb_toRightEnd_le he) (mb_toRightEnd_ne ha hb hab) (mb_toRightEnd_ne ha hc hac)
          (mb_toRightEnd_ne ha he hae) (mb_toRightEnd_ne hb hc hbc) (mb_toRightEnd_ne hb he hbe)
          (mb_toRightEnd_ne hc he hce)))
  · exact mb_pathCF_pos Ω ha.le hb.le hc.le he.le hab hac hae hbc hbe hce

end Phylogenetics
