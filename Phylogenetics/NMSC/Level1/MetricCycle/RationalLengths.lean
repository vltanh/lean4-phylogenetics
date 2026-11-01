module

public import Phylogenetics.NMSC.Level1.Defs
/-!
# Edge lengths with rational attenuations

An explicit metric cycle can choose the factors `x_m = e^{-w_m}`, rational numbers in `(0, 1)`, and
take the edge lengths `w_m = log (1 / x_m)` (`Phylogenetics.ratLen x m`), which are positive
(`Phylogenetics.ratLen_pos`). Then `e^{-(w_a + ⋯ + w_{b-1})}` is the rational number
`x_a ⋯ x_{b-1}` (`Phylogenetics.exp_neg_pathLen_ratLen`), so that the quartet CFs of the cycle, and
sums of them, are rational, and the kernel can compare them exactly. -/

@[expose] public noncomputable section

open Finset

namespace Phylogenetics

/-- The edge lengths `w_m = log (1 / x_m)`, whose factors `e^{-w_m}` are the rational numbers
`x_m` (`Phylogenetics.exp_neg_ratLen`). -/
def ratLen (x : ℕ → ℚ) (m : ℕ) : ℝ := Real.log ((x m : ℝ)⁻¹)

/-- The edge length `log (1 / x_m)` is positive for `0 < x_m < 1`. -/
theorem ratLen_pos {x : ℕ → ℚ} {m : ℕ} (h0 : 0 < x m) (h1 : x m < 1) : 0 < ratLen x m := by
  have h0' : (0 : ℝ) < x m := by exact_mod_cast h0
  have h1' : (x m : ℝ) < 1 := by exact_mod_cast h1
  exact Real.log_pos ((one_lt_inv₀ h0').2 h1')

/-- `e^{-w_m} = x_m`. -/
theorem exp_neg_ratLen {x : ℕ → ℚ} {m : ℕ} (h0 : 0 < x m) : Real.exp (-ratLen x m) = x m := by
  have h0' : (0 : ℝ) < x m := by exact_mod_cast h0
  rw [ratLen, Real.exp_neg, Real.exp_log (inv_pos.2 h0'), inv_inv]

/-- `e^{-(w_a + ⋯ + w_{b-1})} = x_a ⋯ x_{b-1}`. -/
theorem exp_neg_pathLen_ratLen {x : ℕ → ℚ} (h0 : ∀ m, 0 < x m) (a b : ℕ) :
    Real.exp (-pathLen (ratLen x) a b) = ((∏ m ∈ Ico a b, x m : ℚ) : ℝ) := by
  rw [pathLen, ← Finset.sum_neg_distrib, Real.exp_sum, Rat.cast_prod]
  exact Finset.prod_congr rfl fun m _ => exp_neg_ratLen (h0 m)

end Phylogenetics
