module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed

/-!
# Analyticity of the matrix exponential

A matrix has no canonical norm, so `NormedSpace.exp_analytic` does not apply to it directly. The
statements here mention only the topology of `Matrix`; the proofs open the `L∞` operator norm
(`Matrix.Norms.Operator`) locally, as Mathlib's `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` does.

## Main results

* `Matrix.analyticOnNhd_exp_smul`: the entries of `exp (t • A)` are entire in the real variable `t`.
-/

@[expose] public section

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The entries of `exp (t • A)` are entire in the real variable `t`. -/
theorem analyticOnNhd_exp_smul (A : Matrix m m ℝ) (i j : m) :
    AnalyticOnNhd ℝ (fun t : ℝ => NormedSpace.exp (t • A) i j) Set.univ := by
  open scoped Matrix.Norms.Operator in
  have hsmul : AnalyticOnNhd ℝ (fun t : ℝ => t • A) Set.univ :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight A).analyticOnNhd _
  have hentry : AnalyticOnNhd ℝ (fun M : Matrix m m ℝ => M i j) Set.univ :=
    (LinearMap.toContinuousLinearMap (entryLinearMap ℝ ℝ i j)).analyticOnNhd _
  intro t _
  have hexp : AnalyticAt ℝ (fun s : ℝ => NormedSpace.exp (s • A)) t :=
    AnalyticAt.comp (g := NormedSpace.exp) (f := fun s : ℝ => s • A)
      (NormedSpace.exp_analytic (𝕂 := ℝ) (t • A)) (hsmul t (Set.mem_univ _))
  exact AnalyticAt.comp (g := fun M : Matrix m m ℝ => M i j)
    (f := fun s : ℝ => NormedSpace.exp (s • A)) (hentry _ (Set.mem_univ _)) hexp

end Matrix
