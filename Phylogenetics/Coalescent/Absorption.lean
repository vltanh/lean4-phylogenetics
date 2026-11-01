module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Phylogenetics.Coalescent.Tavare
public import Mathlib.Tactic.NormNum

/-!
# The population above the root: Kingman's coalescent run for an infinite time

As `t → ∞`, `g_kj(t) → 1` if `j = 1` and `→ 0` otherwise (for `k ≥ 1`), so `exp(tQ)(F, G)`
converges to the probability that the jump chain, run until one root is left, ends at `G`.

## Main results

* `tendsto_deathProb`: the limits of `g_kj(t)`.
* `tendsto_kingmanTransition`: the entries of `exp(tQ)` at a forest converge to those of
  `kingmanAbsorption`.
* `kingmanAbsorption_apply`: `kingmanAbsorption F G = J^{k-1}(F, G)` for complete `G`, `0`
  otherwise (and the identity on the empty forest).
* `kingmanTransition_mul_kingmanAbsorption`: running for a finite time and then for an infinite
  time is running for an infinite time.
* `sum_kingmanTransition_comp`, `kingmanTransition_comp`, `kingmanAbsorption_comp`: a map of forests
  that intertwines the generators lumps the coalescent.
-/

@[expose] public section

namespace Phylogenetics

open Finset Real Filter Topology

variable {L : Type*} [Fintype L] [DecidableEq L]

private theorem absorb_tavareCoeff_one (k : ℕ) (hk : 1 ≤ k) : tavareCoeff k 1 1 = 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  norm_num [tavareCoeff, div_self hk']

/-- `exp(-(m choose 2) t)` tends to `1` if `m = 1` and to `0` if `m ≥ 2`. -/
private theorem absorb_tendsto_exp (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => exp (-(((m.choose 2 : ℕ) : ℝ) * t))) atTop
      (𝓝 (if m = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h
    simp
  · have hpos : (0 : ℝ) < ((m.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    exact tendsto_exp_comp_nhds_zero.mpr
      (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hpos tendsto_id))

theorem tendsto_deathProb (k j : ℕ) (hk : 1 ≤ k) :
    Tendsto (deathProb k j) atTop (𝓝 (if j = 1 then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h : deathProb k 0 = fun _ => 0 := funext fun t => deathProb_zero_right hk t
    rw [h, ite_eq_right (by norm_num)]
    exact tendsto_const_nhds
  rcases lt_or_ge k j with hkj | hjk
  · have h : deathProb k j = fun _ => 0 := funext fun t => deathProb_eq_zero_of_lt hkj t
    rw [h, ite_eq_right (by omega)]
    exact tendsto_const_nhds
  have h := funext fun t => deathProb_eq_tavare k j hj hjk t
  rw [h]
  have hlim : (if j = 1 then (1 : ℝ) else 0) =
      ∑ m ∈ Icc j k, (if m = 1 then (1 : ℝ) else 0) * tavareCoeff k j m := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Icc j k) 1 (fun m => tavareCoeff k j m)]
    split_ifs with h1 h2 h2
    · subst h1; exact (absorb_tavareCoeff_one k hk).symm
    · exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) h2
    · exact absurd (Finset.mem_Icc.1 h2).1 (by omega)
    · rfl
  rw [hlim]
  refine tendsto_finsetSum _ fun m hm => ?_
  exact (absorb_tendsto_exp m (by have := (Finset.mem_Icc.1 hm).1; omega)).mul_const _

/-- The limit of `exp(tQ)(F, G)`, computed from the factorization. -/
private theorem absorb_tendsto {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 (if #(roots F) = 0 then (if G = F then 1 else 0)
        else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0)) := by
  rcases Nat.eq_zero_or_pos (#(roots F)) with h0 | hpos
  · rw [ite_eq_left h0]
    have h : (fun t => kingmanTransition t F G) = fun _ => if G = F then 1 else 0 :=
      funext fun t => kingmanTransition_of_card_roots_le_one hF (by omega) t G
    rw [h]
    exact tendsto_const_nhds
  · rw [ite_eq_right (by omega)]
    have h : (fun t => kingmanTransition t F G) = fun t =>
        deathProb (#(roots F)) (#(roots G)) t * (jumpMatrix ^ (#(roots F) - #(roots G))) F G :=
      funext fun t => kingmanTransition_apply hF t G
    rw [h]
    have hl := (tendsto_deathProb (#(roots F)) (#(roots G)) hpos).mul_const
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G)
    split_ifs at hl ⊢ with hG
    · rw [hG] at hl ⊢
      simpa using hl
    · simpa using hl

theorem tendsto_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  have h := absorb_tendsto hF G
  have e : kingmanAbsorption F G = _ := h.limUnder_eq
  rw [e]
  exact h

theorem kingmanAbsorption_apply {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      if #(roots F) = 0 then (if G = F then 1 else 0)
      else if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 1)) F G else 0 :=
  (absorb_tendsto hF G).limUnder_eq

theorem kingmanAbsorption_nonneg {F : Finset (Finset L)} (hF : IsForest F)
    (G : Finset (Finset L)) : 0 ≤ kingmanAbsorption F G := by
  rw [kingmanAbsorption_apply hF]
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact jumpMatrix_pow_nonneg _ _ _
  · exact le_rfl

theorem kingmanAbsorption_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 := by
  have h1 : Tendsto (fun t => ∑ G, kingmanTransition t F G) atTop
      (𝓝 (∑ G, kingmanAbsorption F G)) :=
    tendsto_finsetSum _ fun G _ => tendsto_kingmanTransition hF G
  have h2 : (fun t => ∑ G, kingmanTransition t F G) = fun _ => 1 :=
    funext fun t => kingmanTransition_sum hF t
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- First-step analysis in the population above the root. -/
theorem kingmanAbsorption_first_step {F : Finset (Finset L)} (hF : IsForest F)
    (hk : 2 ≤ #(roots F)) (G : Finset (Finset L)) :
    kingmanAbsorption F G =
      (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ * ∑ F' ∈ merges F, kingmanAbsorption F' G := by
  rw [kingmanAbsorption_apply hF, ite_eq_right (by omega)]
  have hm : ∀ F' ∈ merges F, kingmanAbsorption F' G =
      if #(roots G) = 1 then (jumpMatrix ^ (#(roots F) - 2)) F' G else 0 := by
    intro F' hF'
    obtain ⟨hF'f, hcard, -⟩ := hF.of_mem_merges hF'
    rw [kingmanAbsorption_apply hF'f, ite_eq_right (by omega),
      show #(roots F') - 1 = #(roots F) - 2 by omega]
  rw [Finset.sum_congr rfl hm]
  split_ifs with hG
  · rw [show #(roots F) - 1 = (#(roots F) - 2) + 1 by omega, jumpMatrix_pow_succ_apply hk]
  · simp

theorem kingmanTransition_mul_kingmanAbsorption {F : Finset (Finset L)} (hF : IsForest F)
    (t : ℝ) (G : Finset (Finset L)) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have hlim : Tendsto (fun s => kingmanTransition (t + s) F G) atTop
      (𝓝 (kingmanAbsorption F G)) :=
    (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  have heq : (fun s => kingmanTransition (t + s) F G) =
      fun s => ∑ F', kingmanTransition t F F' * kingmanTransition s F' G := by
    funext s
    rw [kingmanTransition_add, Matrix.mul_apply]
  rw [heq] at hlim
  have hlim2 : Tendsto (fun s => ∑ F', kingmanTransition t F F' * kingmanTransition s F' G)
      atTop (𝓝 (∑ F', kingmanTransition t F F' * kingmanAbsorption F' G)) := by
    refine tendsto_finsetSum _ fun F' _ => ?_
    by_cases h : kingmanTransition t F F' = 0
    · simp only [h, zero_mul]
      exact tendsto_const_nhds
    · have hF' : IsForest F' := by
        rw [kingmanTransition_apply hF] at h
        exact (jumpMatrix_pow_support hF (right_ne_zero_of_mul h)).1
      exact (tendsto_kingmanTransition hF' G).const_mul _
  exact tendsto_nhds_unique hlim2 hlim

/-! ### Lumping along a map of forests -/

section Lumping

variable {L' : Type*} [Fintype L'] [DecidableEq L']

/-- The generator is supported on the forest itself and its merges. -/
private theorem lump_kingmanGenerator_ne_zero {F G : Finset (Finset L)} (hF : IsForest F)
    (h : kingmanGenerator F G ≠ 0) : IsForest G := by
  rw [kingmanGenerator_apply_of_isForest] at h
  split_ifs at h with h1 h2
  · exact h1 ▸ hF
  · exact (hF.of_mem_merges h2).1
  · exact absurd rfl h

private theorem lump_sum_kingmanGenerator_pow {Φ : Finset (Finset L) → Finset (Finset L')}
    (hΦ : ∀ F, IsForest F → ∀ w : Finset (Finset L') → ℝ,
      ∑ G, kingmanGenerator F G * w (Φ G) = ∑ G', kingmanGenerator (Φ F) G' * w G')
    (n : ℕ) {F : Finset (Finset L)} (hF : IsForest F) (w : Finset (Finset L') → ℝ) :
    ∑ G, (kingmanGenerator ^ n) F G * w (Φ G) = ∑ G', (kingmanGenerator ^ n) (Φ F) G' * w G' := by
  induction n generalizing F w with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
      ite_true]
  | succ n ih =>
    set u : Finset (Finset L') → ℝ := fun H' => ∑ G', (kingmanGenerator ^ n) H' G' * w G'
      with hu
    have hstep : ∀ H : Finset (Finset L), kingmanGenerator F H *
        ∑ G, (kingmanGenerator ^ n) H G * w (Φ G) = kingmanGenerator F H * u (Φ H) := by
      intro H
      by_cases hQ : kingmanGenerator F H = 0
      · rw [hQ, zero_mul, zero_mul]
      · rw [ih (lump_kingmanGenerator_ne_zero hF hQ) w]
    calc ∑ G, (kingmanGenerator ^ (n + 1)) F G * w (Φ G)
        = ∑ H, kingmanGenerator F H * ∑ G, (kingmanGenerator ^ n) H G * w (Φ G) := by
          simp_rw [pow_succ', Matrix.mul_apply, sum_mul]
          rw [sum_comm]
          simp_rw [mul_sum, mul_assoc]
      _ = ∑ H, kingmanGenerator F H * u (Φ H) := sum_congr rfl fun H _ => hstep H
      _ = ∑ H', kingmanGenerator (Φ F) H' * u H' := hΦ F hF u
      _ = ∑ G', (kingmanGenerator ^ (n + 1)) (Φ F) G' * w G' := by
          simp_rw [hu, pow_succ', Matrix.mul_apply, sum_mul, mul_sum, mul_assoc]
          rw [sum_comm]

set_option backward.isDefEq.respectTransparency false in
/-- **Lumpability from the generator.** A map `Φ` of forests that intertwines the generators lumps
Kingman's coalescent, tested against a function `w` of the image. -/
theorem sum_kingmanTransition_comp {Φ : Finset (Finset L) → Finset (Finset L')}
    (hΦ : ∀ F, IsForest F → ∀ w : Finset (Finset L') → ℝ,
      ∑ G, kingmanGenerator F G * w (Φ G) = ∑ G', kingmanGenerator (Φ F) G' * w G')
    {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) (w : Finset (Finset L') → ℝ) :
    ∑ G, kingmanTransition t F G * w (Φ G) = ∑ G', kingmanTransition t (Φ F) G' * w G' := by
  have h1 : HasSum (fun n : ℕ => ∑ G, ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L)) ^ n) F G * w (Φ G))
      (∑ G, kingmanTransition t F G * w (Φ G)) :=
    hasSum_sum fun G _ => (hasSum_exp_apply _ F G).mul_right _
  have h2 : HasSum (fun n : ℕ => ∑ G', ((n.factorial : ℝ))⁻¹ *
      ((t • kingmanGenerator (L := L')) ^ n) (Φ F) G' * w G')
      (∑ G', kingmanTransition t (Φ F) G' * w G') :=
    hasSum_sum fun G' _ => (hasSum_exp_apply _ _ G').mul_right _
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp_rw [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  rw [lump_sum_kingmanGenerator_pow hΦ n hF w]

/-- Lumpability from the generator, at one forest of the image. -/
theorem kingmanTransition_comp {Φ : Finset (Finset L) → Finset (Finset L')}
    (hΦ : ∀ F, IsForest F → ∀ w : Finset (Finset L') → ℝ,
      ∑ G, kingmanGenerator F G * w (Φ G) = ∑ G', kingmanGenerator (Φ F) G' * w G')
    {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) (G' : Finset (Finset L')) :
    ∑ G, (if Φ G = G' then kingmanTransition t F G else 0) = kingmanTransition t (Φ F) G' := by
  have h := sum_kingmanTransition_comp hΦ hF t fun G'' => if G'' = G' then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h
  exact h

/-- Lumpability from the generator, for the coalescent over an infinite time. -/
theorem kingmanAbsorption_comp {Φ : Finset (Finset L) → Finset (Finset L')}
    (hΦ : ∀ F, IsForest F → ∀ w : Finset (Finset L') → ℝ,
      ∑ G, kingmanGenerator F G * w (Φ G) = ∑ G', kingmanGenerator (Φ F) G' * w G')
    {F : Finset (Finset L)} (hF : IsForest F) (hΦF : IsForest (Φ F)) (G' : Finset (Finset L')) :
    ∑ G, (if Φ G = G' then kingmanAbsorption F G else 0) = kingmanAbsorption (Φ F) G' := by
  have h1 : Filter.Tendsto (fun t => ∑ G, (if Φ G = G' then kingmanTransition t F G else 0))
      Filter.atTop (nhds (∑ G, (if Φ G = G' then kingmanAbsorption F G else 0))) := by
    refine tendsto_finsetSum _ fun G _ => ?_
    split_ifs
    · exact tendsto_kingmanTransition hF G
    · exact tendsto_const_nhds
  have h2 := tendsto_kingmanTransition hΦF G'
  simp_rw [kingmanTransition_comp hΦ hF] at h1
  exact tendsto_nhds_unique h1 h2

end Lumping

end Phylogenetics
