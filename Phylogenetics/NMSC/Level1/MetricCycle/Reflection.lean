module

public import Phylogenetics.NMSC.Level1.MetricCycle.Basic
/-!
# The mirror image of a cycle

Reversing the cyclic ordering (`i ↦ d - i`, with the hybrid component `C₀` fixed) exchanges the two
hybrid edges and reverses the edge lengths (`Phylogenetics.MetricCycle.reflect`). The quartet CFs of
the components are invariant (`Phylogenetics.cycleCF_reflect`). -/

@[expose] public noncomputable section

open Finset

namespace Phylogenetics

variable {d : ℕ}

/-- The mirror image of a metric cycle: the inheritance probabilities are exchanged, and the edge
`w m` becomes the edge `w (d - 1 - m)`. -/
def MetricCycle.reflect (Ω : MetricCycle d) : MetricCycle d where
  γ := 1 - Ω.γ
  w := fun m => Ω.w (d - 1 - m)
  γ_pos := by linarith [Ω.γ_lt_one]
  γ_lt_one := by linarith [Ω.γ_pos]
  w_pos := fun m h1 h2 => Ω.w_pos (d - 1 - m) (by omega) (by omega)

/-- The position of a component in the mirror image: `0 ↦ 0` and `i ↦ d - i`. -/
def reflectPos (d i : ℕ) : ℕ := if i = 0 then 0 else d - i

/-- Reversing the path `0, 1, …, d` (`x ↦ d - x`) reverses the edge lengths: the path from `lo`
to `hi` becomes the path from `d - hi` to `d - lo`. -/
private theorem rf_pathLen_reflect (w : ℕ → ℝ) (hd : 0 < d) {lo hi : ℕ} (hhi : hi ≤ d) :
    pathLen (fun m => w (d - 1 - m)) lo hi = pathLen w (d - hi) (d - lo) := by
  simp only [pathLen]
  rw [Finset.sum_Ico_reflect w lo (n := d - 1) (by omega), show d - 1 + 1 = d by omega]

/-- Reversing the path `0, 1, …, d` (`x ↦ d - x`) preserves the quartet CFs of the trees whose
taxa hang from it: it reverses the order of the four positions, so it keeps the split and maps the
internal path to its mirror image. -/
private theorem rf_pathCF_reflect (w : ℕ → ℝ) (hd : 0 < d) {a b c e : ℕ} (ha : a ≤ d)
    (hb : b ≤ d) (hc : c ≤ d) (he : e ≤ d) :
    pathCF (fun m => w (d - 1 - m)) a b c e = pathCF w (d - a) (d - b) (d - c) (d - e) := by
  -- `x ↦ d - x` exchanges `min` and `max`.
  have hmin : ∀ x y, x ≤ d → y ≤ d → min (d - x) (d - y) = d - max x y := fun x y _ _ => by
    omega
  have hmax : ∀ x y, x ≤ d → y ≤ d → max (d - x) (d - y) = d - min x y := fun x y _ _ => by
    omega
  -- The two middle positions `s₂ = max (min a b) (min c e)` and `s₃ = min (max a b) (max c e)`
  -- become `d - s₃` and `d - s₂`.
  have hs2 : max (min a b) (min c e) ≤ d := by omega
  have hs3 : min (max a b) (max c e) ≤ d := by omega
  rw [mb_pathCF_eq (fun m => w (d - 1 - m)) a b c e _ _ rfl rfl,
    mb_pathCF_eq w (d - a) (d - b) (d - c) (d - e) _ _ rfl rfl,
    hmin a b ha hb, hmin c e hc he, hmax a b ha hb, hmax c e hc he,
    hmax (max a b) (max c e) (max_le ha hb) (max_le hc he),
    hmin (min a b) (min c e) ((min_le_left a b).trans ha) ((min_le_left c e).trans hc),
    hmin _ _ hs3 hs2, hmax _ _ hs3 hs2, max_comm (min (max a b) (max c e)),
    min_comm (min (max a b) (max c e)), rf_pathLen_reflect w hd (max_le hs2 hs3)]
  -- The split is kept.
  by_cases h : max a b < min c e ∨ max c e < min a b
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem cycleCF_reflect (Ω : MetricCycle d) {a b c e : ℕ} (ha : a < d) (hb : b < d) (hc : c < d)
    (he : e < d)     :
    cycleCF Ω.reflect (reflectPos d a) (reflectPos d b) (reflectPos d c) (reflectPos d e) =
      cycleCF Ω a b c e := by
  have hd : 0 < d := by omega
  -- In the mirror image, a component at position `x < d` is at `reflectPos d x`; reversing the
  -- path `0, …, d` sends the displayed tree with `C₀` at position `0` to the one with `C₀` at
  -- position `d`, and conversely.
  have h1 : ∀ x, x < d → reflectPos d x ≤ d ∧ d - reflectPos d x = toRightEnd d x := by
    intro x hx
    unfold reflectPos toRightEnd
    split_ifs <;> omega
  have h2 : ∀ x, x < d →
      toRightEnd d (reflectPos d x) ≤ d ∧ d - toRightEnd d (reflectPos d x) = x := by
    intro x hx
    unfold reflectPos toRightEnd
    split_ifs <;> omega
  have h0 : ∀ x, x < d → (reflectPos d x = 0 ↔ x = 0) := by
    intro x hx
    unfold reflectPos
    split_ifs <;> omega
  have hT : ∀ x, x ≠ 0 → toRightEnd d x = x := fun x hx => ite_eq_right hx
  have hzero : (reflectPos d a = 0 ∨ reflectPos d b = 0 ∨ reflectPos d c = 0 ∨
      reflectPos d e = 0) ↔ (a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0) := by
    rw [h0 a ha, h0 b hb, h0 c hc, h0 e he]
  unfold cycleCF
  rw [show Ω.reflect.w = fun m => Ω.w (d - 1 - m) from rfl,
    show Ω.reflect.γ = 1 - Ω.γ from rfl,
    rf_pathCF_reflect Ω.w hd (h1 a ha).1 (h1 b hb).1 (h1 c hc).1 (h1 e he).1,
    rf_pathCF_reflect Ω.w hd (h2 a ha).1 (h2 b hb).1 (h2 c hc).1 (h2 e he).1,
    (h1 a ha).2, (h1 b hb).2, (h1 c hc).2, (h1 e he).2,
    (h2 a ha).2, (h2 b hb).2, (h2 c hc).2, (h2 e he).2]
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0 ∨ e = 0
  · -- A network quarnet: the two displayed trees are exchanged, and so are `γ` and `1 - γ`.
    rw [ite_eq_left h, ite_eq_left (hzero.2 h)]
    ring
  · -- A tree quarnet.
    rw [ite_eq_right h, ite_eq_right (fun h' => h (hzero.1 h')), hT a (by tauto),
      hT b (by tauto), hT c (by tauto), hT e (by tauto)]

end Phylogenetics
