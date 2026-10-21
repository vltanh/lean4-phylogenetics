module

public import Phylogenetics.NMSC.Consistency

/-!
# The gene trees of the network multispecies coalescent

The network multispecies coalescent on a well-formed network is a probability distribution on
gene trees: the weights `Phylogenetics.Net.geneTreeDist s G` are nonnegative
(`Phylogenetics.Net.geneTreeDist_nonneg`, from `Phylogenetics.Net.forestDist_nonneg` for the
forest at the root) and sum to `1` (`Phylogenetics.Net.sum_geneTreeDist`). So every quartet
concordance factor lies in `[0, 1]` (`Phylogenetics.Net.quartetCF_nonneg`,
`Phylogenetics.Net.quartetCF_le_one`).

Every gene tree in its support is a hierarchy: any two of its clusters are nested or disjoint
(`Phylogenetics.geneTreeDist_isHierarchy`). In a hierarchy the displayed quartets are transitive:
if `ax|ce` and `xb|ce` are displayed, so is `ab|ce` (`Phylogenetics.geneTreeDisplays_trans`).
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u

variable {X : Type u} [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-! ### A probability distribution on gene trees -/

/-- The union of two independent random forests with nonnegative weights has nonnegative
weights. -/
theorem forestUnion_nonneg {μ ν : Finset (Finset L) → ℝ} (hμ : ∀ F, 0 ≤ μ F)
    (hν : ∀ F, 0 ≤ ν F) (G : Finset (Finset L)) : 0 ≤ forestUnion μ ν G := by
  unfold forestUnion
  refine Finset.sum_nonneg fun F _ => Finset.sum_nonneg fun F' _ => ?_
  split_ifs
  · exact mul_nonneg (hμ F) (hν F')
  · exact le_rfl

/-- Kingman's coalescent along an edge of nonnegative length keeps the weights of a random forest
nonnegative. -/
theorem vecMul_kingmanTransition_nonneg {μ : Finset (Finset L) → ℝ} (hμ : ∀ F, 0 ≤ μ F) {t : ℝ}
    (ht : 0 ≤ t) (G : Finset (Finset L)) : 0 ≤ (μ ᵥ* kingmanTransition t) G :=
  Finset.sum_nonneg fun F _ => mul_nonneg (hμ F) (kingmanTransition_nonneg ht F G)

mutual

/-- The distribution of the forest of gene lineages at the root of a metric network has
nonnegative weights. -/
theorem Net.forestDist_nonneg (s : L → X) :
    ∀ N : Net X, N.IsMetric → ∀ G, 0 ≤ N.forestDist s G
  | .leaf x, _, G => by
      simp only [Net.forestDist]
      split_ifs <;> norm_num
  | .tree ℓ₁ N₁ ℓ₂ N₂, h, G => by
      obtain ⟨h₁, h₂, hN₁, hN₂⟩ := h
      simp only [Net.forestDist]
      exact forestUnion_nonneg
        (vecMul_kingmanTransition_nonneg (Net.forestDist_nonneg s N₁ hN₁) h₁.le)
        (vecMul_kingmanTransition_nonneg (Net.forestDist_nonneg s N₂ hN₂) h₂.le) G
  | .cycle γ S₁ S₂ ℓ N, h, G => by
      obtain ⟨hγ₀, hγ₁, hℓ, hS₁, hS₂, hN, -⟩ := h
      simp only [Net.forestDist]
      refine Finset.sum_nonneg fun F _ => mul_nonneg
        (vecMul_kingmanTransition_nonneg (Net.forestDist_nonneg s N hN) hℓ.le F)
        (Finset.sum_nonneg fun A _ => mul_nonneg
          (mul_nonneg (pow_nonneg hγ₀.le _) (pow_nonneg (by linarith) _))
          (forestUnion_nonneg (Side.forestDist_nonneg s S₁ hS₁ _)
            (Side.forestDist_nonneg s S₂ hS₂ _) G))

/-- The transition of the forest of gene lineages along a side of a cycle of a metric network has
nonnegative weights. -/
theorem Side.forestDist_nonneg (s : L → X) :
    ∀ S : Side X, S.IsMetric → ∀ F G, 0 ≤ S.forestDist s F G
  | .hyb ℓ, h, F, G => by
      simp only [Side.forestDist]
      exact kingmanTransition_nonneg (le_of_lt h) F G
  | .node ℓ b N S, h, F, G => by
      obtain ⟨hℓ, hb, hN, hS⟩ := h
      simp only [Side.forestDist]
      exact vecMul_kingmanTransition_nonneg (forestUnion_nonneg (Side.forestDist_nonneg s S hS F)
        (vecMul_kingmanTransition_nonneg (Net.forestDist_nonneg s N hN) hb.le)) hℓ.le G

end

/-- Every forest at the root of a network with distinct leaves that has positive weight is a forest
of the sampled lineages, and the weights at the root sum to `1`. -/
private theorem gt_forestDist (N : Net X) (hN : N.leaves.Nodup) (s : L → X) :
    (∀ F, N.forestDist s F = 0 ∨ IsForest F) ∧ ∑ F, N.forestDist s F = 1 := by
  have hE : ∀ a ∈ N.leaves, IsGood (sampledAt s a) := fun _ _ => isGood_singletons _
  have hdisj : ∀ a ∈ N.leaves, ∀ b ∈ N.leaves, a ≠ b →
      Disjoint (lineages (sampledAt s a)) (lineages (sampledAt s b)) :=
    fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab
  refine ⟨fun F => ?_, ?_⟩
  · by_cases hF : N.forestDist s F = 0
    · exact Or.inl hF
    · rw [Net.forestDist_eq] at hF
      exact Or.inr (Net.forestDistOf_single_support N hN (sampledAt s) hE hdisj hF).1.1
  · rw [Net.forestDist_eq]
    exact Net.forestDistOf_single_sum N hN (sampledAt s) hE hdisj

/-- The gene trees of the NMSC on a well-formed network have nonnegative weights. -/
theorem Net.geneTreeDist_nonneg (N : Net X) (hN : N.WellFormed) (s : L → X)
    (G : Finset (Finset L)) : 0 ≤ N.geneTreeDist s G := by
  refine Finset.sum_nonneg fun F _ => ?_
  rcases (gt_forestDist N hN.2 s).1 F with hF | hF
  · rw [hF, zero_mul]
  · exact mul_nonneg (Net.forestDist_nonneg s N hN.1 F) (kingmanAbsorption_nonneg hF G)

/-- The weights of the gene trees of the NMSC on a network with distinct leaves sum to `1`. -/
theorem Net.sum_geneTreeDist (N : Net X) (hN : N.leaves.Nodup) (s : L → X) :
    ∑ G, N.geneTreeDist s G = 1 := by
  obtain ⟨hterm, hsum⟩ := gt_forestDist N hN s
  unfold Net.geneTreeDist
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm, ← hsum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.mul_sum]
  rcases hterm F with hF | hF
  · rw [hF, zero_mul]
  · rw [kingmanAbsorption_sum hF, mul_one]

/-- A quartet concordance factor of a well-formed network is nonnegative. -/
theorem Net.quartetCF_nonneg (N : Net X) (hN : N.WellFormed) (a b c e : X) :
    0 ≤ N.quartetCF a b c e := by
  unfold Net.quartetCF
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact Net.geneTreeDist_nonneg N hN _ G
  · exact le_rfl

/-- A quartet concordance factor of a well-formed network is at most `1`. -/
theorem Net.quartetCF_le_one (N : Net X) (hN : N.WellFormed) (a b c e : X) :
    N.quartetCF a b c e ≤ 1 := by
  unfold Net.quartetCF
  rw [← Net.sum_geneTreeDist N hN.2 ![a, b, c, e]]
  refine Finset.sum_le_sum fun G _ => ?_
  split_ifs
  · exact le_rfl
  · exact Net.geneTreeDist_nonneg N hN _ G

/-! ### Gene trees are hierarchies -/

/-- **The gene trees of the NMSC are hierarchies.** Any two clusters of a gene tree in the support
of the NMSC on a network with distinct leaves are nested or disjoint. -/
theorem geneTreeDist_isHierarchy (N : Net X) (hN : N.leaves.Nodup) (s : L → X)
    {G : Finset (Finset L)} (hG : N.geneTreeDist s G ≠ 0) :
    ∀ C₁ ∈ G, ∀ C₂ ∈ G, C₁ ⊆ C₂ ∨ C₂ ⊆ C₁ ∨ Disjoint C₁ C₂ := by
  have hG' : ∑ F, N.forestDist s F * kingmanAbsorption F G ≠ 0 := hG
  obtain ⟨F, -, hF⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG'
  have hFd := left_ne_zero_of_mul hF
  rw [Net.forestDist_eq] at hFd
  -- the forest at the root of `N` is good
  have hFgood := (Net.forestDistOf_single_support N hN (sampledAt s)
    (fun _ _ => isGood_singletons _) (fun _ _ _ _ hxy => disjoint_lineages_sampledAt s hxy) hFd).1
  exact (kingmanAbsorption_support hFgood (right_ne_zero_of_mul hF)).1.1.2

/-- **Quartet transitivity in a hierarchy.** If any two clusters of `g` are nested or disjoint and
`g` displays `ax|ce` and `xb|ce`, then it displays `ab|ce`. -/
theorem geneTreeDisplays_trans {T : Type*} [DecidableEq T] {g : Finset (Finset T)}
    (hg : ∀ C₁ ∈ g, ∀ C₂ ∈ g, C₁ ⊆ C₂ ∨ C₂ ⊆ C₁ ∨ Disjoint C₁ C₂) {a b x c e : T}
    (h₁ : geneTreeDisplays g a x c e = true) (h₂ : geneTreeDisplays g x b c e = true) :
    geneTreeDisplays g a b c e = true := by
  simp only [geneTreeDisplays, decide_eq_true_eq] at h₁ h₂ ⊢
  obtain ⟨C₁, hC₁, h₁⟩ := h₁
  obtain ⟨C₂, hC₂, h₂⟩ := h₂
  rcases h₁ with ⟨ha₁, hx₁, hc₁, he₁⟩ | ⟨hc₁, he₁, ha₁, hx₁⟩ <;>
    rcases h₂ with ⟨hx₂, hb₂, hc₂, he₂⟩ | ⟨hc₂, he₂, hx₂, hb₂⟩ <;>
    rcases hg C₁ hC₁ C₂ hC₂ with h | h | h
  -- `ax ⊆ C₁` and `xb ⊆ C₂`: both contain `x`, so they are nested
  · exact ⟨C₂, hC₂, Or.inl ⟨h ha₁, hb₂, hc₂, he₂⟩⟩
  · exact ⟨C₁, hC₁, Or.inl ⟨ha₁, h hb₂, hc₁, he₁⟩⟩
  · exact absurd hx₂ (Finset.disjoint_left.1 h hx₁)
  -- `ax ⊆ C₁` and `ce ⊆ C₂`, `x ∉ C₂`, `c ∉ C₁`: they are disjoint
  · exact absurd (h hx₁) hx₂
  · exact absurd (h hc₂) hc₁
  · exact ⟨C₂, hC₂, Or.inr ⟨hc₂, he₂, Finset.disjoint_left.1 h ha₁, hb₂⟩⟩
  -- `ce ⊆ C₁` and `xb ⊆ C₂`, `x ∉ C₁`, `c ∉ C₂`: they are disjoint
  · exact absurd (h hc₁) hc₂
  · exact absurd (h hx₂) hx₁
  · exact ⟨C₁, hC₁, Or.inr ⟨hc₁, he₁, ha₁, Finset.disjoint_right.1 h hb₂⟩⟩
  -- `ce ⊆ C₁` and `ce ⊆ C₂`: both contain `c`, so they are nested
  · exact ⟨C₁, hC₁, Or.inr ⟨hc₁, he₁, ha₁, fun hb => hb₂ (h hb)⟩⟩
  · exact ⟨C₂, hC₂, Or.inr ⟨hc₂, he₂, fun ha => ha₁ (h ha), hb₂⟩⟩
  · exact absurd hc₂ (Finset.disjoint_left.1 h hc₁)

end Phylogenetics
