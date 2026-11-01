module

public import Phylogenetics.NMSC.Level1.Defs
public import Phylogenetics.Coalescent.Outcome
public import Phylogenetics.Coalescent.Relabel
public import Phylogenetics.MSC.Relabel
public import Phylogenetics.MSC.History
/-!
# The network coalescent: forests and kernels

The facts about forests and about Kingman's coalescent (`Phylogenetics.MSC`,
`Phylogenetics.Coalescent`) that the network coalescent needs.

* `Phylogenetics.unionKernel ν`: the kernel that adds an independent forest with distribution `ν`,
  so that `forestUnion μ ν = μ ᵥ* unionKernel ν`.
* Kingman's coalescent: a forest with at most one root does not change; a forest with two
  roots merges them within time `t` with probability `1 - e^{-t}`.
* `Phylogenetics.quartetScore`: the probability of the split `{0, 1} | {2, 3}` as a function of a
  forest of at least three of four lineages, when the forest determines it or when the lineages are
  treated symmetrically afterwards (see `Phylogenetics.NiceKernel.score`). -/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

variable {L : Type*} [Fintype L] [DecidableEq L]





theorem relabel_sampledAt {X : Type*} [DecidableEq X] (σ : Equiv.Perm L) (s : L → X) (x : X) :
    relabelFamily σ (sampledAt s x) = sampledAt (s ∘ σ.symm) x := by
  unfold relabelFamily sampledAt
  rw [image_image]
  ext C
  simp only [mem_image, mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨σ l, by simpa using hl, by simp⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨σ.symm m, hm, by simp⟩


/-- The forest sampled at a taxon is the forest sampled from a singleton set of taxa. -/
theorem sampledAt_eq_sampledForest {X : Type*} [DecidableEq X] (s : L → X) (x : X) :
    sampledAt s x = sampledForest s {x} := by
  simp [sampledAt, sampledForest]

/-! ### Adding an independent forest -/

/-- The kernel that adds an independent random forest with distribution `ν`. -/
def unionKernel (ν : Finset (Finset L) → ℝ) : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => ∑ E, if F ∪ E = G then ν E else 0

theorem forestUnion_eq_vecMul (μ ν : Finset (Finset L) → ℝ) :
    forestUnion μ ν = μ ᵥ* unionKernel ν := by
  ext G
  simp only [forestUnion, vecMul, dotProduct, unionKernel, mul_sum, mul_ite, mul_zero]

theorem forestUnion_comm (μ ν : Finset (Finset L) → ℝ) : forestUnion μ ν = forestUnion ν μ := by
  ext G
  unfold forestUnion
  rw [sum_comm]
  refine sum_congr rfl fun F _ => sum_congr rfl fun F' _ => ?_
  rw [union_comm, mul_comm]

theorem unionKernel_single (E : Finset (Finset L)) (F : Finset (Finset L)) :
    unionKernel (Pi.single E 1) F = Pi.single (F ∪ E) 1 := by
  ext G
  simp only [unionKernel]
  rw [Fintype.sum_eq_single E fun E' hE' => by simp [hE']]
  simp [Pi.single_apply, eq_comm]

theorem forestUnion_single_single (F E : Finset (Finset L)) :
    forestUnion (Pi.single F 1) (Pi.single E 1) = Pi.single (F ∪ E) 1 := by
  rw [forestUnion_eq_vecMul, single_one_vecMul, row_apply', unionKernel_single]

theorem forestUnion_single_empty (μ : Finset (Finset L) → ℝ) :
    forestUnion μ (Pi.single ∅ 1) = μ := by
  rw [forestUnion_comm, forestUnion_eq_vecMul, single_one_vecMul, row_apply']
  ext G
  simp [unionKernel]

theorem forestUnion_add_left (μ μ' ν : Finset (Finset L) → ℝ) :
    forestUnion (μ + μ') ν = forestUnion μ ν + forestUnion μ' ν := by
  ext G
  simp only [forestUnion, Pi.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun F _ => sum_congr rfl fun F' _ => ?_
  split_ifs <;> ring

theorem forestUnion_smul_left (c : ℝ) (μ ν : Finset (Finset L) → ℝ) :
    forestUnion (c • μ) ν = c • forestUnion μ ν := by
  ext G
  simp only [forestUnion, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun F _ => sum_congr rfl fun F' _ => ?_
  split_ifs <;> ring

/-! ### Kingman's coalescent -/



/-- A forest with at most one root does not change. -/
theorem single_vecMul_kingmanTransition {F : Finset (Finset L)} (hF : IsForest F)
    (h : #(roots F) ≤ 1) (t : ℝ) :
    Pi.single F 1 ᵥ* kingmanTransition t = Pi.single F 1 := by
  ext G
  rw [single_one_vecMul, row_apply, kingmanTransition_of_card_roots_le_one hF h t G, Pi.single_apply]

/-- A forest with two roots `A ≠ B` keeps them apart for a time `t` with probability `e^{-t}`, and
otherwise merges them. -/
theorem single_vecMul_kingmanTransition_two {F : Finset (Finset L)} (hF : IsForest F)
    {A B : Finset L} (hAB : A ≠ B) (hroots : roots F = {A, B}) (t : ℝ) :
    Pi.single F 1 ᵥ* kingmanTransition t =
      Real.exp (-t) • Pi.single F 1 + (1 - Real.exp (-t)) • Pi.single (insert (A ∪ B) F) 1 := by
  have hroots' : roots F = {A, B} := hroots
  have hk : #(roots F) = 2 := by rw [hroots', card_pair hAB]
  have hA : A ∈ roots F := by rw [hroots']; exact mem_insert_self _ _
  have hB : B ∈ roots F := by rw [hroots']; exact mem_insert_of_mem (mem_singleton_self _)
  have hmerges : merges F = {insert (A ∪ B) F} := by
    ext G
    rw [mem_merges, mem_singleton]
    constructor
    · rintro ⟨C, hC, D, hD, hCD, rfl⟩
      rw [hroots', mem_insert, mem_singleton] at hC hD
      rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
      · exact absurd rfl hCD
      · rfl
      · rw [union_comm]
      · exact absurd rfl hCD
    · rintro rfl
      exact ⟨A, hA, B, hB, hAB, rfl⟩
  have hk' : #(roots (insert (A ∪ B) F)) = 1 := by
    have := hF.card_roots_merge hA hB hAB
    omega
  have h21 := (deathProb_small t).2.2.1
  have h22 := (deathProb_small t).2.2.2.1
  ext G
  rw [single_one_vecMul, row_apply, kingmanTransition_apply hF,
    hk]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  obtain hj | hj | hj | hj : #(roots G) = 0 ∨ #(roots G) = 1 ∨
      #(roots G) = 2 ∨ 3 ≤ #(roots G) := by omega
  · have h1 : G ≠ F := by rintro rfl; omega
    have h2 : G ≠ insert (A ∪ B) F := by rintro rfl; omega
    rw [hj, deathProb_zero_right (by norm_num), ite_eq_right h1, ite_eq_right h2]
    ring
  · have h1 : G ≠ F := by rintro rfl; omega
    rw [hj, h21, ite_eq_right h1, show 2 - 1 = 1 from rfl, pow_one,
      jumpMatrix_apply_of_isForest (by omega), hmerges, hk]
    by_cases h2 : G = insert (A ∪ B) F
    · rw [ite_eq_left (mem_singleton.2 h2), ite_eq_left h2]
      simp
    · rw [ite_eq_right (fun h => h2 (mem_singleton.1 h)), ite_eq_right h2]
      ring
  · have h2 : G ≠ insert (A ∪ B) F := by rintro rfl; omega
    rw [hj, h22, ite_eq_right h2, Nat.sub_self, pow_zero, one_apply]
    by_cases hGF : G = F
    · subst hGF
      simp
    · rw [ite_eq_right (Ne.symm hGF), ite_eq_right hGF]
      ring
  · have h1 : G ≠ F := by rintro rfl; omega
    have h2 : G ≠ insert (A ∪ B) F := by rintro rfl; omega
    rw [deathProb_eq_zero_of_lt (by omega), zero_mul, ite_eq_right h1, ite_eq_right h2]
    ring

theorem kingmanTransition_add_vecMul (μ : Finset (Finset L) → ℝ) (s t : ℝ) :
    μ ᵥ* kingmanTransition s ᵥ* kingmanTransition t = μ ᵥ* kingmanTransition (s + t) := by
  rw [vecMul_vecMul]
  congr 1
  exact (kingmanTransition_add s t).symm


/-! ### The score of a forest of four lineages -/

/-- The probability of the split `{0, 1} | {2, 3}` as a function of a good forest `F` of at least
three of the lineages `0, 1, 2, 3`: `1` if `F` has the cluster `{0, 1}` or `{2, 3}`, `0` if it has
another cluster of two lineages, and `1/3` if all its clusters are singletons (from then on the
lineages are treated symmetrically; see `Phylogenetics.NiceKernel.score`). -/
def quartetScore (F : Finset (Finset (Fin 4))) : ℝ :=
  if ({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F then 1
  else if ∃ C ∈ F, #C = 2 then 0 else 1 / 3

/-- A good forest with a cluster of three lineages has a cluster of two lineages. -/
private theorem np_exists_card_two_of_three {G : Finset (Finset (Fin 4))} (hG : IsGoodForest G)
    {D : Finset (Fin 4)} (hD : D ∈ G) (hD3 : #D = 3) : ∃ C ∈ G, #C = 2 := by
  obtain ⟨E, hE, E', hE', hEE', hEU⟩ := hG.2 D hD (by omega)
  have hc := card_union_of_disjoint hEE'
  rw [hEU] at hc
  have := (hG.1.1 E hE).card_pos
  have := (hG.1.1 E' hE').card_pos
  by_cases h : #E = 2
  · exact ⟨E, hE, h⟩
  · exact ⟨E', hE', by omega⟩

/-- A complete good tree on the four lineages has a cluster of two lineages. -/
private theorem np_exists_card_two {G : Finset (Finset (Fin 4))} (hG : IsGoodForest G)
    (huniv : (univ : Finset (Fin 4)) ∈ G) : ∃ C ∈ G, #C = 2 := by
  obtain ⟨B, hB, C, hC, hBC, hU⟩ := hG.2 univ huniv (by simp)
  have hc := card_union_of_disjoint hBC
  rw [hU, card_univ, Fintype.card_fin] at hc
  have := (hG.1.1 B hB).card_pos
  have := (hG.1.1 C hC).card_pos
  by_cases h2 : #B = 2
  · exact ⟨B, hB, h2⟩
  by_cases h3 : #B = 3
  · exact np_exists_card_two_of_three hG hB h3
  · exact np_exists_card_two_of_three hG hC (by omega)

/-- On a complete good tree on the four lineages, the score is the indicator of the split
`{0, 1} | {2, 3}` in the unrooted tree. -/
theorem quartetScore_eq_of_univ_mem {G : Finset (Finset (Fin 4))} (hG : IsGoodForest G)
    (huniv : (univ : Finset (Fin 4)) ∈ G) :
    quartetScore G = if ({0, 1} : Finset (Fin 4)) ∈ unroot G then 1 else 0 := by
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ unroot G ↔
      ({0, 1} : Finset (Fin 4)) ∈ G ∨ ({2, 3} : Finset (Fin 4)) ∈ G := by
    have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    have h1 : ({0, 1} : Finset (Fin 4)) ≠ univ := by decide
    have h2 : ({2, 3} : Finset (Fin 4)) ≠ univ := by decide
    rw [mem_unroot, hc]
    simp only [ne_eq, h1, h2, not_false_eq_true, and_true]
  unfold quartetScore
  rw [if_congr hmem rfl rfl]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (np_exists_card_two hG huniv) h2

end Phylogenetics
