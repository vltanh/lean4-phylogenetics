module

public import Phylogenetics.Defs
public import Phylogenetics.Coalescent.Outcome
public import Phylogenetics.MSC.Relabel
public import Phylogenetics.MSC.History
/-!
# The network coalescent: forests and kernels

The facts about forests and about Kingman's coalescent (`Phylogenetics.MSC`,
`Phylogenetics.Coalescent`) that the network coalescent needs.

* Good forests (`Phylogenetics.IsGood`): forests in which every cluster with at least two lineages
  is the union of two disjoint clusters; Kingman's coalescent, unions of forests on disjoint
  lineages and the parts of a forest below some of its roots preserve them.
* `Phylogenetics.unionKernel ν`: the kernel that adds an independent forest with distribution `ν`,
  so that `forestUnion μ ν = μ ᵥ* unionKernel ν`.
* Kingman's coalescent: rows of `kingmanTransition t` and `kingmanAbsorption` are probability
  distributions on good forests containing the starting forest; both are invariant under
  relabelling the lineages; a forest with at most one root does not change; a forest with two
  roots merges them within time `t` with probability `1 - e^{-t}`.
* `Phylogenetics.quartetScore`: the probability of the split `{0, 1} | {2, 3}` as a function of a
  forest of at least three of four lineages, when the forest determines it or when the lineages are
  treated symmetrically afterwards (see `Phylogenetics.NiceKernel.score`). -/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

variable {L : Type*} [Fintype L] [DecidableEq L]

/-! ### Good forests -/

/-- A good forest: a forest (nonempty clusters, any two nested or disjoint) in which every
cluster with at least two lineages is the union of two disjoint clusters. -/
def IsGood (F : Finset (Finset L)) : Prop :=
  IsForest F ∧ model_IsBinaryForest F

omit [Fintype L] in
theorem isGood_empty : IsGood (∅ : Finset (Finset L)) :=
  ⟨isForest_empty, fun A hA => absurd hA (notMem_empty A)⟩

omit [Fintype L] in
/-- The forest of the singletons of a set of lineages is good. -/
theorem isGood_singletons (T : Finset L) : IsGood (T.image fun l => ({l} : Finset L)) := by
  refine ⟨?_, fun A hA h2 => ?_⟩
  · simpa using (isForest_empty (L := L)).union_image_singleton T
  · obtain ⟨l, -, rfl⟩ := mem_image.1 hA
    simp at h2

omit [Fintype L] in
theorem lineages_singletons (T : Finset L) :
    lineages (T.image fun l => ({l} : Finset L)) = T :=
  lineages_image_singleton T

omit [Fintype L] in
theorem IsGood.union {F G : Finset (Finset L)} (hF : IsGood F) (hG : IsGood G)
    (h : Disjoint (lineages F) (lineages G)) : IsGood (F ∪ G) := by
  refine ⟨hF.1.union_of_disjoint hG.1 h, fun A hA h2 => ?_⟩
  rcases mem_union.1 hA with hA | hA
  · obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA h2
    exact ⟨B, mem_union_left _ hB, C, mem_union_left _ hC, hBC, rfl⟩
  · obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hG.2 A hA h2
    exact ⟨B, mem_union_right _ hB, C, mem_union_right _ hC, hBC, rfl⟩

omit [Fintype L] in
theorem mem_forestBelow {F A : Finset (Finset L)} {B : Finset L} :
    B ∈ forestBelow F A ↔ B ∈ F ∧ ∃ C ∈ A, B ⊆ C :=
  mem_filter

omit [Fintype L] in
/-- The part of a good forest below the members of any family `A` of clusters is good. -/
theorem isGood_forestBelow {F A : Finset (Finset L)} (hF : IsGood F) :
    IsGood (forestBelow F A) := by
  refine ⟨hF.1.subset (filter_subset _ _), fun B hB h2 => ?_⟩
  obtain ⟨hBF, C, hC, hBC⟩ := mem_forestBelow.1 hB
  obtain ⟨D, hD, E, hE, hDE, rfl⟩ := hF.2 B hBF h2
  exact ⟨D, mem_forestBelow.2 ⟨hD, C, hC, subset_union_left.trans hBC⟩, E,
    mem_forestBelow.2 ⟨hE, C, hC, subset_union_right.trans hBC⟩, hDE, rfl⟩

/-- The lineages of the part of a forest below some of its roots: the union of those roots. -/
theorem lineages_forestBelow {F A : Finset (Finset L)} (hA : A ⊆ roots F) :
    lineages (forestBelow F A) = A.sup id := by
  ext l
  rw [mem_lineages, Finset.mem_sup]
  constructor
  · rintro ⟨B, hB, hl⟩
    obtain ⟨-, C, hC, hBC⟩ := mem_forestBelow.1 hB
    exact ⟨C, hC, hBC hl⟩
  · rintro ⟨C, hC, hl⟩
    exact ⟨C, mem_forestBelow.2 ⟨roots_subset F (hA hC), C, hC, subset_rfl⟩, hl⟩

/-- A good forest is the union of its parts below two complementary sets of roots, and these
parts have disjoint lineages. -/
theorem forestBelow_union {F A : Finset (Finset L)} (hF : IsGood F) (hA : A ⊆ roots F) :
    forestBelow F A ∪ forestBelow F (roots F \ A) = F ∧
      Disjoint (lineages (forestBelow F A))
        (lineages (forestBelow F (roots F \ A))) := by
  refine ⟨Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _)) fun B hB => ?_,
    ?_⟩
  · obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    by_cases hRA : R ∈ A
    · exact mem_union_left _ (mem_forestBelow.2 ⟨hB, R, hRA, hBR⟩)
    · exact mem_union_right _ (mem_forestBelow.2 ⟨hB, R, mem_sdiff.2 ⟨hR, hRA⟩, hBR⟩)
  · rw [lineages_forestBelow hA, lineages_forestBelow sdiff_subset, Finset.disjoint_sup_left]
    intro C hC
    rw [Finset.disjoint_sup_right]
    intro D hD
    have hCD : C ≠ D := fun h => (mem_sdiff.1 hD).2 (h ▸ hC)
    exact hF.1.disjoint_of_mem_roots (hA hC) (mem_sdiff.1 hD).1 hCD

/-! ### Relabelling the lineages -/

omit [Fintype L] in
theorem IsGood.relabel {F : Finset (Finset L)} (hF : IsGood F) (σ : Equiv.Perm L) :
    IsGood (relabelFamily σ F) := by
  unfold relabelFamily
  refine ⟨⟨fun A hA => ?_, fun A hA B hB => ?_⟩, fun A hA h2 => ?_⟩
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    exact map_nonempty.2 (hF.1.1 A hA')
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    obtain ⟨B, hB', rfl⟩ := mem_image.1 hB
    rcases hF.1.2 A hA' B hB' with h | h | h
    · exact Or.inl (map_subset_map.2 h)
    · exact Or.inr (Or.inl (map_subset_map.2 h))
    · exact Or.inr (Or.inr ((disjoint_map _).2 h))
  · obtain ⟨A, hA', rfl⟩ := mem_image.1 hA
    rw [card_map] at h2
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hF.2 A hA' h2
    exact ⟨B.map σ.toEmbedding, mem_image_of_mem _ hB, C.map σ.toEmbedding,
      mem_image_of_mem _ hC, (disjoint_map _).2 hBC, (map_union _ _).symm⟩

omit [Fintype L] in
theorem lineages_relabel (σ : Equiv.Perm L) (F : Finset (Finset L)) :
    lineages (relabelFamily σ F) = (lineages F).map σ.toEmbedding := by
  ext l
  rw [mem_map_equiv, mem_lineages, mem_lineages]
  constructor
  · rintro ⟨B, hB, hl⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact ⟨A, hA, mem_map_equiv.1 hl⟩
  · rintro ⟨A, hA, hl⟩
    exact ⟨A.map σ.toEmbedding, mem_image_of_mem _ hA, mem_map_equiv.2 hl⟩

omit [Fintype L] in
theorem relabel_union (σ : Equiv.Perm L) (F G : Finset (Finset L)) :
    relabelFamily σ (F ∪ G) = relabelFamily σ F ∪ relabelFamily σ G :=
  relabelFamily_union σ F G

theorem relabel_roots (σ : Equiv.Perm L) (F : Finset (Finset L)) :
    roots (relabelFamily σ F) = relabelFamily σ (roots F) :=
  roots_relabelFamily σ F

omit [Fintype L] in
theorem relabel_forestBelow (σ : Equiv.Perm L) (F A : Finset (Finset L)) :
    relabelFamily σ (forestBelow F A) =
      forestBelow (relabelFamily σ F) (relabelFamily σ A) := by
  unfold relabelFamily forestBelow
  rw [filter_image]
  congr 1
  refine filter_congr fun B _ => ?_
  rw [exists_mem_image]
  simp only [map_subset_map]

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

omit [Fintype L] in
/-- A relabelling that fixes every lineage of a forest fixes the forest. -/
theorem relabel_eq_self {σ : Equiv.Perm L} {F : Finset (Finset L)}
    (h : ∀ l ∈ lineages F, σ l = l) : relabelFamily σ F = F := by
  have hA : ∀ A ∈ F, A.map σ.toEmbedding = A := by
    intro A hA
    rw [map_eq_image]
    conv_rhs => rw [← image_id (s := A)]
    exact image_congr fun l hl => h l (subset_lineages hA hl)
  unfold relabelFamily
  conv_rhs => rw [← image_id (s := F)]
  exact image_congr fun A hA' => hA A hA'

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

theorem kingmanTransition_row_sum {F : Finset (Finset L)} (hF : IsForest F) (t : ℝ) :
    ∑ G, kingmanTransition t F G = 1 :=
  kingmanTransition_sum hF t

/-- Kingman's coalescent from a good forest reaches only good forests that contain it and have
the same lineages. -/
theorem kingmanTransition_support_isGood {F G : Finset (Finset L)} (hF : IsGood F) {t : ℝ}
    (h : kingmanTransition t F G ≠ 0) :
    IsGood G ∧ F ⊆ G ∧ lineages G = lineages F := by
  obtain ⟨h1, h2, h3, -⟩ := kingmanTransition_support hF.1 h
  rw [kingmanTransition_apply hF.1] at h
  exact ⟨⟨h1, model_isBinaryForest_of_jumpMatrix_pow hF.1 hF.2 (right_ne_zero_of_mul h)⟩,
    h2, h3⟩

theorem kingmanTransition_relabel (σ : Equiv.Perm L) (t : ℝ) (F G : Finset (Finset L)) :
    kingmanTransition t (relabelFamily σ F) (relabelFamily σ G) =
      kingmanTransition t F G :=
  kingmanTransition_relabelFamily σ t F G

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

theorem kingmanAbsorption_row_sum {F : Finset (Finset L)} (hF : IsForest F) :
    ∑ G, kingmanAbsorption F G = 1 :=
  kingmanAbsorption_sum hF

/-- Above the root, the lineages of a nonempty good forest coalesce into one tree. -/
theorem kingmanAbsorption_support {F G : Finset (Finset L)} (hF : IsGood F)
    (h : kingmanAbsorption F G ≠ 0) :
    IsGood G ∧ F ⊆ G ∧ lineages G = lineages F ∧ (F.Nonempty → #(roots G) = 1) := by
  rw [kingmanAbsorption_apply hF.1] at h
  by_cases h0 : #(roots F) = 0
  · rw [ite_eq_left h0] at h
    have hGF : G = F := by
      by_contra hne
      exact h (ite_eq_right hne)
    subst hGF
    exact ⟨hF, subset_rfl, rfl, fun hne => absurd (card_roots_eq_zero_iff.1 h0) hne.ne_empty⟩
  rw [ite_eq_right h0] at h
  by_cases h1 : #(roots G) = 1
  · rw [ite_eq_left h1] at h
    obtain ⟨h1', h2, h3, -⟩ := jumpMatrix_pow_support hF.1 h
    exact ⟨⟨h1', model_isBinaryForest_of_jumpMatrix_pow hF.1 hF.2 h⟩, h2, h3, fun _ => h1⟩
  · rw [ite_eq_right h1] at h
    exact absurd rfl h

theorem kingmanAbsorption_relabel (σ : Equiv.Perm L) (F G : Finset (Finset L)) :
    kingmanAbsorption (relabelFamily σ F) (relabelFamily σ G) =
      kingmanAbsorption F G :=
  kingmanAbsorption_relabelFamily σ F G

/-! ### The score of a forest of four lineages -/

/-- The probability of the split `{0, 1} | {2, 3}` as a function of a good forest `F` of at least
three of the lineages `0, 1, 2, 3`: `1` if `F` has the cluster `{0, 1}` or `{2, 3}`, `0` if it has
another cluster of two lineages, and `1/3` if all its clusters are singletons (from then on the
lineages are treated symmetrically; see `Phylogenetics.NiceKernel.score`). -/
def quartetScore (F : Finset (Finset (Fin 4))) : ℝ :=
  if ({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F then 1
  else if ∃ C ∈ F, #C = 2 then 0 else 1 / 3

/-- A good forest with a cluster of three lineages has a cluster of two lineages. -/
private theorem np_exists_card_two_of_three {G : Finset (Finset (Fin 4))} (hG : IsGood G)
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
private theorem np_exists_card_two {G : Finset (Finset (Fin 4))} (hG : IsGood G)
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
theorem quartetScore_eq_of_univ_mem {G : Finset (Finset (Fin 4))} (hG : IsGood G)
    (huniv : (univ : Finset (Fin 4)) ∈ G) :
    quartetScore G = if ({0, 1} : Finset (Fin 4)) ∈ unroot G then 1 else 0 := by
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ unroot G ↔
      ({0, 1} : Finset (Fin 4)) ∈ G ∨ ({2, 3} : Finset (Fin 4)) ∈ G := by
    have hc : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    have h1 : ({0, 1} : Finset (Fin 4)) ≠ univ := by decide
    have h2 : ({2, 3} : Finset (Fin 4)) ≠ univ := by decide
    rw [absorb_mem_unroot, hc]
    simp only [ne_eq, h1, h2, not_false_eq_true, and_true]
  unfold quartetScore
  rw [if_congr hmem rfl rfl]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (np_exists_card_two hG huniv) h2

end Phylogenetics
