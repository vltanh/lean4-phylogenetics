module

public import Phylogenetics.NMSC.Level1.Process
public import Phylogenetics.MSC.Marginal
/-!
# Sampling consistency of the network coalescent

Dropping lineages commutes with the network multispecies coalescent: the forest of a subset of the
lineages is distributed as the coalescent of that subset (`Phylogenetics.Net.forestDist_restrict`),
and so is the gene tree (`Phylogenetics.Net.geneTreeDist_restrict`). The subset is given by an
embedding `e : L' ↪ L` of lineage types, and a forest on `L` restricts to `L'` by keeping the
nonempty traces of its clusters (`Phylogenetics.restrictForest`).

This is the consistency of Kingman's coalescent (`Phylogenetics.kingmanTransition_lump`,
`Phylogenetics.kingmanAbsorption_lump`), carried through the network: a union of
independent forests restricts to the union of the restrictions, and at a hybrid node the lineages
that do not meet the subset also choose a side, but their choices sum out, since the inheritance
probabilities `γ` and `1 - γ` add up to `1`.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u

variable {X : Type u} [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L] {L' : Type*}
  [Fintype L'] [DecidableEq L']

/-! ### Pushing distributions forward along the restriction -/

/-- The pushforward of a distribution on forests on `L` along the restriction to `L'`. -/
private def nr_push (e : L' ↪ L) (μ : Finset (Finset L) → ℝ) (G' : Finset (Finset L')) : ℝ :=
  ∑ G, if restrictForest e G = G' then μ G else 0

/-- Change of variables along the restriction. -/
private theorem nr_sum_mul_push (e : L' ↪ L) (μ : Finset (Finset L) → ℝ)
    (f : Finset (Finset L') → ℝ) :
    ∑ F, μ F * f (restrictForest e F) = ∑ F', nr_push e μ F' * f F' := by
  simp only [nr_push, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_ite_eq]
  simp

/-- A kernel `K` on forests on `L` lumps to `K'` on forests on `L'` (on the support of `μ`):
the pushforward of `μ ᵥ* K` is `(pushforward of μ) ᵥ* K'`. -/
private theorem nr_push_vecMul (e : L' ↪ L) {μ : Finset (Finset L) → ℝ}
    {K : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ}
    {K' : Matrix (Finset (Finset L')) (Finset (Finset L')) ℝ}
    (h : ∀ F, μ F ≠ 0 → ∀ G', nr_push e (K F) G' = K' (restrictForest e F) G') :
    nr_push e (μ ᵥ* K) = nr_push e μ ᵥ* K' := by
  funext G'
  have h1 : nr_push e (μ ᵥ* K) G' = ∑ F, μ F * nr_push e (K F) G' := by
    simp only [nr_push, vecMul, dotProduct, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    refine sum_congr rfl fun G _ => ?_
    split_ifs <;> simp
  have h2 : ∀ F, μ F * nr_push e (K F) G' = μ F * K' (restrictForest e F) G' := by
    intro F
    by_cases hF : μ F = 0
    · rw [hF, zero_mul, zero_mul]
    · rw [h F hF G']
  rw [h1, sum_congr rfl fun F _ => h2 F, nr_sum_mul_push e μ fun F' => K' F' G']
  rfl

private theorem nr_push_kT (e : L' ↪ L) {μ : Finset (Finset L) → ℝ}
    (hμ : ∀ F, μ F ≠ 0 → IsForest F) (t : ℝ) :
    nr_push e (μ ᵥ* kingmanTransition t) = nr_push e μ ᵥ* kingmanTransition t :=
  nr_push_vecMul e fun F hF G' => kingmanTransition_lump (hμ F hF) e t G'

private theorem nr_push_unionKernel (e : L' ↪ L) (ν : Finset (Finset L) → ℝ)
    (F : Finset (Finset L)) (G' : Finset (Finset L')) :
    nr_push e (unionKernel ν F) G' =
      unionKernel (nr_push e ν) (restrictForest e F) G' := by
  have h1 : nr_push e (unionKernel ν F) G' = ∑ E, ν E *
      (if restrictForest e F ∪ restrictForest e E = G' then 1 else 0) := by
    simp only [nr_push, unionKernel]
    have h : ∀ G, (if restrictForest e G = G' then
        ∑ E, (if F ∪ E = G then ν E else 0) else 0) =
        ∑ E, if F ∪ E = G then (if restrictForest e G = G' then ν E else 0) else 0 := by
      intro G
      split_ifs <;> simp
    simp_rw [h]
    rw [sum_comm]
    refine sum_congr rfl fun E _ => ?_
    rw [sum_ite_eq]
    simp [restrictForest_union]
  rw [h1, nr_sum_mul_push e ν fun E' =>
    if restrictForest e F ∪ E' = G' then (1 : ℝ) else 0]
  simp only [unionKernel, mul_ite, mul_one, mul_zero]

private theorem nr_push_forestUnion (e : L' ↪ L) (μ ν : Finset (Finset L) → ℝ) :
    nr_push e (forestUnion μ ν) = forestUnion (nr_push e μ) (nr_push e ν) := by
  rw [forestUnion_eq_vecMul, forestUnion_eq_vecMul]
  exact nr_push_vecMul e fun F _ G' => nr_push_unionKernel e ν F G'

private theorem nr_push_sum (e : L' ↪ L) {ι : Type*} (P : Finset ι) (c : ι → ℝ)
    (φ : ι → Finset (Finset L) → ℝ) (G' : Finset (Finset L')) :
    nr_push e (fun G => ∑ A ∈ P, c A * φ A G) G' = ∑ A ∈ P, c A * nr_push e (φ A) G' := by
  simp only [nr_push, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun G _ => ?_
  split_ifs <;> simp

/-! ### Restricting the parts of a forest below some of its roots -/

/-- The trace of a cluster on the lineages `L'`. -/
private def nr_tr (e : L' ↪ L) (C : Finset L) : Finset L' :=
  univ.filter fun l => e l ∈ C

omit [Fintype L] in
private theorem nr_mem_restrict (e : L' ↪ L) {F : Finset (Finset L)} {D : Finset L'} :
    D ∈ restrictForest e F ↔ ∃ A ∈ F, (∃ l, e l ∈ A) ∧ nr_tr e A = D := by
  unfold restrictForest nr_tr
  simp only [mem_image, mem_filter, and_assoc]

omit [Fintype L] [DecidableEq L'] in
private theorem nr_tr_mono (e : L' ↪ L) {A B : Finset L} (h : A ⊆ B) : nr_tr e A ⊆ nr_tr e B :=
  fun l hl => mem_filter.2 ⟨mem_univ l, h (mem_filter.1 hl).2⟩

omit [Fintype L] [DecidableEq L'] in
private theorem nr_mem_tr (e : L' ↪ L) {A : Finset L} {l : L'} : l ∈ nr_tr e A ↔ e l ∈ A := by
  simp [nr_tr]

/-- The roots of the restriction of a forest are the traces of its roots meeting the range. -/
private theorem nr_mem_roots_restrict {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {D : Finset L'} :
    D ∈ roots (restrictForest e F) ↔
      ∃ A ∈ roots F, (∃ l, e l ∈ A) ∧ nr_tr e A = D := by
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := mem_roots.1 hD
    obtain ⟨A, hA, ⟨l, hl⟩, rfl⟩ := (nr_mem_restrict e).1 hDF
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    have hRm : ∃ l, e l ∈ R := ⟨l, hAR hl⟩
    exact ⟨R, hR, hRm, hmax _ ((nr_mem_restrict e).2 ⟨R, roots_subset F hR, hRm, rfl⟩)
      (nr_tr_mono e hAR)⟩
  · rintro ⟨A, hA, ⟨l, hl⟩, rfl⟩
    refine mem_roots.2 ⟨(nr_mem_restrict e).2 ⟨A, roots_subset F hA, ⟨l, hl⟩, rfl⟩,
      fun D hD hAD => ?_⟩
    obtain ⟨B, hB, -, rfl⟩ := (nr_mem_restrict e).1 hD
    obtain ⟨R, hR, hBR⟩ := exists_mem_roots_subset hB
    have hlB : e l ∈ B := (nr_mem_tr e).1 (hAD ((nr_mem_tr e).2 hl))
    have hAR : A = R := hF.eq_of_mem_roots_of_mem hA hR hl (hBR hlB)
    subst hAR
    exact subset_antisymm (nr_tr_mono e hBR) hAD

private theorem nr_roots_restrict {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) :
    roots (restrictForest e F) =
      ((roots F).filter fun C => ∃ l, e l ∈ C).image (nr_tr e) := by
  ext D
  rw [nr_mem_roots_restrict hF e, mem_image]
  simp only [mem_filter, and_assoc]

omit [DecidableEq L'] in
/-- The trace is injective on the roots meeting the range. -/
private theorem nr_tr_injOn {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L) :
    Set.InjOn (nr_tr e) ↑((roots F).filter fun C => ∃ l, e l ∈ C) := by
  intro A hA B hB h
  obtain ⟨hAr, l, hl⟩ := mem_filter.1 (mem_coe.1 hA)
  have hBr := (mem_filter.1 (mem_coe.1 hB)).1
  have hlB : e l ∈ B := (nr_mem_tr e).1 (h ▸ (nr_mem_tr e).2 hl)
  exact hF.eq_of_mem_roots_of_mem hAr hBr hl hlB

/-- The restriction of the part of a forest below some of its roots `B` is the part of the
restriction below the traces `B'` of the roots of `B` meeting the range. -/
private theorem nr_restrict_forestBelow {F : Finset (Finset L)} (hF : IsForest F)
    (e : L' ↪ L) {B : Finset (Finset L)} (hB : B ⊆ roots F) {B' : Finset (Finset L')}
    (hB' : B' ⊆ roots (restrictForest e F))
    (h : ∀ C ∈ roots F, (∃ l, e l ∈ C) → (nr_tr e C ∈ B' ↔ C ∈ B)) :
    restrictForest e (forestBelow F B) = forestBelow (restrictForest e F) B' := by
  ext D
  rw [mem_forestBelow, nr_mem_restrict, nr_mem_restrict]
  constructor
  · rintro ⟨E, hE, ⟨l, hl⟩, rfl⟩
    obtain ⟨hEF, C, hCB, hEC⟩ := mem_forestBelow.1 hE
    exact ⟨⟨E, hEF, ⟨l, hl⟩, rfl⟩, _, (h C (hB hCB) ⟨l, hEC hl⟩).2 hCB, nr_tr_mono e hEC⟩
  · rintro ⟨⟨E, hEF, ⟨l, hl⟩, rfl⟩, C', hC', hEC'⟩
    obtain ⟨C, hC, hCm, rfl⟩ := (nr_mem_roots_restrict hF e).1 (hB' hC')
    have hCB : C ∈ B := (h C hC hCm).1 hC'
    obtain ⟨R, hR, hER⟩ := exists_mem_roots_subset hEF
    have hlC : e l ∈ C := (nr_mem_tr e).1 (hEC' ((nr_mem_tr e).2 hl))
    have hRC : R = C := hF.eq_of_mem_roots_of_mem hR hC (hER hl) hlC
    exact ⟨E, mem_forestBelow.2 ⟨hEF, C, hCB, hRC ▸ hER⟩, ⟨l, hl⟩, rfl⟩

/-! ### Summing out the choices of the roots outside the subset -/

private theorem nr_sum_powerset_insert {α : Type*} [DecidableEq α] (γ : ℝ) {x : α}
    {R : Finset α} (hx : x ∉ R) (g : Finset α → ℝ) :
    ∑ A ∈ (insert x R).powerset, γ ^ #A * (1 - γ) ^ #(insert x R \ A) * g A =
      (1 - γ) * ∑ A ∈ R.powerset, γ ^ #A * (1 - γ) ^ #(R \ A) * g A +
        γ * ∑ A ∈ R.powerset, γ ^ #A * (1 - γ) ^ #(R \ A) * g (insert x A) := by
  rw [sum_powerset_insert hx, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun A hA => ?_
    have hxA : x ∉ A := fun h => hx (mem_powerset.1 hA h)
    rw [insert_sdiff_of_notMem _ hxA, card_insert_of_notMem fun h => hx (sdiff_subset h)]
    ring
  · refine sum_congr rfl fun A hA => ?_
    have hxA : x ∉ A := fun h => hx (mem_powerset.1 hA h)
    rw [card_insert_of_notMem hxA, insert_sdiff_insert, sdiff_insert_of_notMem hx]
    ring

/-- The choices of the elements outside `p` sum out. -/
private theorem nr_sum_powerset_filter {α : Type*} [DecidableEq α] (γ : ℝ) (p : α → Prop)
    [DecidablePred p] (R : Finset α) (f : Finset α → ℝ) :
    ∑ A ∈ R.powerset, γ ^ #A * (1 - γ) ^ #(R \ A) * f (A.filter p) =
      ∑ A ∈ (R.filter p).powerset, γ ^ #A * (1 - γ) ^ #(R.filter p \ A) * f A := by
  induction R using Finset.induction_on generalizing f with
  | empty => simp
  | insert x R hx ih =>
    rw [nr_sum_powerset_insert γ hx]
    by_cases hp : p x
    · rw [filter_insert, ite_eq_left hp, nr_sum_powerset_insert γ fun h => hx (mem_filter.1 h).1]
      simp_rw [filter_insert, ite_eq_left hp]
      rw [ih f, ih fun A => f (insert x A)]
    · rw [filter_insert, ite_eq_right hp]
      simp_rw [filter_insert, ite_eq_right hp]
      rw [ih f, ← add_mul, sub_add_cancel, one_mul]

/-- Reindexing the subsets along a map injective on the ground set. -/
private theorem nr_sum_powerset_image {α β : Type*} [DecidableEq α] [DecidableEq β] (γ : ℝ)
    (τ : α → β) {M : Finset α} (hτ : Set.InjOn τ M) (f : Finset β → ℝ) :
    ∑ A ∈ M.powerset, γ ^ #A * (1 - γ) ^ #(M \ A) * f (A.image τ) =
      ∑ A' ∈ (M.image τ).powerset, γ ^ #A' * (1 - γ) ^ #(M.image τ \ A') * f A' := by
  refine sum_bij (fun A _ => A.image τ)
    (fun A hA => mem_powerset.2 (image_subset_image (mem_powerset.1 hA)))
    (fun A₁ hA₁ A₂ hA₂ h => ?_) (fun A' hA' => ?_) (fun A hA => ?_)
  · have h' : τ '' (A₁ : Set α) = τ '' (A₂ : Set α) := by
      rw [← coe_image, ← coe_image, h]
    exact coe_injective ((hτ.image_eq_image_iff (coe_subset.2 (mem_powerset.1 hA₁))
      (coe_subset.2 (mem_powerset.1 hA₂))).1 h')
  · obtain ⟨A, hA, rfl⟩ := subset_image_iff.1 (mem_powerset.1 hA')
    exact ⟨A, mem_powerset.2 hA, rfl⟩
  · have hAM := mem_powerset.1 hA
    rw [card_image_of_injOn (hτ.mono (coe_subset.2 hAM)), ← image_sdiff_of_injOn hτ hAM,
      card_image_of_injOn (hτ.mono (coe_subset.2 sdiff_subset))]

/-- The hybrid split commutes with the restriction: the roots not meeting the range also choose
a side, but their choices sum out. -/
private theorem nr_sum_split {F : Finset (Finset L)} (hF : IsForest F) (e : L' ↪ L)
    (γ : ℝ) (Φ : Finset (Finset L') → Finset (Finset L') → ℝ) :
    ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
        Φ (restrictForest e (forestBelow F A))
          (restrictForest e (forestBelow F (roots F \ A))) =
      ∑ A' ∈ (roots (restrictForest e F)).powerset,
        γ ^ #A' * (1 - γ) ^ #(roots (restrictForest e F) \ A') *
          Φ (forestBelow (restrictForest e F) A')
            (forestBelow (restrictForest e F) (roots (restrictForest e F) \ A')) := by
  have hR' := nr_roots_restrict hF e
  have hinj := nr_tr_injOn hF e
  set M := (roots F).filter fun C => ∃ l, e l ∈ C with hM
  have key : ∀ A ∈ (roots F).powerset,
      γ ^ #A * (1 - γ) ^ #(roots F \ A) * Φ (restrictForest e (forestBelow F A))
        (restrictForest e (forestBelow F (roots F \ A))) =
      γ ^ #A * (1 - γ) ^ #(roots F \ A) *
        Φ (forestBelow (restrictForest e F)
            ((A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e)))
          (forestBelow (restrictForest e F)
            (M.image (nr_tr e) \ (A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e))) := by
    intro A hA
    have hAR := mem_powerset.1 hA
    have hsub : (A.filter fun C => ∃ l, e l ∈ C) ⊆ M := filter_subset_filter _ hAR
    have hiff : ∀ C ∈ roots F, (∃ l, e l ∈ C) →
        (nr_tr e C ∈ (A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e) ↔ C ∈ A) := by
      intro C hC hCm
      constructor
      · intro hmem
        obtain ⟨C₀, hC₀, hC₀C⟩ := mem_image.1 hmem
        have := hinj (mem_coe.2 (hsub hC₀)) (mem_coe.2 (mem_filter.2 ⟨hC, hCm⟩)) hC₀C
        exact this ▸ (mem_filter.1 hC₀).1
      · intro hCA
        exact mem_image_of_mem _ (mem_filter.2 ⟨hCA, hCm⟩)
    have hCM : ∀ C ∈ roots F, (∃ l, e l ∈ C) → nr_tr e C ∈ M.image (nr_tr e) :=
      fun C hC hCm => mem_image_of_mem _ (mem_filter.2 ⟨hC, hCm⟩)
    have h₁ : ((A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e)) ⊆
        roots (restrictForest e F) := by
      rw [hR']
      exact image_subset_image hsub
    have h₂ : M.image (nr_tr e) \ (A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e) ⊆
        roots (restrictForest e F) := by
      rw [hR']
      exact sdiff_subset
    have hiff₂ : ∀ C ∈ roots F, (∃ l, e l ∈ C) →
        (nr_tr e C ∈ M.image (nr_tr e) \ (A.filter fun C => ∃ l, e l ∈ C).image (nr_tr e) ↔
          C ∈ roots F \ A) := by
      intro C hC hCm
      rw [mem_sdiff, hiff C hC hCm, mem_sdiff]
      simp [hC, hCM C hC hCm]
    rw [nr_restrict_forestBelow hF e hAR h₁ hiff,
      nr_restrict_forestBelow hF e sdiff_subset h₂ hiff₂]
  rw [sum_congr rfl key, nr_sum_powerset_filter γ (fun C => ∃ l, e l ∈ C) (roots F)
      fun A₁ => Φ (forestBelow (restrictForest e F) (A₁.image (nr_tr e)))
        (forestBelow (restrictForest e F) (M.image (nr_tr e) \ A₁.image (nr_tr e))),
    nr_sum_powerset_image γ (nr_tr e) hinj
      fun A' => Φ (forestBelow (restrictForest e F) A')
        (forestBelow (restrictForest e F) (M.image (nr_tr e) \ A')), hR']

/-! ### Supports -/

/-- The lineages sampled from the taxa in the list `l`. -/
private def nr_T (s : L → X) (l : List X) : Finset L :=
  univ.filter fun x => s x ∈ l

/-- `μ` is supported on good forests on lineages in `T`. -/
private def nr_Supp (μ : Finset (Finset L) → ℝ) (T : Finset L) : Prop :=
  ∀ G, μ G ≠ 0 → IsGoodForest G ∧ lineages G ⊆ T

private theorem nr_T_append (s : L → X) (l₁ l₂ : List X) :
    nr_T s (l₁ ++ l₂) = nr_T s l₁ ∪ nr_T s l₂ := by
  ext x
  simp [nr_T]

omit [DecidableEq L] in
private theorem nr_T_disjoint (s : L → X) {l₁ l₂ : List X} (h : (l₁ ++ l₂).Nodup) :
    Disjoint (nr_T s l₁) (nr_T s l₂) := by
  rw [disjoint_left]
  intro x hx₁ hx₂
  simp only [nr_T, mem_filter, mem_univ, true_and] at hx₁ hx₂
  exact (List.nodup_append.1 h).2.2 _ hx₁ _ hx₂ rfl

private theorem nr_lineages_sampledAt (s : L → X) (x : X) :
    lineages (sampledAt s x) = univ.filter fun l => s l = x :=
  lineages_image_singleton _

/-- The lineages sampled from two distinct taxa are disjoint. -/
theorem disjoint_lineages_sampledAt (s : L → X) {a b : X} (hab : a ≠ b) :
    Disjoint (lineages (sampledAt s a)) (lineages (sampledAt s b)) := by
  rw [nr_lineages_sampledAt, nr_lineages_sampledAt, disjoint_left]
  intro l hla hlb
  exact hab ((mem_filter.1 hla).2.symm.trans (mem_filter.1 hlb).2)

private theorem nr_sampledAt_subset (s : L → X) {a : X} {l : List X} (ha : a ∈ l) :
    lineages (sampledAt s a) ⊆ nr_T s l := by
  rw [nr_lineages_sampledAt]
  intro m hm
  simp only [nr_T, mem_filter, mem_univ, true_and] at hm ⊢
  rw [hm]
  exact ha

private theorem nr_biUnion_subset (s : L → X) (l : List X) :
    l.toFinset.biUnion (fun a => lineages (sampledAt s a)) ⊆ nr_T s l := by
  intro m hm
  obtain ⟨a, ha, hma⟩ := mem_biUnion.1 hm
  exact nr_sampledAt_subset s (List.mem_toFinset.1 ha) hma

private theorem nr_supp_net (s : L → X) (N : Net X) (hN : N.leaves.Nodup) :
    nr_Supp (N.forestDist s) (nr_T s N.leaves) := by
  intro G hG
  rw [Net.forestDist_eq] at hG
  obtain ⟨h1, -, h3⟩ := Net.forestDistOf_single_support N hN (sampledAt s)
    (fun a _ => isGoodForest_singletons _) (fun a _ b _ hab => disjoint_lineages_sampledAt s hab) hG
  exact ⟨h1, h3 ▸ nr_biUnion_subset s N.leaves⟩

private theorem nr_supp_side (s : L → X) (S : Side X) (hS : S.leaves.Nodup)
    {F : Finset (Finset L)} (hF : IsGoodForest F) (hFd : Disjoint (lineages F) (nr_T s S.leaves)) :
    nr_Supp (S.forestDist s F) (lineages F ∪ nr_T s S.leaves) := by
  intro G hG
  rw [Side.forestDist_eq] at hG
  obtain ⟨h1, -, -, h4⟩ := Side.forestDistOf_single_support S hS (sampledAt s)
    (fun a _ => isGoodForest_singletons _) (fun a _ b _ hab => disjoint_lineages_sampledAt s hab) hF
    (fun a ha => hFd.mono_right (nr_sampledAt_subset s ha)) hG
  exact ⟨h1, h4 ▸ union_subset_union subset_rfl (nr_biUnion_subset s S.leaves)⟩

private theorem nr_supp_kT {μ : Finset (Finset L) → ℝ} {T : Finset L} (h : nr_Supp μ T)
    (t : ℝ) : nr_Supp (μ ᵥ* kingmanTransition t) T := by
  intro G hG
  have hG' : ∑ H, μ H * kingmanTransition t H G ≠ 0 := hG
  obtain ⟨H, -, hH⟩ := exists_ne_zero_of_sum_ne_zero hG'
  obtain ⟨h1, h2⟩ := h H (left_ne_zero_of_mul hH)
  obtain ⟨g1, -, g3⟩ := kingmanTransition_support_good h1 (right_ne_zero_of_mul hH)
  exact ⟨g1, g3 ▸ h2⟩

private theorem nr_supp_union {μ ν : Finset (Finset L) → ℝ} {T₁ T₂ : Finset L}
    (hμ : nr_Supp μ T₁) (hν : nr_Supp ν T₂) (hT : Disjoint T₁ T₂) :
    nr_Supp (forestUnion μ ν) (T₁ ∪ T₂) := by
  intro G hG
  unfold forestUnion at hG
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero hF
  by_cases hU : F ∪ F' = G
  · rw [ite_eq_left hU] at hF'
    subst hU
    obtain ⟨h1, h2⟩ := hμ F (left_ne_zero_of_mul hF')
    obtain ⟨g1, g2⟩ := hν F' (right_ne_zero_of_mul hF')
    exact ⟨h1.union g1 (hT.mono h2 g2), by
      rw [lineages_union]
      exact union_subset_union h2 g2⟩
  · exact absurd (ite_eq_right hU) hF'

/-! ### The induction -/

private theorem nr_restrict_sampledAt (e : L' ↪ L) (s : L → X) (x : X) :
    restrictForest e (sampledAt s x) = sampledAt (s ∘ e) x := by
  ext D
  rw [nr_mem_restrict]
  unfold sampledAt
  simp only [mem_image, mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, ⟨l, hl⟩, rfl⟩
    rw [mem_singleton] at hl
    subst hl
    refine ⟨l, hm, ?_⟩
    ext k
    simp [nr_tr, e.injective.eq_iff]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨{e l}, ⟨e l, hl, rfl⟩, ⟨l, mem_singleton_self _⟩, ?_⟩
    ext k
    simp [nr_tr, e.injective.eq_iff]

private theorem nr_push_leaf (s : L → X) (e : L' ↪ L) (x : X) :
    nr_push e ((Net.leaf x).forestDist s) = (Net.leaf x).forestDist (s ∘ e) := by
  funext G'
  simp only [nr_push, Net.forestDist]
  rw [Fintype.sum_eq_single (sampledAt s x) fun G hG => by simp [hG], nr_restrict_sampledAt]
  by_cases h : G' = sampledAt (s ∘ e) x
  · simp [h]
  · simp [h, Ne.symm h]

/-- The kernel of a cycle, from the forest at the top of the child edge of its hybrid node to
the forest at its top node. -/
private def nr_C (s : L → X) (γ : ℝ) (S₁ S₂ : Side X) :
    Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G => ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
    forestUnion (S₁.forestDist s (forestBelow F A))
      (S₂.forestDist s (forestBelow F (roots F \ A))) G

private theorem nr_forestDist_cycle (s : L → X) (γ : ℝ) (S₁ S₂ : Side X) (ℓ : ℝ) (N : Net X) :
    (Net.cycle γ S₁ S₂ ℓ N).forestDist s =
      (N.forestDist s ᵥ* kingmanTransition ℓ) ᵥ* nr_C s γ S₁ S₂ := by
  funext G
  simp only [Net.forestDist, vecMul, dotProduct, nr_C]

/-- The cycle kernel lumps, given the lumpability of the processes along its sides. -/
private theorem nr_push_C (s : L → X) (e : L' ↪ L) (γ : ℝ) (S₁ S₂ : Side X)
    {T₁ T₂ : Finset L}
    (hS₁ : ∀ H, IsGoodForest H → Disjoint (lineages H) T₁ →
      nr_push e (S₁.forestDist s H) = S₁.forestDist (s ∘ e) (restrictForest e H))
    (hS₂ : ∀ H, IsGoodForest H → Disjoint (lineages H) T₂ →
      nr_push e (S₂.forestDist s H) = S₂.forestDist (s ∘ e) (restrictForest e H))
    {F : Finset (Finset L)} {T : Finset L} (hF : IsGoodForest F ∧ lineages F ⊆ T)
    (h₁ : Disjoint T T₁) (h₂ : Disjoint T T₂) (G' : Finset (Finset L')) :
    nr_push e (nr_C s γ S₁ S₂ F) G' = nr_C (s ∘ e) γ S₁ S₂ (restrictForest e F) G' := by
  have hsub : ∀ A, lineages (forestBelow F A) ⊆ T :=
    fun A => (lineages_mono (filter_subset _ _)).trans hF.2
  calc nr_push e (nr_C s γ S₁ S₂ F) G'
      = ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          nr_push e (forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) G' :=
        nr_push_sum e _ (fun A => γ ^ #A * (1 - γ) ^ #(roots F \ A))
          (fun A => forestUnion (S₁.forestDist s (forestBelow F A))
            (S₂.forestDist s (forestBelow F (roots F \ A)))) G'
    _ = ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (S₁.forestDist (s ∘ e) (restrictForest e (forestBelow F A)))
            (S₂.forestDist (s ∘ e) (restrictForest e (forestBelow F (roots F \ A)))) G' := by
        refine sum_congr rfl fun A _ => ?_
        rw [nr_push_forestUnion, hS₁ _ (isGoodForest_forestBelow hF.1) (h₁.mono_left (hsub A)),
          hS₂ _ (isGoodForest_forestBelow hF.1) (h₂.mono_left (hsub _))]
    _ = nr_C (s ∘ e) γ S₁ S₂ (restrictForest e F) G' :=
        nr_sum_split hF.1.1 e γ fun H₁ H₂ =>
          forestUnion (S₁.forestDist (s ∘ e) H₁) (S₂.forestDist (s ∘ e) H₂) G'

mutual
private theorem nr_net (s : L → X) (e : L' ↪ L) :
    ∀ N : Net X, N.leaves.Nodup → nr_push e (N.forestDist s) = N.forestDist (s ∘ e)
  | .leaf x, _ => nr_push_leaf s e x
  | .tree ℓ₁ N₁ ℓ₂ N₂, h => by
      have h' : (N₁.leaves ++ N₂.leaves).Nodup := h
      have h₁ := (List.nodup_append.1 h').1
      have h₂ := (List.nodup_append.1 h').2.1
      simp only [Net.forestDist]
      rw [nr_push_forestUnion, nr_push_kT e (fun F hF => (nr_supp_net s N₁ h₁ F hF).1.1),
        nr_push_kT e (fun F hF => (nr_supp_net s N₂ h₂ F hF).1.1), nr_net s e N₁ h₁,
        nr_net s e N₂ h₂]
  | .cycle γ S₁ S₂ ℓ N, h => by
      have h' : (S₁.leaves ++ S₂.leaves ++ N.leaves).Nodup := h
      have h12 := (List.nodup_append.1 h').1
      have hN := (List.nodup_append.1 h').2.1
      have hS₁ := (List.nodup_append.1 h12).1
      have hS₂ := (List.nodup_append.1 h12).2.1
      have hd := nr_T_disjoint s h'
      rw [nr_T_append, disjoint_union_left] at hd
      rw [nr_forestDist_cycle, nr_forestDist_cycle,
        nr_push_vecMul e (K' := nr_C (s ∘ e) γ S₁ S₂) fun F hF G' =>
          nr_push_C s e γ S₁ S₂ (fun H hH hHd => nr_side s e S₁ hS₁ H hH hHd)
            (fun H hH hHd => nr_side s e S₂ hS₂ H hH hHd)
            (nr_supp_kT (nr_supp_net s N hN) ℓ F hF) hd.1.symm hd.2.symm G',
        nr_push_kT e (fun F hF => (nr_supp_net s N hN F hF).1.1), nr_net s e N hN]

private theorem nr_side (s : L → X) (e : L' ↪ L) :
    ∀ S : Side X, S.leaves.Nodup → ∀ F, IsGoodForest F →
      Disjoint (lineages F) (nr_T s S.leaves) →
      nr_push e (S.forestDist s F) = S.forestDist (s ∘ e) (restrictForest e F)
  | .hyb ℓ, _, F, hF, _ => by
      funext G'
      simp only [Side.forestDist]
      exact kingmanTransition_lump hF.1 e ℓ G'
  | .node ℓ b N S, h, F, hF, hFd => by
      have h' : (N.leaves ++ S.leaves).Nodup := h
      have hN := (List.nodup_append.1 h').1
      have hS := (List.nodup_append.1 h').2.1
      have hFd' : Disjoint (lineages F) (nr_T s (N.leaves ++ S.leaves)) := hFd
      rw [nr_T_append, disjoint_union_right] at hFd'
      have hsupp := nr_supp_union (nr_supp_side s S hS hF hFd'.2)
        (nr_supp_kT (nr_supp_net s N hN) b) (by
          rw [disjoint_union_left]
          exact ⟨hFd'.1, (nr_T_disjoint s h').symm⟩)
      simp only [Side.forestDist]
      rw [nr_push_kT e (fun G hG => (hsupp G hG).1.1), nr_push_forestUnion,
        nr_side s e S hS F hF hFd'.2, nr_push_kT e (fun G hG => (nr_supp_net s N hN G hG).1.1),
        nr_net s e N hN]
end

/-- **Sampling consistency.** The forest at the root of `N` formed by the lineages of `L'`
(sampled through `s ∘ e`) is distributed as the restriction of the forest formed by the lineages
of `L` (the pushforward of its distribution under `Phylogenetics.restrictForest e`). -/
theorem Net.forestDist_restrict (N : Net X) (hN : N.leaves.Nodup) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then N.forestDist s G else 0) =
      N.forestDist (s ∘ e) G' :=
  congrFun (nr_net s e N hN) G'

/-- **Sampling consistency** of the gene trees: the gene tree of the lineages of `L'` is
distributed as the restriction of the gene tree of the lineages of `L` (the pushforward of its
distribution under `Phylogenetics.restrictForest e`). -/
theorem Net.geneTreeDist_restrict (N : Net X) (hN : N.leaves.Nodup) (s : L → X) (e : L' ↪ L)
    (G' : Finset (Finset L')) :
    ∑ G, (if restrictForest e G = G' then N.geneTreeDist s G else 0) =
      N.geneTreeDist (s ∘ e) G' := by
  have h := nr_push_vecMul e (μ := N.forestDist s) (K := kingmanAbsorption)
    (K' := kingmanAbsorption) fun F hF G' =>
      kingmanAbsorption_lump (nr_supp_net s N hN F hF).1.1 e G'
  rw [nr_net s e N hN] at h
  exact congrFun h G'

end Phylogenetics
