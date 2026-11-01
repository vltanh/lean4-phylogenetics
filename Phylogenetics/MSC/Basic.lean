module

public import Phylogenetics.Coalescent.Outcome
public import Phylogenetics.MSC.Defs

/-!
# Basic properties of the multispecies coalescent

The recursion `Phylogenetics.forestDist` is defined for any family of clusters `H` and any lengths;
most results here assume `H` is a hierarchy (`IsHierarchy H`) and the lengths are nonnegative.

* `enteringDist H len s A`: the distribution of the forest entering the population above `A`.
* `unrootedDistOf H len s`: the distribution of unrooted gene trees, for raw data; it is
  `SpeciesTree.unrootedDist` for a species tree.

## Main results

* `forestDist_eq_sum_entering`: `forestDist` is the entering distribution pushed through the
  population kernel.
* `forestDist_of_childClusters_eq_empty`, `forestDist_of_childClusters_eq_pair`,
  `forestDist_of_childClusters_eq_triple`: unfolding at a leaf, at a node with two children and
  at a node with three children (and the same for `enteringDist`).
* `forestDist_singleton_of_card_le_one`, `forestDist_id_singleton`: at a leaf from which at most
  one lineage is sampled, the leaving forest is the sampled forest.
* `forestDist_support`: the forest leaving the population above `A` is a forest on exactly the
  lineages sampled from `A`, containing their singletons (`enteringDist_support`: the same for the
  entering forest; `forestDist_univ_support`: above the root, it has at most one root).
* `forestDist_nonneg`, `forestDist_nonneg_of_ne_univ`, `forestDist_sum`, `forestDist_le_one`,
  `enteringDist_nonneg_of_ne_univ`, `enteringDist_sum`,
  `unrootedDistOf_nonneg`, `unrootedDistOf_sum`: probability distributions.
* `forestDist_congr_len`: only the lengths of the edges below the root matter.
* `unrootedDistOf_eq_sum_entering`: the unrooted distribution is obtained from the forest entering
  the population above the root through `unrootedOutcome`.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The distribution of the forest entering the population above `A`: the union of the
independent forests leaving the populations of the children of `A`, together with the singletons
of the lineages sampled at `A`. -/
noncomputable def enteringDist (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (F : Finset (Finset L)) : ℝ :=
  ∑ f : childClusters H A → Finset (Finset L),
    if univ.sup f ∪ sampledForest s A = F then ∏ B : childClusters H A, forestDist H len s B (f B)
    else 0

/-- The distribution of unrooted gene trees for raw data `H`, `len`. -/
noncomputable def unrootedDistOf (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (T : Finset (Finset L)) : ℝ :=
  ∑ G, if unroot G = T then forestDist H len s univ G else 0

theorem SpeciesTree.unrootedDist_eq_unrootedDistOf (σ : SpeciesTree X) (s : L → X) :
    σ.unrootedDist s = unrootedDistOf σ.clusters σ.length s := rfl

theorem forestDist_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ F, enteringDist H len s A F * populationKernel len A F G := by
  rw [forestDist]
  unfold enteringDist
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem forestDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (G : Finset (Finset L)) :
    forestDist H len s A G = populationKernel len A (sampledForest s A) G := by
  rw [forestDist]
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]
  simp

/-- A sum over the functions on a two-element finset is a double sum. -/
private lemma msc_sum_pi_pair {ι α β : Type*} [DecidableEq ι] [Fintype α] [AddCommMonoid β]
    {T : Finset ι} {B C : ι} (h : T = {B, C}) (hBC : B ≠ C) (g : (T → α) → β) :
    ∑ f : T → α, g f = ∑ a, ∑ b, g (fun D => if D.1 = B then a else b) := by
  subst h
  let e : (({B, C} : Finset ι) → α) ≃ α × α :=
    { toFun := fun f => (f ⟨B, by simp⟩, f ⟨C, by simp⟩)
      invFun := fun p D => if D.1 = B then p.1 else p.2
      left_inv := by
        intro f
        funext ⟨D, hD⟩
        rcases mem_insert.1 hD with rfl | hD
        · simp
        · rw [mem_singleton] at hD
          subst hD
          simp [hBC.symm]
      right_inv := by
        intro p
        simp [hBC.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over the functions on a three-element finset is a triple sum. -/
private lemma msc_sum_pi_triple {ι α β : Type*} [DecidableEq ι] [Fintype α] [AddCommMonoid β]
    {T : Finset ι} {B C D : ι} (h : T = {B, C, D}) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (g : (T → α) → β) :
    ∑ f : T → α, g f =
      ∑ a, ∑ b, ∑ c, g (fun E => if E.1 = B then a else if E.1 = C then b else c) := by
  subst h
  let e : (({B, C, D} : Finset ι) → α) ≃ α × α × α :=
    { toFun := fun f => (f ⟨B, by simp⟩, f ⟨C, by simp⟩, f ⟨D, by simp⟩)
      invFun := fun p E => if E.1 = B then p.1 else if E.1 = C then p.2.1 else p.2.2
      left_inv := by
        intro f
        funext ⟨E, hE⟩
        simp only [mem_insert, mem_singleton] at hE
        rcases hE with rfl | rfl | rfl
        · simp
        · simp [hBC.symm]
        · simp [hBD.symm, hCD.symm]
      right_inv := by
        intro p
        simp [hBC.symm, hBD.symm, hCD.symm] }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rfl

theorem forestDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, forestDist H len s B F₁ * forestDist H len s C F₂ *
        populationKernel len A (F₁ ∪ F₂ ∪ sampledForest s A) G := by
  rw [forestDist, msc_sum_pi_pair h hBC]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ => ?_
  congr 1
  · rw [Finset.prod_coe_sort (childClusters H A)
      (fun D => forestDist H len s D (if D = B then F₁ else F₂)), h, prod_pair hBC]
    simp [hBC.symm]
  · congr 2
    rw [univ_eq_attach, sup_attach (childClusters H A) (fun D => if D = B then F₁ else F₂), h,
      sup_insert, sup_singleton]
    simp [hBC.symm]

/-- Unfolding at a node with three children (a polytomy). -/
theorem forestDist_of_childClusters_eq_triple {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C D : Finset X} (h : childClusters H A = {B, C, D}) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (G : Finset (Finset L)) :
    forestDist H len s A G =
      ∑ F₁, ∑ F₂, ∑ F₃, forestDist H len s B F₁ * forestDist H len s C F₂ *
        forestDist H len s D F₃ * populationKernel len A (F₁ ∪ F₂ ∪ F₃ ∪ sampledForest s A) G := by
  rw [forestDist, msc_sum_pi_triple h hBC hBD hCD]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ =>
    Finset.sum_congr rfl fun F₃ _ => ?_
  congr 1
  · rw [Finset.prod_coe_sort (childClusters H A)
      (fun E => forestDist H len s E (if E = B then F₁ else if E = C then F₂ else F₃)), h,
      prod_insert (by simp [hBC, hBD]), prod_pair hCD]
    simp [hBC.symm, hBD.symm, hCD.symm, mul_assoc]
  · congr 2
    rw [univ_eq_attach, sup_attach (childClusters H A)
      (fun E => if E = B then F₁ else if E = C then F₂ else F₃), h,
      sup_insert, sup_insert, sup_singleton]
    simp [hBC.symm, hBD.symm, hCD.symm, union_assoc]

theorem enteringDist_of_childClusters_eq_empty {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A : Finset X} (h : childClusters H A = ∅) (F : Finset (Finset L)) :
    enteringDist H len s A F = if F = sampledForest s A then 1 else 0 := by
  unfold enteringDist
  have : IsEmpty (childClusters H A) := by rw [h]; infer_instance
  rw [Fintype.sum_unique]
  simp [eq_comm]

theorem enteringDist_of_childClusters_eq_pair {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C : Finset X} (h : childClusters H A = {B, C}) (hBC : B ≠ C)
    (F : Finset (Finset L)) :
    enteringDist H len s A F =
      ∑ F₁, ∑ F₂, if F₁ ∪ F₂ ∪ sampledForest s A = F then
        forestDist H len s B F₁ * forestDist H len s C F₂ else 0 := by
  unfold enteringDist
  rw [msc_sum_pi_pair h hBC]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ => ?_
  dsimp only
  rw [Finset.prod_coe_sort (childClusters H A)
      (fun D => forestDist H len s D (if D = B then F₁ else F₂)),
    univ_eq_attach, sup_attach (childClusters H A) (fun D => if D = B then F₁ else F₂),
    h, prod_pair hBC, sup_insert, sup_singleton]
  simp [hBC.symm]

theorem enteringDist_of_childClusters_eq_triple {H : Finset (Finset X)} {len : Finset X → ℝ}
    {s : L → X} {A B C D : Finset X} (h : childClusters H A = {B, C, D}) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (F : Finset (Finset L)) :
    enteringDist H len s A F =
      ∑ F₁, ∑ F₂, ∑ F₃, if F₁ ∪ F₂ ∪ F₃ ∪ sampledForest s A = F then
        forestDist H len s B F₁ * forestDist H len s C F₂ * forestDist H len s D F₃ else 0 := by
  unfold enteringDist
  rw [msc_sum_pi_triple h hBC hBD hCD]
  refine Finset.sum_congr rfl fun F₁ _ => Finset.sum_congr rfl fun F₂ _ =>
    Finset.sum_congr rfl fun F₃ _ => ?_
  dsimp only
  rw [Finset.prod_coe_sort (childClusters H A)
      (fun E => forestDist H len s E (if E = B then F₁ else if E = C then F₂ else F₃)),
    univ_eq_attach, sup_attach (childClusters H A)
      (fun E => if E = B then F₁ else if E = C then F₂ else F₃), h,
    prod_insert (by simp [hBC, hBD]), prod_pair hCD, sup_insert, sup_insert, sup_singleton]
  simp [hBC.symm, hBD.symm, hCD.symm, mul_assoc, union_assoc]


omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

omit [Fintype X] in
theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  rw [mem_sampledForest]
  constructor
  · rintro ⟨l', hl', h⟩
    rw [singleton_inj] at h
    exact h ▸ hl'
  · exact fun h => ⟨l, h, rfl⟩

omit [Fintype L] in
private lemma msc_singleton_laminar {C D : Finset L} {l : L} (hC : C = {l}) :
    C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  subst hC
  by_cases h : l ∈ D
  · exact Or.inl (singleton_subset_iff.2 h)
  · exact Or.inr (Or.inr (disjoint_singleton_left.2 h))

/-- The forest entering the population above a cluster `A` of a hierarchy, when the forests
leaving the children are forests on the lineages sampled from the children, is a forest on the
lineages sampled from `A`, containing their singletons. -/
theorem IsHierarchy.isForest_entering {H : Finset (Finset X)} (hH : IsHierarchy H) {s : L → X}
    {A : Finset X} (f : childClusters H A → Finset (Finset L))
    (hf : ∀ B, IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X))) :
    IsForest (univ.sup f ∪ sampledForest s A) ∧
      sampledForest s A ⊆ univ.sup f ∪ sampledForest s A ∧
      lineages (univ.sup f ∪ sampledForest s A) = univ.filter (fun l => s l ∈ A) := by
  have hsub : ∀ (B : childClusters H A) (C : Finset L), C ∈ f B → ∀ l ∈ C,
      s l ∈ (B : Finset X) := by
    intro B C hC l hl
    have : l ∈ lineages (f B) := mem_lineages.2 ⟨C, hC, hl⟩
    rw [(hf B).2, mem_filter] at this
    exact this.2
  have hBA : ∀ B : childClusters H A, (B : Finset X) ⊆ A :=
    fun B => (mem_childClusters.1 B.2).2.1.1
  refine ⟨⟨fun C hC => ?_, fun C hC D hD => ?_⟩, subset_union_right, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
      exact (hf B).1.1 C hCB
    · exact (isForest_sampledForest s A).1 C hC
  · rcases mem_union.1 hD with hD' | hD'
    · rcases mem_union.1 hC with hC' | hC'
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC'
        obtain ⟨B', -, hDB'⟩ := Finset.mem_sup.1 hD'
        by_cases hBB' : B = B'
        · subst hBB'
          exact (hf B).1.2 C hCB D hDB'
        · refine Or.inr (Or.inr (Finset.disjoint_left.2 fun l hlC hlD => ?_))
          have hdis := hH.disjoint_of_mem_childClusters B.2 B'.2
            (fun h => hBB' (Subtype.ext h))
          exact Finset.disjoint_left.1 hdis (hsub B C hCB l hlC) (hsub B' D hDB' l hlD)
      · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hC'
        exact msc_singleton_laminar rfl
    · obtain ⟨l, -, rfl⟩ := mem_sampledForest.1 hD'
      rcases msc_singleton_laminar (D := C) (rfl : ({l} : Finset L) = {l}) with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h.symm)
  · ext l
    rw [mem_lineages, mem_filter]
    constructor
    · rintro ⟨C, hC, hlC⟩
      refine ⟨mem_univ _, ?_⟩
      rcases mem_union.1 hC with hC | hC
      · obtain ⟨B, -, hCB⟩ := Finset.mem_sup.1 hC
        exact hBA B (hsub B C hCB l hlC)
      · obtain ⟨l', hl', rfl⟩ := mem_sampledForest.1 hC
        rw [mem_singleton] at hlC
        exact hlC ▸ hl'
    · rintro ⟨-, h⟩
      exact ⟨{l}, mem_union_right _ (singleton_mem_sampledForest.2 h), mem_singleton_self l⟩

/-- The population kernels only add clusters to a forest and keep its lineages. -/
theorem populationKernel_support {len : Finset X → ℝ} {A : Finset X} {F G : Finset (Finset L)}
    (hF : IsForest F) (h : populationKernel len A F G ≠ 0) :
    IsForest G ∧ F ⊆ G ∧ lineages G = lineages F := by
  unfold populationKernel at h
  split_ifs at h with hA
  · rw [kingmanAbsorption_apply hF] at h
    split_ifs at h with h0 h1 h2
    · subst h1
      exact ⟨hF, subset_rfl, rfl⟩
    · exact absurd rfl h
    · obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF h
      exact ⟨h1, h2, h3⟩
    · exact absurd rfl h
  · rw [kingmanTransition_apply hF] at h
    obtain ⟨h1, h2, h3, -⟩ := jumpMatrix_pow_support hF (right_ne_zero_of_mul h)
    exact ⟨h1, h2, h3⟩

theorem populationKernel_nonneg {len : Finset X → ℝ} {A : Finset X} (hlen : A ≠ univ → 0 ≤ len A)
    {F : Finset (Finset L)} (hF : IsForest F) (G : Finset (Finset L)) :
    0 ≤ populationKernel len A F G := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_nonneg hF G
  · exact kingmanTransition_nonneg (hlen hA) F G

theorem populationKernel_sum (len : Finset X → ℝ) (A : Finset X) {F : Finset (Finset L)}
    (hF : IsForest F) : ∑ G, populationKernel len A F G = 1 := by
  unfold populationKernel
  split_ifs with hA
  · exact kingmanAbsorption_sum hF
  · exact kingmanTransition_sum hF (len A)

/-- The forest leaving the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem forestDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) {G : Finset (Finset L)}
    (hG : forestDist H len s A G ≠ 0) :
    IsForest G ∧ sampledForest s A ⊆ G ∧ lineages G = univ.filter (fun l => s l ∈ A) := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist] at hG
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
  have hprod := left_ne_zero_of_mul hf
  have hfB : ∀ B : childClusters H A,
      IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
    intro B
    have hBmem := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := ih B hBmem.2.1 hBmem.1 (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
    exact ⟨h1, h3⟩
  obtain ⟨hF, hSF, hLF⟩ := hH.isForest_entering f hfB
  obtain ⟨hG1, hG2, hG3⟩ := populationKernel_support hF (right_ne_zero_of_mul hf)
  exact ⟨hG1, hSF.trans hG2, hG3.trans hLF⟩

/-- Nonnegativity, assuming only that the lengths of the edges below the root are nonnegative
(the length at `univ` is irrelevant). -/
theorem forestDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X}
    (hA : A ∈ H) (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist]
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
  · rw [hprod, zero_mul]
  · refine mul_nonneg (Finset.prod_nonneg fun B _ => ?_) ?_
    · exact ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _
    · have hfB : ∀ B : childClusters H A,
          IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
        intro B
        obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
          (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
        exact ⟨h1, h3⟩
      exact populationKernel_nonneg (hlen A hA) (hH.isForest_entering f hfB).1 G

theorem forestDist_nonneg {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, 0 ≤ len A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : 0 ≤ forestDist H len s A G :=
  forestDist_nonneg_of_ne_univ hH (fun B hB _ => hlen B hB) s hA G

theorem forestDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hA : A ∈ H) : ∑ G, forestDist H len s A G = 1 := by
  induction A using Finset.strongInduction with
  | H A ih =>
  have hunf : ∀ G, forestDist H len s A G = ∑ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        populationKernel len A (univ.sup f ∪ sampledForest s A) G := fun G => by
    rw [forestDist]
  simp_rw [hunf]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hterm : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
        ∑ G, populationKernel len A (univ.sup f ∪ sampledForest s A) G =
      ∏ B : childClusters H A, forestDist H len s B (f B) := by
    intro f
    by_cases hprod : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hprod, zero_mul]
    · have hfB : ∀ B : childClusters H A,
          IsForest (f B) ∧ lineages (f B) = univ.filter (fun l => s l ∈ (B : Finset X)) := by
        intro B
        obtain ⟨h1, -, h3⟩ := forestDist_support hH len s (mem_childClusters.1 B.2).1
          (Finset.prod_ne_zero_iff.1 hprod B (mem_univ _))
        exact ⟨h1, h3⟩
      rw [populationKernel_sum len A (hH.isForest_entering f hfB).1, mul_one]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1

/-- The unrooted gene tree distribution, from the forest entering the population above the root. -/
theorem unrootedDistOf_eq_sum_entering (H : Finset (Finset X)) (len : Finset X → ℝ) (s : L → X)
    (T : Finset (Finset L)) :
    unrootedDistOf H len s T = ∑ F, enteringDist H len s univ F * unrootedOutcome F T := by
  unfold unrootedDistOf unrootedOutcome
  have hK : populationKernel (L := L) len (univ : Finset X) = kingmanAbsorption :=
    ite_eq_left rfl
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [forestDist_eq_sum_entering, hK]
  split_ifs <;> simp

/-! ### The entering distribution -/

/-- The forest entering the population above a cluster `A` of a hierarchy is a forest on exactly
the lineages sampled from `A`, containing the singletons of all of them. -/
theorem enteringDist_support {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} {F : Finset (Finset L)} (hF : enteringDist H len s A F ≠ 0) :
    IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F = univ.filter (fun l => s l ∈ A) := by
  unfold enteringDist at hF
  obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hF
  split_ifs at hf with hfF
  · subst hfF
    refine hH.isForest_entering f fun B => ?_
    have hBmem := mem_childClusters.1 B.2
    obtain ⟨h1, -, h3⟩ := forestDist_support hH len s hBmem.1
      (Finset.prod_ne_zero_iff.1 hf B (mem_univ _))
    exact ⟨h1, h3⟩
  · exact absurd rfl hf

/-- The forest leaving the population above the root is a forest on all the lineages with at
most one root (a single rooted gene tree, when some lineage is sampled). -/
theorem forestDist_univ_support {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (s : L → X) {G : Finset (Finset L)}
    (hG : forestDist H len s univ G ≠ 0) :
    IsForest G ∧ sampledForest s univ ⊆ G ∧ lineages G = univ ∧ #(roots G) ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := forestDist_support hH len s hH.1 hG
  refine ⟨h1, h2, by simpa using h3, ?_⟩
  rw [forestDist_eq_sum_entering] at hG
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
  have hFf := (enteringDist_support hH len s (left_ne_zero_of_mul hF)).1
  have hK := right_ne_zero_of_mul hF
  rw [populationKernel, ite_eq_left rfl, kingmanAbsorption_apply hFf] at hK
  split_ifs at hK with h0 hGF h1
  · rw [hGF, h0]
    exact Nat.zero_le 1
  · exact absurd rfl hK
  · rw [h1]
  · exact absurd rfl hK

theorem enteringDist_nonneg_of_ne_univ {H : Finset (Finset X)} (hH : IsHierarchy H)
    {len : Finset X → ℝ} (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) (A : Finset X)
    (F : Finset (Finset L)) : 0 ≤ enteringDist H len s A F := by
  unfold enteringDist
  refine Finset.sum_nonneg fun f _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun B _ =>
      forestDist_nonneg_of_ne_univ hH hlen s (mem_childClusters.1 B.2).1 _
  · exact le_rfl

theorem enteringDist_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) : ∑ F, enteringDist H len s A F = 1 := by
  unfold enteringDist
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  rw [← Fintype.prod_sum (fun (B : childClusters H A) (F : Finset (Finset L)) =>
    forestDist H len s B F)]
  exact Finset.prod_eq_one fun B _ => forestDist_sum hH len s (mem_childClusters.1 B.2).1

/-! ### Leaves -/

/-- At a leaf `{x}` from which at most one lineage is sampled, the forest leaving the population
is the sampled forest, whatever the length of the pendant edge. -/
theorem forestDist_singleton_of_card_le_one {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) {s : L → X} {x : X} (hx : #(univ.filter fun l => s l = x) ≤ 1)
    (G : Finset (Finset L)) :
    forestDist H len s {x} G = if G = sampledForest s {x} then 1 else 0 := by
  rw [forestDist_of_childClusters_eq_empty (hH.childClusters_singleton x)]
  have hF := isForest_sampledForest s ({x} : Finset X)
  have hk : #(roots (sampledForest s {x})) ≤ 1 := by
    refine (card_le_card (roots_subset _)).trans (card_image_le.trans ?_)
    simpa using hx
  by_cases hxu : ({x} : Finset X) = univ
  · rw [populationKernel, ite_eq_left hxu, kingmanAbsorption_apply hF]
    by_cases h0 : #(roots (sampledForest s {x})) = 0
    · rw [ite_eq_left h0]
    · have h1 : #(roots (sampledForest s {x})) = 1 := by omega
      rw [ite_eq_right h0, h1, Nat.sub_self, pow_zero, Matrix.one_apply]
      by_cases hG : G = sampledForest s {x}
      · subst hG
        simp [h1]
      · simp [hG, Ne.symm hG]
  · rw [populationKernel, ite_eq_right hxu]
    exact kingmanTransition_of_card_roots_le_one hF hk _ G

theorem sampledForest_id (A : Finset X) :
    sampledForest (id : X → X) A = A.image fun x => {x} := by
  ext C
  simp [sampledForest]

/-- With one lineage per taxon, the forest leaving the population above a leaf `{x}` is the
single lineage `{x}`. -/
theorem forestDist_id_singleton {H : Finset (Finset X)} (hH : IsHierarchy H)
    (len : Finset X → ℝ) (x : X) (G : Finset (Finset X)) :
    forestDist H len id {x} G = if G = {{x}} then 1 else 0 := by
  have hS : sampledForest (id : X → X) {x} = {{x}} := by
    ext C
    simp [sampledForest, eq_comm]
  rw [forestDist_singleton_of_card_le_one hH len (by simp [Finset.filter_eq']) G, hS]

/-! ### Dependence on the lengths -/

/-- `forestDist` depends on the lengths only through the edges below the root. -/
theorem forestDist_congr_len {H : Finset (Finset X)} {len len' : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → len A = len' A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : forestDist H len s A G = forestDist H len' s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 H len, forestDist.eq_1 H len']
  have hK : populationKernel (L := L) len A = populationKernel len' A := by
    unfold populationKernel
    split_ifs with hAu
    · rfl
    · rw [hlen A hA hAu]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hK]
  congr 1
  exact Finset.prod_congr rfl fun B _ =>
    ih B (mem_childClusters.1 B.2).2.1 (mem_childClusters.1 B.2).1 _

/-! ### Species trees: probability distributions -/

theorem SpeciesTree.forestDist_nonneg_of_mem (σ : SpeciesTree X) (s : L → X) {A : Finset X}
    (hA : A ∈ σ.clusters) (G : Finset (Finset L)) :
    0 ≤ forestDist σ.clusters σ.length s A G :=
  forestDist_nonneg_of_ne_univ σ.isHierarchy (fun B hB hBu => (σ.length_pos B hB hBu).le) s hA G

theorem SpeciesTree.forestDist_sum_eq_one (σ : SpeciesTree X) (s : L → X) {A : Finset X}
    (hA : A ∈ σ.clusters) : ∑ G, forestDist σ.clusters σ.length s A G = 1 :=
  forestDist_sum σ.isHierarchy σ.length s hA

theorem forestDist_le_one {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) {A : Finset X} (hA : A ∈ H)
    (G : Finset (Finset L)) : forestDist H len s A G ≤ 1 := by
  rw [← forestDist_sum hH len s hA]
  exact Finset.single_le_sum (fun G _ => forestDist_nonneg_of_ne_univ hH hlen s hA G)
    (mem_univ G)

theorem unrootedDistOf_nonneg {H : Finset (Finset X)} (hH : IsHierarchy H) {len : Finset X → ℝ}
    (hlen : ∀ A ∈ H, A ≠ univ → 0 ≤ len A) (s : L → X) (T : Finset (Finset L)) :
    0 ≤ unrootedDistOf H len s T := by
  unfold unrootedDistOf
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact forestDist_nonneg_of_ne_univ hH hlen s hH.1 G
  · exact le_rfl

theorem unrootedDistOf_sum {H : Finset (Finset X)} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) : ∑ T, unrootedDistOf H len s T = 1 := by
  unfold unrootedDistOf
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, mem_univ, ite_true]
  exact forestDist_sum hH len s hH.1

end Phylogenetics
