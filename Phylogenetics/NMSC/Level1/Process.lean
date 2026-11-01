module

public import Phylogenetics.NMSC.Level1.Basic
/-!
# The network coalescent with given forests at the leaves

`Phylogenetics.Net.forestDistOf ι N` runs the network multispecies coalescent of
`Phylogenetics.Net.forestDist` on `N`, the leaf labelled `a` holding a random forest with
distribution `ι a`. With the singletons of the sampled lineages at the leaves it is `Net.forestDist`
(`Phylogenetics.Net.forestDist_eq`).

## Main results

* `Phylogenetics.Net.forestDistOf_bind`: substituting networks for the leaves of `N` (`Net.bind`)
  composes the processes.
* `Phylogenetics.Net.forestDistOf_relabel`: relabelling the lineages relabels the distributions.
* `Phylogenetics.Net.forestDistOf_single_support`, `Phylogenetics.Net.forestDistOf_single_sum`: with
  good forests on disjoint lineages at distinct leaves, the result is a probability distribution on
  good forests that contain the forests of the leaves; and the same for sides.
* `Phylogenetics.Net.forestDist_of_card_le_one`: a network from which at most one lineage is sampled
  returns it unchanged.
* `Phylogenetics.Net.forestDist_cycle_of_single`: at a cycle whose hybrid node receives at most one
  lineage, that lineage takes the side of `γ` with probability `γ`.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u v

variable {α : Type u} {β : Type v} {L : Type*} [Fintype L] [DecidableEq L]

mutual
/-- The network multispecies coalescent on `N` when the leaf labelled `a` holds a random forest
with distribution `ι a`: as `Phylogenetics.Net.forestDist`, the leaves excepted. -/
noncomputable def Net.forestDistOf (ι : α → Finset (Finset L) → ℝ) :
    Net α → Finset (Finset L) → ℝ
  | .leaf a => ι a
  | .tree ℓ₁ N₁ ℓ₂ N₂ =>
      forestUnion (N₁.forestDistOf ι ᵥ* kingmanTransition ℓ₁)
        (N₂.forestDistOf ι ᵥ* kingmanTransition ℓ₂)
  | .cycle γ S₁ S₂ ℓ N => fun G =>
      ∑ F, (N.forestDistOf ι ᵥ* kingmanTransition ℓ) F *
        ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (S₁.forestDistOf ι (forestBelow F A))
            (S₂.forestDistOf ι (forestBelow F (roots F \ A))) G

/-- The network multispecies coalescent along a side, with given forests at the leaves. -/
noncomputable def Side.forestDistOf (ι : α → Finset (Finset L) → ℝ) :
    Side α → Finset (Finset L) → Finset (Finset L) → ℝ
  | .hyb ℓ => fun F => kingmanTransition ℓ F
  | .node ℓ b N S => fun F =>
      forestUnion (S.forestDistOf ι F) (N.forestDistOf ι ᵥ* kingmanTransition b) ᵥ*
        kingmanTransition ℓ
end

/-- The forests at the leaves in `Phylogenetics.Net.forestDist`: the singletons of the lineages
sampled from the taxon. -/
def sampledInput {X : Type*} [DecidableEq X] (s : L → X) (x : X) : Finset (Finset L) → ℝ :=
  Pi.single (sampledAt s x) 1

mutual
private theorem np_forestDist_eq_net {X : Type u} [DecidableEq X] (s : L → X) :
    ∀ N : Net X, N.forestDist s = N.forestDistOf (sampledInput s)
  | .leaf x => by
      funext G
      simp only [Net.forestDist, Net.forestDistOf, sampledInput, Pi.single_apply]
  | .tree ℓ₁ N₁ ℓ₂ N₂ => by
      simp only [Net.forestDist, Net.forestDistOf, np_forestDist_eq_net s N₁,
        np_forestDist_eq_net s N₂]
  | .cycle γ S₁ S₂ ℓ N => by
      simp only [Net.forestDist, Net.forestDistOf, np_forestDist_eq_net s N,
        np_forestDist_eq_side s S₁, np_forestDist_eq_side s S₂]

private theorem np_forestDist_eq_side {X : Type u} [DecidableEq X] (s : L → X) :
    ∀ S : Side X, S.forestDist s = S.forestDistOf (sampledInput s)
  | .hyb _ => rfl
  | .node ℓ b N S => by
      simp only [Side.forestDist, Side.forestDistOf, np_forestDist_eq_net s N,
        np_forestDist_eq_side s S]
end

theorem Net.forestDist_eq {X : Type u} [DecidableEq X] (s : L → X) (N : Net X) :
    N.forestDist s = N.forestDistOf (sampledInput s) :=
  np_forestDist_eq_net s N

theorem Side.forestDist_eq {X : Type u} [DecidableEq X] (s : L → X) (S : Side X) :
    S.forestDist s = S.forestDistOf (sampledInput s) :=
  np_forestDist_eq_side s S

/-! ### Substitution -/

mutual
/-- Substitute the network `f a` for each leaf labelled `a`. -/
def Net.bind (f : α → Net β) : Net α → Net β
  | .leaf a => f a
  | .tree ℓ₁ N₁ ℓ₂ N₂ => .tree ℓ₁ (N₁.bind f) ℓ₂ (N₂.bind f)
  | .cycle γ S₁ S₂ ℓ N => .cycle γ (S₁.bind f) (S₂.bind f) ℓ (N.bind f)

/-- Substitute the network `f a` for each leaf labelled `a` below a side. -/
def Side.bind (f : α → Net β) : Side α → Side β
  | .hyb ℓ => .hyb ℓ
  | .node ℓ b N S => .node ℓ b (N.bind f) (S.bind f)
end

mutual
private theorem np_leaves_bind_net (f : α → Net β) :
    ∀ N : Net α, (N.bind f).leaves = N.leaves.flatMap fun a => (f a).leaves
  | .leaf a => by simp [Net.bind, Net.leaves]
  | .tree _ N₁ _ N₂ => by
      simp only [Net.bind, Net.leaves, List.flatMap_append, np_leaves_bind_net f N₁,
        np_leaves_bind_net f N₂]
  | .cycle _ S₁ S₂ _ N => by
      simp only [Net.bind, Net.leaves, List.flatMap_append, np_leaves_bind_side f S₁,
        np_leaves_bind_side f S₂, np_leaves_bind_net f N]

private theorem np_leaves_bind_side (f : α → Net β) :
    ∀ S : Side α, (S.bind f).leaves = S.leaves.flatMap fun a => (f a).leaves
  | .hyb _ => by simp [Side.bind, Side.leaves]
  | .node _ _ N S => by
      simp only [Side.bind, Side.leaves, List.flatMap_append, np_leaves_bind_net f N,
        np_leaves_bind_side f S]
end

theorem Net.leaves_bind (f : α → Net β) (N : Net α) :
    (N.bind f).leaves = N.leaves.flatMap fun a => (f a).leaves :=
  np_leaves_bind_net f N

mutual
private theorem np_forestDistOf_bind_net (ι : β → Finset (Finset L) → ℝ) (f : α → Net β) :
    ∀ N : Net α, (N.bind f).forestDistOf ι = N.forestDistOf fun a => (f a).forestDistOf ι
  | .leaf _ => rfl
  | .tree ℓ₁ N₁ ℓ₂ N₂ => by
      simp only [Net.bind, Net.forestDistOf, np_forestDistOf_bind_net ι f N₁,
        np_forestDistOf_bind_net ι f N₂]
  | .cycle γ S₁ S₂ ℓ N => by
      simp only [Net.bind, Net.forestDistOf, np_forestDistOf_bind_net ι f N,
        np_forestDistOf_bind_side ι f S₁, np_forestDistOf_bind_side ι f S₂]

private theorem np_forestDistOf_bind_side (ι : β → Finset (Finset L) → ℝ) (f : α → Net β) :
    ∀ S : Side α, (S.bind f).forestDistOf ι = S.forestDistOf fun a => (f a).forestDistOf ι
  | .hyb _ => rfl
  | .node ℓ b N S => by
      simp only [Side.bind, Side.forestDistOf, np_forestDistOf_bind_net ι f N,
        np_forestDistOf_bind_side ι f S]
end

theorem Net.forestDistOf_bind (ι : β → Finset (Finset L) → ℝ) (f : α → Net β) (N : Net α) :
    (N.bind f).forestDistOf ι = N.forestDistOf fun a => (f a).forestDistOf ι :=
  np_forestDistOf_bind_net ι f N

/-! ### Relabelling the lineages -/

/-- A matrix invariant under relabelling maps relabelled distributions to relabelled
distributions. -/
private theorem np_vecMul_relabel (σ : Equiv.Perm L) {μ μ' : Finset (Finset L) → ℝ}
    (h : ∀ H, μ' (relabelFamily σ H) = μ H)
    {M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ}
    (hM : ∀ F G, M (relabelFamily σ F) (relabelFamily σ G) = M F G)
    (G : Finset (Finset L)) :
    (μ' ᵥ* M) (relabelFamily σ G) = (μ ᵥ* M) G := by
  symm
  simp only [vecMul, dotProduct]
  exact Fintype.sum_equiv (relabelFamilyEquiv σ) _ _ fun H => by
    simp only [relabelFamilyEquiv_apply, h, hM]

/-- The union of independent forests commutes with relabelling. -/
private theorem np_forestUnion_relabel (σ : Equiv.Perm L) {μ μ' ν ν' : Finset (Finset L) → ℝ}
    (hμ : ∀ H, μ' (relabelFamily σ H) = μ H) (hν : ∀ H, ν' (relabelFamily σ H) = ν H)
    (G : Finset (Finset L)) :
    forestUnion μ' ν' (relabelFamily σ G) = forestUnion μ ν G := by
  symm
  unfold forestUnion
  refine Fintype.sum_equiv (relabelFamilyEquiv σ) _ _ fun F => ?_
  refine Fintype.sum_equiv (relabelFamilyEquiv σ) _ _ fun F' => ?_
  simp only [relabelFamilyEquiv_apply, hμ, hν, ← relabelFamily_union,
    (relabelFamily_injective σ).eq_iff]

omit [Fintype L] in
private theorem np_relabel_sdiff (σ : Equiv.Perm L) (F A : Finset (Finset L)) :
    relabelFamily σ (F \ A) = relabelFamily σ F \ relabelFamily σ A :=
  image_sdiff _ _ (map_injective _)

omit [Fintype L] in
private theorem np_relabel_subset (σ : Equiv.Perm L) {A F : Finset (Finset L)} (h : A ⊆ F) :
    relabelFamily σ A ⊆ relabelFamily σ F :=
  image_subset_image h

omit [Fintype L] in
private theorem np_relabel_symm' (σ : Equiv.Perm L) (F : Finset (Finset L)) :
    relabelFamily σ (relabelFamily σ.symm F) = F := by
  simpa using relabelFamily_symm σ.symm F

mutual
private theorem np_relabel_net (σ : Equiv.Perm L) (ι : α → Finset (Finset L) → ℝ) :
    ∀ (N : Net α) (G : Finset (Finset L)),
      N.forestDistOf (fun a H => ι a (relabelFamily σ.symm H)) (relabelFamily σ G) =
        N.forestDistOf ι G
  | .leaf a, G => by
      show ι a (relabelFamily σ.symm (relabelFamily σ G)) = ι a G
      rw [relabelFamily_symm]
  | .tree ℓ₁ N₁ ℓ₂ N₂, G =>
      np_forestUnion_relabel σ
        (np_vecMul_relabel σ (np_relabel_net σ ι N₁) (kingmanTransition_relabelFamily σ ℓ₁))
        (np_vecMul_relabel σ (np_relabel_net σ ι N₂) (kingmanTransition_relabelFamily σ ℓ₂)) G
  | .cycle γ S₁ S₂ ℓ N, G => by
      have hN := np_vecMul_relabel σ (np_relabel_net σ ι N) (kingmanTransition_relabelFamily σ ℓ)
      have hS₁ := np_relabel_side σ ι S₁
      have hS₂ := np_relabel_side σ ι S₂
      simp only [Net.forestDistOf]
      symm
      refine Fintype.sum_equiv (relabelFamilyEquiv σ) _ _ fun F => ?_
      simp only [relabelFamilyEquiv_apply, hN, roots_relabelFamily]
      congr 1
      refine sum_nbij' (relabelFamily σ) (relabelFamily σ.symm) ?_ ?_ ?_ ?_ ?_
      · intro A hA
        exact mem_powerset.2 (np_relabel_subset σ (mem_powerset.1 hA))
      · intro A hA
        have := np_relabel_subset σ.symm (mem_powerset.1 hA)
        rw [relabelFamily_symm] at this
        exact mem_powerset.2 this
      · intro A _
        exact relabelFamily_symm σ A
      · intro A _
        exact np_relabel_symm' σ A
      · intro A _
        rw [← np_relabel_sdiff, ← relabel_forestBelow, ← relabel_forestBelow,
          np_forestUnion_relabel σ (hS₁ _) (hS₂ _), card_relabelFamily,
          card_relabelFamily]

private theorem np_relabel_side (σ : Equiv.Perm L) (ι : α → Finset (Finset L) → ℝ) :
    ∀ (S : Side α) (F G : Finset (Finset L)),
      S.forestDistOf (fun a H => ι a (relabelFamily σ.symm H)) (relabelFamily σ F)
          (relabelFamily σ G) =
        S.forestDistOf ι F G
  | .hyb ℓ, F, G => kingmanTransition_relabelFamily σ ℓ F G
  | .node ℓ b N S, F, G =>
      np_vecMul_relabel σ
        (np_forestUnion_relabel σ (np_relabel_side σ ι S F)
          (np_vecMul_relabel σ (np_relabel_net σ ι N) (kingmanTransition_relabelFamily σ b)))
        (kingmanTransition_relabelFamily σ ℓ) G
end

/-- Relabelling the lineages by `σ` (the inputs at the leaves pushed forward by `σ`) relabels the
distribution. -/
theorem Net.forestDistOf_relabel (σ : Equiv.Perm L) (ι : α → Finset (Finset L) → ℝ) (N : Net α)
    (G : Finset (Finset L)) :
    N.forestDistOf (fun a H => ι a (relabelFamily σ.symm H)) (relabelFamily σ G) =
      N.forestDistOf ι G :=
  np_relabel_net σ ι N G

theorem Side.forestDistOf_relabel (σ : Equiv.Perm L) (ι : α → Finset (Finset L) → ℝ)
    (S : Side α) (F G : Finset (Finset L)) :
    S.forestDistOf (fun a H => ι a (relabelFamily σ.symm H)) (relabelFamily σ F)
        (relabelFamily σ G) =
      S.forestDistOf ι F G :=
  np_relabel_side σ ι S F G

/-! ### Support and total mass, with given forests at the leaves -/

/-- `μ` is supported on good forests that contain `B` and have the lineages of `B`. -/
private abbrev np_GoodSupp (μ : Finset (Finset L) → ℝ) (B : Finset (Finset L)) : Prop :=
  ∀ G, μ G ≠ 0 → IsGoodForest G ∧ B ⊆ G ∧ lineages G = lineages B

omit [Fintype L] in
private theorem np_goodSupp_single {B : Finset (Finset L)} (hB : IsGoodForest B) :
    np_GoodSupp (Pi.single B 1) B := by
  intro G hG
  have hGB : G = B := by
    by_contra h
    exact hG (by rw [Pi.single_apply, ite_eq_right h])
  subst hGB
  exact ⟨hB, subset_rfl, rfl⟩

private theorem np_goodSupp_vecMul {μ : Finset (Finset L) → ℝ} {B : Finset (Finset L)}
    (h : np_GoodSupp μ B) (t : ℝ) : np_GoodSupp (μ ᵥ* kingmanTransition t) B := by
  intro G hG
  have hG' : ∑ H, μ H * kingmanTransition t H G ≠ 0 := hG
  obtain ⟨H, -, hH⟩ := exists_ne_zero_of_sum_ne_zero hG'
  obtain ⟨h1, h2, h3⟩ := h H (left_ne_zero_of_mul hH)
  obtain ⟨g1, g2, g3⟩ := kingmanTransition_support_good h1 (right_ne_zero_of_mul hH)
  exact ⟨g1, h2.trans g2, g3.trans h3⟩

private theorem np_forestUnion_ne_zero {μ ν : Finset (Finset L) → ℝ} {G : Finset (Finset L)}
    (h : forestUnion μ ν G ≠ 0) : ∃ F F', μ F ≠ 0 ∧ ν F' ≠ 0 ∧ F ∪ F' = G := by
  unfold forestUnion at h
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨F', -, hF'⟩ := exists_ne_zero_of_sum_ne_zero hF
  by_cases hU : F ∪ F' = G
  · rw [ite_eq_left hU] at hF'
    exact ⟨F, F', left_ne_zero_of_mul hF', right_ne_zero_of_mul hF', hU⟩
  · exact absurd (ite_eq_right hU) hF'

private theorem np_goodSupp_forestUnion {μ ν : Finset (Finset L) → ℝ}
    {B₁ B₂ : Finset (Finset L)} (hμ : np_GoodSupp μ B₁) (hν : np_GoodSupp ν B₂)
    (hd : Disjoint (lineages B₁) (lineages B₂)) :
    np_GoodSupp (forestUnion μ ν) (B₁ ∪ B₂) := by
  intro G hG
  obtain ⟨F, F', hF, hF', rfl⟩ := np_forestUnion_ne_zero hG
  obtain ⟨h1, h2, h3⟩ := hμ F hF
  obtain ⟨g1, g2, g3⟩ := hν F' hF'
  refine ⟨h1.union g1 (by rw [h3, g3]; exact hd), union_subset_union h2 g2, ?_⟩
  rw [lineages_union, lineages_union, h3, g3]

omit [Fintype L] in
private theorem np_lineages_forestBelow_subset (F A : Finset (Finset L)) :
    lineages (forestBelow F A) ⊆ lineages F :=
  lineages_mono (filter_subset _ _)

/-- The support at the top of a cycle, from the supports below the hybrid node and along the
sides. -/
private theorem np_goodSupp_cycle {γ : ℝ} {μ : Finset (Finset L) → ℝ}
    {K₁ K₂ : Finset (Finset L) → Finset (Finset L) → ℝ} {B B₁ B₂ : Finset (Finset L)}
    (hμ : np_GoodSupp μ B)
    (hK₁ : ∀ F, IsGoodForest F → Disjoint (lineages F) (lineages B₁) →
      np_GoodSupp (K₁ F) (F ∪ B₁))
    (hK₂ : ∀ F, IsGoodForest F → Disjoint (lineages F) (lineages B₂) →
      np_GoodSupp (K₂ F) (F ∪ B₂))
    (h₁ : Disjoint (lineages B) (lineages B₁))
    (h₂ : Disjoint (lineages B) (lineages B₂))
    (h₁₂ : Disjoint (lineages B₁) (lineages B₂)) :
    np_GoodSupp (fun G => ∑ F, μ F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (K₁ (forestBelow F A)) (K₂ (forestBelow F (roots F \ A))) G)
      (B₁ ∪ B₂ ∪ B) := by
  intro G hG
  obtain ⟨F, -, hF⟩ := exists_ne_zero_of_sum_ne_zero hG
  obtain ⟨A, hA, hFA⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hF)
  obtain ⟨f1, f2, f3⟩ := hμ F (left_ne_zero_of_mul hF)
  have hAr : A ⊆ roots F := mem_powerset.1 hA
  obtain ⟨hFU, hFd⟩ := forestBelow_union f1 hAr
  have hs₁ : lineages (forestBelow F A) ⊆ lineages B :=
    f3 ▸ np_lineages_forestBelow_subset F A
  have hs₂ : lineages (forestBelow F (roots F \ A)) ⊆ lineages B :=
    f3 ▸ np_lineages_forestBelow_subset F _
  have k₁ := hK₁ _ (isGoodForest_forestBelow f1) (h₁.mono_left hs₁)
  have k₂ := hK₂ _ (isGoodForest_forestBelow f1) (h₂.mono_left hs₂)
  have hd : Disjoint (lineages (forestBelow F A ∪ B₁))
      (lineages (forestBelow F (roots F \ A) ∪ B₂)) := by
    rw [lineages_union, lineages_union, disjoint_union_left, disjoint_union_right,
      disjoint_union_right]
    exact ⟨⟨hFd, h₂.mono_left hs₁⟩, h₁.symm.mono_right hs₂, h₁₂⟩
  obtain ⟨g1, g2, g3⟩ := np_goodSupp_forestUnion k₁ k₂ hd G (right_ne_zero_of_mul hFA)
  have hlin : lineages B =
      lineages (forestBelow F A) ∪ lineages (forestBelow F (roots F \ A)) := by
    rw [← f3, ← lineages_union, hFU]
  refine ⟨g1, fun C hC => g2 ?_, ?_⟩
  · rcases mem_union.1 hC with hC | hC
    · rcases mem_union.1 hC with hC | hC
      · exact mem_union_left _ (mem_union_right _ hC)
      · exact mem_union_right _ (mem_union_right _ hC)
    · have hCF : C ∈ forestBelow F A ∪ forestBelow F (roots F \ A) := by
        rw [hFU]
        exact f2 hC
      rcases mem_union.1 hCF with hC' | hC'
      · exact mem_union_left _ (mem_union_left _ hC')
      · exact mem_union_right _ (mem_union_left _ hC')
  · rw [g3, lineages_union, lineages_union, lineages_union, lineages_union, lineages_union, hlin]
    ext x
    simp only [mem_union]
    tauto

section Leaves

variable [DecidableEq α]

/-- The union of the forests at the leaves `l`. -/
private def np_B (E : α → Finset (Finset L)) (l : List α) : Finset (Finset L) :=
  l.toFinset.biUnion E

/-- The hypotheses on the forests at the leaves `l`: distinct leaves, good forests, pairwise
disjoint lineages. -/
private abbrev np_Ok (E : α → Finset (Finset L)) (l : List α) : Prop :=
  l.Nodup ∧ (∀ a ∈ l, IsGoodForest (E a)) ∧
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → Disjoint (lineages (E a)) (lineages (E b))

omit [Fintype L] in
private theorem np_B_append (E : α → Finset (Finset L)) (l₁ l₂ : List α) :
    np_B E (l₁ ++ l₂) = np_B E l₁ ∪ np_B E l₂ := by
  simp only [np_B, List.toFinset_append, union_biUnion]

omit [Fintype L] in
private theorem np_B_singleton (E : α → Finset (Finset L)) (a : α) : np_B E [a] = E a := by
  simp [np_B]

omit [Fintype L] in
private theorem np_B_nil (E : α → Finset (Finset L)) : np_B E [] = ∅ := by
  simp [np_B]

omit [Fintype L] in
private theorem np_lineages_B (E : α → Finset (Finset L)) (l : List α) :
    lineages (np_B E l) = l.toFinset.biUnion fun a => lineages (E a) := by
  ext x
  simp only [np_B, mem_lineages, mem_biUnion]
  constructor
  · rintro ⟨A, ⟨a, ha, hA⟩, hx⟩
    exact ⟨a, ha, A, hA, hx⟩
  · rintro ⟨a, ha, A, hA, hx⟩
    exact ⟨A, ⟨a, ha, hA⟩, hx⟩

omit [Fintype L] [DecidableEq α] in
private theorem np_ok_left {E : α → Finset (Finset L)} {l₁ l₂ : List α}
    (h : np_Ok E (l₁ ++ l₂)) : np_Ok E l₁ :=
  ⟨(List.nodup_append.1 h.1).1, fun a ha => h.2.1 a (List.mem_append_left _ ha),
    fun a ha b hb => h.2.2 a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)⟩

omit [Fintype L] [DecidableEq α] in
private theorem np_ok_right {E : α → Finset (Finset L)} {l₁ l₂ : List α}
    (h : np_Ok E (l₁ ++ l₂)) : np_Ok E l₂ :=
  ⟨(List.nodup_append.1 h.1).2.1, fun a ha => h.2.1 a (List.mem_append_right _ ha),
    fun a ha b hb => h.2.2 a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)⟩

omit [Fintype L] in
private theorem np_ok_disjoint {E : α → Finset (Finset L)} {l₁ l₂ : List α}
    (h : np_Ok E (l₁ ++ l₂)) :
    Disjoint (lineages (np_B E l₁)) (lineages (np_B E l₂)) := by
  rw [np_lineages_B, np_lineages_B, disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  have ha' := List.mem_toFinset.1 ha
  have hb' := List.mem_toFinset.1 hb
  exact h.2.2 a (List.mem_append_left _ ha') b (List.mem_append_right _ hb')
    ((List.nodup_append.1 h.1).2.2 a ha' b hb')

mutual
private theorem np_supp_net (E : α → Finset (Finset L)) :
    ∀ N : Net α, np_Ok E N.leaves →
      np_GoodSupp (N.forestDistOf fun a => Pi.single (E a) 1) (np_B E N.leaves)
  | .leaf a, h => by
      simp only [Net.leaves, Net.forestDistOf]
      rw [np_B_singleton]
      exact np_goodSupp_single (h.2.1 a (List.mem_singleton_self a))
  | .tree ℓ₁ N₁ ℓ₂ N₂, h => by
      have h' : np_Ok E (N₁.leaves ++ N₂.leaves) := h
      simp only [Net.leaves, Net.forestDistOf]
      rw [np_B_append]
      exact np_goodSupp_forestUnion (np_goodSupp_vecMul (np_supp_net E N₁ (np_ok_left h')) ℓ₁)
        (np_goodSupp_vecMul (np_supp_net E N₂ (np_ok_right h')) ℓ₂) (np_ok_disjoint h')
  | .cycle γ S₁ S₂ ℓ N, h => by
      have h' : np_Ok E (S₁.leaves ++ S₂.leaves ++ N.leaves) := h
      have h12 := np_ok_left h'
      have hd := np_ok_disjoint h'
      rw [np_B_append, lineages_union, disjoint_union_left] at hd
      simp only [Net.leaves, Net.forestDistOf]
      rw [np_B_append, np_B_append]
      exact np_goodSupp_cycle (np_goodSupp_vecMul (np_supp_net E N (np_ok_right h')) ℓ)
        (np_supp_side E S₁ (np_ok_left h12)) (np_supp_side E S₂ (np_ok_right h12))
        hd.1.symm hd.2.symm (np_ok_disjoint h12)

private theorem np_supp_side (E : α → Finset (Finset L)) :
    ∀ S : Side α, np_Ok E S.leaves → ∀ F, IsGoodForest F →
      Disjoint (lineages F) (lineages (np_B E S.leaves)) →
      np_GoodSupp (S.forestDistOf (fun a => Pi.single (E a) 1) F) (F ∪ np_B E S.leaves)
  | .hyb ℓ, _, F, hF, _ => by
      simp only [Side.leaves, Side.forestDistOf]
      rw [np_B_nil, union_empty]
      exact fun G hG => kingmanTransition_support_good hF hG
  | .node ℓ b N S, h, F, hF, hFd => by
      have h' : np_Ok E (N.leaves ++ S.leaves) := h
      have hFd' : Disjoint (lineages F)
          (lineages (np_B E (N.leaves ++ S.leaves))) := hFd
      rw [np_B_append, lineages_union, disjoint_union_right] at hFd'
      have key := np_goodSupp_forestUnion (np_supp_side E S (np_ok_right h') F hF hFd'.2)
        (np_goodSupp_vecMul (np_supp_net E N (np_ok_left h')) b) (by
          rw [lineages_union, disjoint_union_left]
          exact ⟨hFd'.1, (np_ok_disjoint h').symm⟩)
      have heq : F ∪ np_B E (N.leaves ++ S.leaves) = F ∪ np_B E S.leaves ∪ np_B E N.leaves := by
        rw [np_B_append]
        ext x
        simp only [mem_union]
        tauto
      simp only [Side.leaves, Side.forestDistOf]
      rw [heq]
      exact np_goodSupp_vecMul key ℓ
end

private theorem np_sum_single (B : Finset (Finset L)) :
    ∑ G, (Pi.single B 1 : Finset (Finset L) → ℝ) G = 1 := by
  simp

private theorem np_sum_vecMul {μ : Finset (Finset L) → ℝ}
    (hμ : ∀ H, μ H ≠ 0 → IsForest H) (t : ℝ) :
    ∑ G, (μ ᵥ* kingmanTransition t) G = ∑ H, μ H := by
  simp only [vecMul, dotProduct]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  rw [← mul_sum]
  by_cases h : μ H = 0
  · rw [h, zero_mul]
  · rw [kingmanTransition_sum (hμ H h), mul_one]

private theorem np_sum_forestUnion (μ ν : Finset (Finset L) → ℝ) :
    ∑ G, forestUnion μ ν G = (∑ F, μ F) * ∑ F', ν F' := by
  simp only [forestUnion]
  rw [sum_comm, sum_mul_sum]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun F' _ => ?_
  simp

omit [Fintype L] [DecidableEq α] in
private theorem np_sum_powerset_weights (γ : ℝ) (s : Finset (Finset L)) :
    ∑ A ∈ s.powerset, γ ^ #A * (1 - γ) ^ #(s \ A) = 1 := by
  have h := sum_pow_mul_eq_add_pow γ (1 - γ) s
  rw [show γ + (1 - γ) = 1 by ring, one_pow] at h
  refine (sum_congr rfl fun A hA => ?_).trans h
  rw [card_sdiff_of_subset (mem_powerset.1 hA)]

mutual
private theorem np_sum_net (E : α → Finset (Finset L)) :
    ∀ N : Net α, np_Ok E N.leaves → ∑ G, N.forestDistOf (fun a => Pi.single (E a) 1) G = 1
  | .leaf a, _ => np_sum_single (E a)
  | .tree ℓ₁ N₁ ℓ₂ N₂, h => by
      have h' : np_Ok E (N₁.leaves ++ N₂.leaves) := h
      simp only [Net.forestDistOf]
      rw [np_sum_forestUnion,
        np_sum_vecMul (fun H hH => (np_supp_net E N₁ (np_ok_left h') H hH).1.1),
        np_sum_vecMul (fun H hH => (np_supp_net E N₂ (np_ok_right h') H hH).1.1),
        np_sum_net E N₁ (np_ok_left h'), np_sum_net E N₂ (np_ok_right h'), one_mul]
  | .cycle γ S₁ S₂ ℓ N, h => by
      have h' : np_Ok E (S₁.leaves ++ S₂.leaves ++ N.leaves) := h
      have h12 := np_ok_left h'
      have hd := np_ok_disjoint h'
      rw [np_B_append, lineages_union, disjoint_union_left] at hd
      have hsupp := np_goodSupp_vecMul (np_supp_net E N (np_ok_right h')) ℓ
      have hμ :
          ∑ F, (N.forestDistOf (fun a => Pi.single (E a) 1) ᵥ* kingmanTransition ℓ) F = 1 := by
        rw [np_sum_vecMul (fun H hH => (np_supp_net E N (np_ok_right h') H hH).1.1),
          np_sum_net E N (np_ok_right h')]
      simp only [Net.forestDistOf]
      rw [sum_comm]
      refine (sum_congr rfl fun F _ => ?_).trans hμ
      rw [← mul_sum]
      by_cases hF : (N.forestDistOf (fun a => Pi.single (E a) 1) ᵥ* kingmanTransition ℓ) F = 0
      · rw [hF, zero_mul]
      obtain ⟨f1, -, f3⟩ := hsupp F hF
      have hw : ∑ A ∈ (roots F).powerset, ∑ G, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
          forestUnion (S₁.forestDistOf (fun a => Pi.single (E a) 1) (forestBelow F A))
            (S₂.forestDistOf (fun a => Pi.single (E a) 1) (forestBelow F (roots F \ A))) G = 1 := by
        refine (sum_congr rfl fun A hA => ?_).trans (np_sum_powerset_weights γ (roots F))
        have hAr := mem_powerset.1 hA
        rw [← mul_sum, np_sum_forestUnion,
          np_sum_side E S₁ (np_ok_left h12) _ (isGoodForest_forestBelow f1)
            (hd.1.symm.mono_left (f3 ▸ np_lineages_forestBelow_subset F A)),
          np_sum_side E S₂ (np_ok_right h12) _ (isGoodForest_forestBelow f1)
            (hd.2.symm.mono_left (f3 ▸ np_lineages_forestBelow_subset F _)),
          mul_one, mul_one]
      rw [sum_comm, hw, mul_one]

private theorem np_sum_side (E : α → Finset (Finset L)) :
    ∀ S : Side α, np_Ok E S.leaves → ∀ F, IsGoodForest F →
      Disjoint (lineages F) (lineages (np_B E S.leaves)) →
      ∑ G, S.forestDistOf (fun a => Pi.single (E a) 1) F G = 1
  | .hyb ℓ, _, F, hF, _ => kingmanTransition_sum hF.1 ℓ
  | .node ℓ b N S, h, F, hF, hFd => by
      have h' : np_Ok E (N.leaves ++ S.leaves) := h
      have hFd' : Disjoint (lineages F)
          (lineages (np_B E (N.leaves ++ S.leaves))) := hFd
      rw [np_B_append, lineages_union, disjoint_union_right] at hFd'
      have key := np_goodSupp_forestUnion (np_supp_side E S (np_ok_right h') F hF hFd'.2)
        (np_goodSupp_vecMul (np_supp_net E N (np_ok_left h')) b) (by
          rw [lineages_union, disjoint_union_left]
          exact ⟨hFd'.1, (np_ok_disjoint h').symm⟩)
      simp only [Side.forestDistOf]
      rw [np_sum_vecMul (fun H hH => (key H hH).1.1), np_sum_forestUnion,
        np_sum_side E S (np_ok_right h') F hF hFd'.2,
        np_sum_vecMul (fun H hH => (np_supp_net E N (np_ok_left h') H hH).1.1),
        np_sum_net E N (np_ok_left h'), one_mul]
end

end Leaves

/-- With good forests on pairwise disjoint lineages at the (distinct) leaves, the network
coalescent produces good forests that contain the forests of the leaves, on the union of their
lineages. -/
theorem Net.forestDistOf_single_support [DecidableEq α] (N : Net α) (hN : N.leaves.Nodup)
    (E : α → Finset (Finset L)) (hE : ∀ a ∈ N.leaves, IsGoodForest (E a))
    (hdisj : ∀ a ∈ N.leaves, ∀ b ∈ N.leaves, a ≠ b →
      Disjoint (lineages (E a)) (lineages (E b)))
    {G : Finset (Finset L)} (hG : N.forestDistOf (fun a => Pi.single (E a) 1) G ≠ 0) :
    IsGoodForest G ∧ (∀ a ∈ N.leaves, E a ⊆ G) ∧
      lineages G = N.leaves.toFinset.biUnion fun a => lineages (E a) := by
  obtain ⟨h1, h2, h3⟩ := np_supp_net E N ⟨hN, hE, hdisj⟩ G hG
  refine ⟨h1, fun a ha => (subset_biUnion_of_mem E (List.mem_toFinset.2 ha)).trans h2, ?_⟩
  rw [h3, np_lineages_B]

theorem Net.forestDistOf_single_sum [DecidableEq α] (N : Net α) (hN : N.leaves.Nodup)
    (E : α → Finset (Finset L)) (hE : ∀ a ∈ N.leaves, IsGoodForest (E a))
    (hdisj : ∀ a ∈ N.leaves, ∀ b ∈ N.leaves, a ≠ b →
      Disjoint (lineages (E a)) (lineages (E b))) :
    ∑ G, N.forestDistOf (fun a => Pi.single (E a) 1) G = 1 :=
  np_sum_net E N ⟨hN, hE, hdisj⟩

/-- The same along a side, with a good forest `F` taking the hybrid edge at its bottom. -/
theorem Side.forestDistOf_single_support [DecidableEq α] (S : Side α) (hS : S.leaves.Nodup)
    (E : α → Finset (Finset L)) (hE : ∀ a ∈ S.leaves, IsGoodForest (E a))
    (hdisj : ∀ a ∈ S.leaves, ∀ b ∈ S.leaves, a ≠ b →
      Disjoint (lineages (E a)) (lineages (E b)))
    {F : Finset (Finset L)} (hF : IsGoodForest F)
    (hFdisj : ∀ a ∈ S.leaves, Disjoint (lineages F) (lineages (E a)))
    {G : Finset (Finset L)} (hG : S.forestDistOf (fun a => Pi.single (E a) 1) F G ≠ 0) :
    IsGoodForest G ∧ F ⊆ G ∧ (∀ a ∈ S.leaves, E a ⊆ G) ∧
      lineages G =
        lineages F ∪ S.leaves.toFinset.biUnion fun a => lineages (E a) := by
  have hd : Disjoint (lineages F) (lineages (np_B E S.leaves)) := by
    rw [np_lineages_B, disjoint_biUnion_right]
    exact fun a ha => hFdisj a (List.mem_toFinset.1 ha)
  obtain ⟨h1, h2, h3⟩ := np_supp_side E S ⟨hS, hE, hdisj⟩ F hF hd G hG
  refine ⟨h1, subset_union_left.trans h2, fun a ha =>
    ((subset_biUnion_of_mem E (List.mem_toFinset.2 ha)).trans subset_union_right).trans h2, ?_⟩
  rw [h3, lineages_union, np_lineages_B]

theorem Side.forestDistOf_single_sum [DecidableEq α] (S : Side α) (hS : S.leaves.Nodup)
    (E : α → Finset (Finset L)) (hE : ∀ a ∈ S.leaves, IsGoodForest (E a))
    (hdisj : ∀ a ∈ S.leaves, ∀ b ∈ S.leaves, a ≠ b →
      Disjoint (lineages (E a)) (lineages (E b)))
    {F : Finset (Finset L)} (hF : IsGoodForest F)
    (hFdisj : ∀ a ∈ S.leaves, Disjoint (lineages F) (lineages (E a))) :
    ∑ G, S.forestDistOf (fun a => Pi.single (E a) 1) F G = 1 := by
  have hd : Disjoint (lineages F) (lineages (np_B E S.leaves)) := by
    rw [np_lineages_B, disjoint_biUnion_right]
    exact fun a ha => hFdisj a (List.mem_toFinset.1 ha)
  exact np_sum_side E S ⟨hS, hE, hdisj⟩ F hF hd

/-! ### Networks with at most one sampled lineage -/

/-- The forest of the singletons of the lineages sampled from the taxa of `N`. -/
def Net.sampledForest {X : Type u} [DecidableEq X] (s : L → X) (N : Net X) :
    Finset (Finset L) :=
  (univ.filter fun l => s l ∈ N.taxa).image fun l => {l}

omit [Fintype L] in
private theorem np_forestBelow_empty (F : Finset (Finset L)) : forestBelow F ∅ = ∅ := by
  unfold forestBelow
  simp

omit [Fintype L] in
private theorem np_forestBelow_singleton (C : Finset L) : forestBelow {C} {C} = {C} := by
  unfold forestBelow
  simp

private theorem np_roots_singleton (C : Finset L) : roots ({C} : Finset (Finset L)) = {C} := by
  refine Subset.antisymm (roots_subset _) fun A hA => ?_
  rw [mem_singleton] at hA
  subst hA
  exact mem_roots.2 ⟨mem_singleton_self A, fun B hB _ => mem_singleton.1 hB⟩

omit [Fintype L] in
private theorem np_powerset_singleton (C : Finset L) :
    ({C} : Finset (Finset L)).powerset = {∅, {C}} := by
  ext A
  simp [subset_singleton_iff]

/-- A cycle whose hybrid node receives a deterministic forest of at most one lineage. -/
private theorem np_cycle_of_single {X : Type*} [DecidableEq X] (s : L → X) (γ ℓ : ℝ)
    (S₁ S₂ : Side X) (N : Net X) (E : Finset (Finset L)) (hE : E = ∅ ∨ ∃ l, E = {{l}})
    (hN : N.forestDist s ᵥ* kingmanTransition ℓ = Pi.single E 1) :
    (Net.cycle γ S₁ S₂ ℓ N).forestDist s =
      γ • forestUnion (S₁.forestDist s E) (S₂.forestDist s ∅) +
        (1 - γ) • forestUnion (S₁.forestDist s ∅) (S₂.forestDist s E) := by
  funext G
  simp only [Net.forestDist, hN, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single E fun F hF => by rw [Pi.single_apply, ite_eq_right hF, zero_mul],
    Pi.single_eq_same, one_mul]
  rcases hE with rfl | ⟨l, rfl⟩
  · rw [roots_empty, powerset_empty, sum_singleton, sdiff_self,
      bot_eq_empty, np_forestBelow_empty, card_empty, pow_zero, pow_zero]
    ring
  · rw [np_roots_singleton, np_powerset_singleton,
      sum_pair (by simp : (∅ : Finset (Finset L)) ≠ {{l}}), sdiff_empty, sdiff_self,
      bot_eq_empty, np_forestBelow_empty, np_forestBelow_singleton, card_empty,
      card_singleton, pow_zero, pow_one, pow_zero, pow_one]
    ring

/-- The lineages sampled from the taxa in the list `l`. -/
private def np_T {X : Type*} [DecidableEq X] (s : L → X) (l : List X) : Finset L :=
  univ.filter fun x => s x ∈ l.toFinset

/-- The forest of the singletons of a set of lineages. -/
private abbrev np_sf (T : Finset L) : Finset (Finset L) :=
  T.image fun l => {l}

omit [Fintype L] in
private theorem np_sf_empty : np_sf (∅ : Finset L) = ∅ :=
  image_empty _

omit [Fintype L] in
private theorem np_sf_singleton (l : L) : np_sf {l} = {{l}} :=
  image_singleton _ _

omit [Fintype L] in
private theorem np_sf_union (T₁ T₂ : Finset L) : np_sf (T₁ ∪ T₂) = np_sf T₁ ∪ np_sf T₂ :=
  image_union _ _

private theorem np_T_append {X : Type*} [DecidableEq X] (s : L → X) (l₁ l₂ : List X) :
    np_T s (l₁ ++ l₂) = np_T s l₁ ∪ np_T s l₂ := by
  ext x
  simp [np_T]

omit [DecidableEq L] in
private theorem np_T_nil {X : Type*} [DecidableEq X] (s : L → X) : np_T s [] = ∅ := by
  ext x
  simp [np_T]

private theorem np_sampledAt_eq {X : Type*} [DecidableEq X] (s : L → X) (x : X) :
    sampledAt s x = np_sf (np_T s [x]) := by
  unfold sampledAt np_sf np_T
  congr 1
  ext l
  simp

private theorem np_kT_sf {T : Finset L} (h : #T ≤ 1) (t : ℝ) :
    Pi.single (np_sf T) 1 ᵥ* kingmanTransition t = Pi.single (np_sf T) 1 :=
  single_vecMul_kingmanTransition (isGoodForest_singletons T).1
    ((card_le_card (roots_subset _)).trans (card_image_le.trans h)) t

private theorem np_kT_row_sf {T : Finset L} (h : #T ≤ 1) (t : ℝ) :
    kingmanTransition t (np_sf T) = Pi.single (np_sf T) 1 := by
  have := np_kT_sf h t
  rwa [single_one_vecMul, row_apply'] at this

mutual
private theorem np_one_net {X : Type*} [DecidableEq X] (s : L → X) :
    ∀ N : Net X, #(np_T s N.leaves) ≤ 1 →
      N.forestDist s = Pi.single (np_sf (np_T s N.leaves)) 1
  | .leaf x, _ => by
      show (fun G => if G = sampledAt s x then 1 else 0) = Pi.single (np_sf (np_T s [x])) 1
      rw [← np_sampledAt_eq]
      funext G
      rw [Pi.single_apply]
  | .tree ℓ₁ N₁ ℓ₂ N₂, h => by
      have hT : np_T s (Net.tree ℓ₁ N₁ ℓ₂ N₂).leaves = np_T s N₁.leaves ∪ np_T s N₂.leaves :=
        np_T_append s _ _
      rw [hT] at h ⊢
      have h₁ : #(np_T s N₁.leaves) ≤ 1 := (card_le_card subset_union_left).trans h
      have h₂ : #(np_T s N₂.leaves) ≤ 1 := (card_le_card subset_union_right).trans h
      simp only [Net.forestDist]
      rw [np_one_net s N₁ h₁, np_one_net s N₂ h₂, np_kT_sf h₁, np_kT_sf h₂,
        forestUnion_single_single, ← np_sf_union]
  | .cycle γ S₁ S₂ ℓ N, h => by
      have hT : np_T s (Net.cycle γ S₁ S₂ ℓ N).leaves =
          np_T s S₁.leaves ∪ np_T s S₂.leaves ∪ np_T s N.leaves := by
        show np_T s (S₁.leaves ++ S₂.leaves ++ N.leaves) = _
        rw [np_T_append, np_T_append]
      rw [hT] at h ⊢
      have hN : #(np_T s N.leaves) ≤ 1 := (card_le_card subset_union_right).trans h
      have hE : np_sf (np_T s N.leaves) = ∅ ∨ ∃ l, np_sf (np_T s N.leaves) = {{l}} := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hN with h0 | h1
        · left
          rw [card_eq_zero.1 h0, np_sf_empty]
        · right
          obtain ⟨l, hl⟩ := card_eq_one.1 h1
          exact ⟨l, by rw [hl, np_sf_singleton]⟩
      rw [np_cycle_of_single s γ ℓ S₁ S₂ N _ hE (by rw [np_one_net s N hN, np_kT_sf hN])]
      have hc : ∀ {A B : Finset L}, A ⊆ np_T s S₁.leaves ∪ np_T s S₂.leaves ∪ np_T s N.leaves →
          B = A → #B ≤ 1 := fun hA hB => hB ▸ (card_le_card hA).trans h
      have e1 := np_one_side s S₁ (np_T s N.leaves)
        (hc (union_subset subset_union_right (subset_union_left.trans subset_union_left)) rfl)
      have e2 := np_one_side s S₂ ∅
        (hc (union_subset (empty_subset _) (subset_union_right.trans subset_union_left)) rfl)
      have e3 := np_one_side s S₁ ∅
        (hc (union_subset (empty_subset _) (subset_union_left.trans subset_union_left)) rfl)
      have e4 := np_one_side s S₂ (np_T s N.leaves)
        (hc (union_subset subset_union_right (subset_union_right.trans subset_union_left)) rfl)
      rw [np_sf_empty] at e2 e3
      have u₁ : np_T s N.leaves ∪ np_T s S₁.leaves ∪ (∅ ∪ np_T s S₂.leaves) =
          np_T s S₁.leaves ∪ np_T s S₂.leaves ∪ np_T s N.leaves := by
        ext x
        simp only [mem_union, notMem_empty, false_or]
        tauto
      have u₂ : ∅ ∪ np_T s S₁.leaves ∪ (np_T s N.leaves ∪ np_T s S₂.leaves) =
          np_T s S₁.leaves ∪ np_T s S₂.leaves ∪ np_T s N.leaves := by
        ext x
        simp only [mem_union, notMem_empty, false_or]
        tauto
      rw [e1, e2, e3, e4, forestUnion_single_single, forestUnion_single_single, ← np_sf_union,
        ← np_sf_union, u₁, u₂, ← add_smul, show γ + (1 - γ) = 1 by ring, one_smul]

private theorem np_one_side {X : Type*} [DecidableEq X] (s : L → X) :
    ∀ (S : Side X) (T₀ : Finset L), #(T₀ ∪ np_T s S.leaves) ≤ 1 →
      S.forestDist s (np_sf T₀) = Pi.single (np_sf (T₀ ∪ np_T s S.leaves)) 1
  | .hyb ℓ, T₀, h => by
      have hT : np_T s (Side.hyb ℓ : Side X).leaves = ∅ := np_T_nil s
      rw [hT, union_empty] at h ⊢
      exact np_kT_row_sf h ℓ
  | .node ℓ b N S, T₀, h => by
      have hT : np_T s (Side.node ℓ b N S).leaves = np_T s N.leaves ∪ np_T s S.leaves :=
        np_T_append s _ _
      rw [hT] at h ⊢
      have hS : #(T₀ ∪ np_T s S.leaves) ≤ 1 :=
        (card_le_card (union_subset_union_right subset_union_right)).trans h
      have hN : #(np_T s N.leaves) ≤ 1 :=
        (card_le_card (subset_union_left.trans subset_union_right)).trans h
      have u : T₀ ∪ np_T s S.leaves ∪ np_T s N.leaves =
          T₀ ∪ (np_T s N.leaves ∪ np_T s S.leaves) := by
        ext x
        simp only [mem_union]
        tauto
      simp only [Side.forestDist]
      rw [np_one_side s S T₀ hS, np_one_net s N hN, np_kT_sf hN, forestUnion_single_single,
        ← np_sf_union, u, np_kT_sf h]
end

/-- If at most one lineage is sampled from the taxa of `N`, it reaches the root of `N`
unchanged. -/
theorem Net.forestDist_of_card_le_one {X : Type u} [DecidableEq X] (N : Net X) (s : L → X)
    (h : #(univ.filter fun l => s l ∈ N.taxa) ≤ 1) :
    N.forestDist s = Pi.single (N.sampledForest s) 1 :=
  np_one_net s N h

/-- A cycle whose hybrid node receives (deterministically) at most one lineage: the lineage
takes the side `S₁` with probability `γ` and the side `S₂` with probability `1 - γ`. -/
theorem Net.forestDist_cycle_of_single {X : Type u} [DecidableEq X] (s : L → X) (γ ℓ : ℝ)
    (S₁ S₂ : Side X) (N : Net X) (E : Finset (Finset L)) (hE : E = ∅ ∨ ∃ l, E = {{l}})
    (hN : N.forestDist s ᵥ* kingmanTransition ℓ = Pi.single E 1) :
    (Net.cycle γ S₁ S₂ ℓ N).forestDist s =
      γ • forestUnion (S₁.forestDist s E) (S₂.forestDist s ∅) +
        (1 - γ) • forestUnion (S₁.forestDist s ∅) (S₂.forestDist s E) :=
  np_cycle_of_single s γ ℓ S₁ S₂ N E hE hN

end Phylogenetics
