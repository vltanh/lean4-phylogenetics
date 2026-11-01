module

public import Phylogenetics.Tree.Splits

/-!
# The constrained dynamic program of ASTRAL

After Mirarab, Reaz, Bayzid, Zimmermann, Swenson, Warnow, *ASTRAL: genome-scale coalescent-based species
tree estimation*, Bioinformatics 30 (2014), i541-i548, Section 2 ("Approach"). A quartet tree displayed on
a binary tree is "associated to the pair of nodes" at the two ends of the path between its cherries, and
deleting such a node gives a tripartition `(A|B|C)` of the taxa, with weight `W(A|B|C)`. "Because each
quartet is associated to exactly two nodes", the sum of the weights over the nodes is twice the quartet
score. The dynamic program, for a set `X*` of clusters (the sides of the allowed bipartitions), is
`C(A) = max {C(A') + C(A - A') + W(A'|A - A'|S - A)}` over `A' ⊂ A` with `A', A - A' ∈ X*`, with the boundary
condition `C({x}) = 0` and `W = 0` when `A = S`. "At the end of the algorithm, `C(S)` gives the final score,
and backtracking gives the final tree", which by their Theorem 1 is an optimal solution of the
problem constrained to the allowed bipartitions.

Here:

* `tripartitionWeight` is `W`, for any weights `w : QuartetTree X → ℝ`; `nodeWeight` is its value at a node of a
  hierarchy (`nodeWeight_eq_tripartitionWeight`);
* `IsHierarchy.card_filter_isAnchorOf` is "each quartet is associated to exactly two nodes", and
  `two_mul_quartetSupport_unroot`, `two_mul_quartetSupport_eq_sum_tripartitionWeight` and
  `IsBinaryTree.exists_two_mul_quartetSupport` are the resulting identity;
* `IsBinaryClusterTree 𝒞 C R` says that `R` is a binary rooted tree on the taxa `C` with clusters in `𝒞`;
* `astralValue` is the recursion `C(·)` (with values in `WithBot ℝ`, `⊥` when `A` has no tree),
  `IsTraceback` is backtracking under any rule for breaking ties, and `astralTrace` is one such rule;
* `astralValue_eq_max` is the correctness of the recursion over clusters, and `IsTraceback.isAstralOptimal`,
  `astralTree_isAstralOptimal` are that Theorem 1 (its optimality part): the output is an optimum of
  `quartetSupport` among the binary trees with sides in `𝒞`.

Running times, and the computation of `W` from the gene trees without listing quartets, are not treated.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Tripartitions and their weights -/

/-- `s` is the quartet tree `ab|cd` with `a ∈ A`, `b ∈ B` and `c, d ∈ C`. -/
def IsSplitBy (A B C : Finset X) (s : QuartetTree X) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ({a, b} : Finset X) ∈ s.val ∧ s.taxa \ {a, b} ⊆ C

/-- The quartet tree `s` is associated to the tripartition `(A|B|C)` (Mirarab et al. 2014, Section 2): one
cherry has its taxa in two of the parts, and the other cherry lies in the third part. -/
def IsAnchoredAt (A B C : Finset X) (s : QuartetTree X) : Prop :=
  IsSplitBy A B C s ∨ IsSplitBy B C A s ∨ IsSplitBy C A B s

/-- The weight `W(A|B|C)` of a tripartition (Mirarab et al. 2014, Section 2): the total weight of the quartet
trees associated to it. -/
def tripartitionWeight (w : QuartetTree X → ℝ) (A B C : Finset X) : ℝ :=
  ∑ s, if IsAnchoredAt A B C s then w s else 0

omit [Fintype X] in
theorem isSplitBy_comm (A B C : Finset X) (s : QuartetTree X) :
    IsSplitBy A B C s ↔ IsSplitBy B A C s := by
  constructor <;> rintro ⟨a, ha, b, hb, h, h'⟩ <;>
    exact ⟨b, hb, a, ha, by rwa [pair_comm], by rwa [pair_comm]⟩

omit [Fintype X] in
theorem isAnchoredAt_comm (A B C : Finset X) (s : QuartetTree X) :
    IsAnchoredAt A B C s ↔ IsAnchoredAt B A C s := by
  unfold IsAnchoredAt
  rw [isSplitBy_comm A B C, isSplitBy_comm B C A, isSplitBy_comm C A B]
  tauto

omit [Fintype X] in
theorem isAnchoredAt_rotate (A B C : Finset X) (s : QuartetTree X) :
    IsAnchoredAt A B C s ↔ IsAnchoredAt B C A s := by
  unfold IsAnchoredAt
  tauto

/-- The weight of a tripartition does not depend on the order of the first two parts. -/
theorem tripartitionWeight_comm (w : QuartetTree X → ℝ) (A B C : Finset X) :
    tripartitionWeight w A B C = tripartitionWeight w B A C := by
  simp only [tripartitionWeight, isAnchoredAt_comm A B C]

/-- The weight of a tripartition is invariant under rotating its parts. -/
theorem tripartitionWeight_rotate (w : QuartetTree X → ℝ) (A B C : Finset X) :
    tripartitionWeight w A B C = tripartitionWeight w B C A := by
  simp only [tripartitionWeight, isAnchoredAt_rotate A B C]

/-- No quartet tree is associated to a "tripartition" with an empty third part. This is why Mirarab et al. can
"set `W(A'|A - A'|S - A) = 0`" for the special case `A = S`; here that is a theorem, not a convention. -/
theorem tripartitionWeight_empty (w : QuartetTree X → ℝ) (A B : Finset X) :
    tripartitionWeight w A B ∅ = 0 := by
  refine sum_eq_zero fun s _ => ite_eq_right ?_
  rintro (⟨a, -, b, -, -, h⟩ | ⟨-, -, x, hx, -⟩ | ⟨x, hx, -⟩)
  · have h1 := card_le_card (sdiff_eq_empty_iff_subset.1 (subset_empty.1 h))
    rw [s.card_taxa] at h1
    have h2 : ({a, b} : Finset X).card ≤ 2 := card_le_two
    omega
  · simp at hx
  · simp at hx

/-! ### The anchors of a quartet tree on a binary hierarchy -/

/-- The cluster `U` of `H` is an anchor of the quartet tree `s`: `s` is associated to the tripartition of `U` into
two of its children and the complement `Uᶜ`. -/
def IsAnchorOf (H : Finset (Finset X)) (U : Finset X) (s : QuartetTree X) : Prop :=
  ∃ A ∈ childClusters H U, ∃ B ∈ childClusters H U, A ≠ B ∧ IsAnchoredAt A B Uᶜ s

/-- The weight of a node of a tree: the total weight of the quartet trees anchored there. -/
def nodeWeight (w : QuartetTree X → ℝ) (H : Finset (Finset X)) (U : Finset X) : ℝ :=
  ∑ s, if IsAnchorOf H U s then w s else 0

/-- At a node with children `A` and `B`, the weight is that of the tripartition `(A|B|Uᶜ)`. -/
theorem nodeWeight_eq_tripartitionWeight (w : QuartetTree X → ℝ) {H : Finset (Finset X)}
    {U A B : Finset X} (hne : A ≠ B) (h : childClusters H U = {A, B}) :
    nodeWeight w H U = tripartitionWeight w A B Uᶜ := by
  refine sum_congr rfl fun s _ => if_congr ?_ rfl rfl
  rw [IsAnchorOf, h]
  constructor
  · rintro ⟨A', hA', B', hB', hne', hs⟩
    simp only [mem_insert, mem_singleton] at hA' hB'
    rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl
    · exact absurd rfl hne'
    · exact hs
    · exact (isAnchoredAt_comm _ _ _ _).1 hs
    · exact absurd rfl hne'
  · exact fun hs => ⟨A, by simp, B, by simp, hne, hs⟩

/-- A node without children has weight zero. -/
theorem nodeWeight_eq_zero (w : QuartetTree X → ℝ) {H : Finset (Finset X)} {U : Finset X}
    (h : childClusters H U = ∅) : nodeWeight w H U = 0 := by
  refine sum_eq_zero fun s _ => ite_eq_right ?_
  rintro ⟨A, hA, -⟩
  simp [h] at hA

/-- The weight of a node depends only on its children. -/
theorem nodeWeight_congr (w : QuartetTree X → ℝ) {H H' : Finset (Finset X)} {U : Finset X}
    (h : childClusters H U = childClusters H' U) : nodeWeight w H U = nodeWeight w H' U := by
  refine sum_congr rfl fun s _ => if_congr ?_ rfl rfl
  rw [IsAnchorOf, IsAnchorOf, h]

/-- `U` is the anchor of the cherry `P`, the other cherry being `Q`: the taxa of `P` lie in two parts at `U`,
and `Q` lies in the third. Either the two parts are the children and `Q` is outside `U`, or they are a child and the
outside, and `Q` is in the other child. -/
def IsCherryAnchor (H : Finset (Finset X)) (U P Q : Finset X) : Prop :=
  ∃ A ∈ childClusters H U, ∃ B ∈ childClusters H U, A ≠ B ∧ ∃ a ∈ A, ∃ b, P = {a, b} ∧
    ((b ∈ B ∧ Q ⊆ Uᶜ) ∨ (b ∉ U ∧ Q ⊆ B))

theorem isAnchorOf_iff {H : Finset (Finset X)} {U : Finset X} {s : QuartetTree X} :
    IsAnchorOf H U s ↔ ∃ P ∈ s.val, IsCherryAnchor H U P (s.taxa \ P) := by
  constructor
  · rintro ⟨A, hA, B, hB, hne, ⟨a, ha, b, hb, hm, hsub⟩ | ⟨b, hb, x, hx, hm, hsub⟩ |
      ⟨x, hx, a, ha, hm, hsub⟩⟩
    · exact ⟨_, hm, A, hA, B, hB, hne, a, ha, b, rfl, Or.inl ⟨hb, hsub⟩⟩
    · exact ⟨_, hm, B, hB, A, hA, hne.symm, b, hb, x, rfl, Or.inr ⟨mem_compl.1 hx, hsub⟩⟩
    · exact ⟨_, hm, A, hA, B, hB, hne, a, ha, x, pair_comm _ _, Or.inr ⟨mem_compl.1 hx, hsub⟩⟩
  · rintro ⟨P, hP, A, hA, B, hB, hne, a, ha, b, rfl, ⟨hb, hsub⟩ | ⟨hb, hsub⟩⟩
    · exact ⟨A, hA, B, hB, hne, Or.inl ⟨a, ha, b, hb, hP, hsub⟩⟩
    · refine ⟨A, hA, B, hB, hne, Or.inr (Or.inr ⟨b, mem_compl.2 hb, a, ha, ?_, ?_⟩)⟩
      · rwa [pair_comm]
      · rwa [pair_comm]

namespace IsHierarchy

variable {H : Finset (Finset X)}

omit [Fintype X] in
private theorem exists_eq_pair_of_mem {P : Finset X} {a : X} (hP : P.card = 2) (ha : a ∈ P) :
    ∃ b, P = {a, b} := by
  obtain ⟨x, y, -, rfl⟩ := card_eq_two.1 hP
  rcases mem_insert.1 ha with rfl | h
  · exact ⟨y, rfl⟩
  · rw [mem_singleton] at h
    subst h
    exact ⟨x, pair_comm _ _⟩

private theorem exists_other_mem {α : Type*} [DecidableEq α] {F : Finset α} {B : α} (hF : F.card = 2)
    (hB : B ∈ F) : ∃ A ∈ F, A ≠ B ∧ ∀ C ∈ F, C = A ∨ C = B := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hF
  rcases mem_insert.1 hB with rfl | h
  · exact ⟨y, by simp, hxy.symm, fun C hC => by
      rcases mem_insert.1 hC with h | h
      · exact Or.inr h
      · exact Or.inl (mem_singleton.1 h)⟩
  · rw [mem_singleton] at h
    subst h
    exact ⟨x, by simp, hxy, fun C hC => by
      rcases mem_insert.1 hC with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.1 h)⟩

/-- Two children of a cluster with a common taxon are equal. -/
theorem eq_of_mem_childClusters (hH : IsHierarchy H) {U A B : Finset X}
    (hA : A ∈ childClusters H U) (hB : B ∈ childClusters H U) {x : X} (hxA : x ∈ A) (hxB : x ∈ B) :
    A = B := by
  by_contra hne
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hA hB hne) hxA hxB

/-- A cherry contained in a side avoiding the other cherry has an anchor: the least cluster containing it. -/
theorem exists_isCherryAnchor_of_side (hH : IsHierarchy H) {P Q E : Finset X} (hP : P.card = 2)
    (hE : E ∈ H) (hPE : P ⊆ E) (hEQ : Disjoint E Q) : ∃ U ∈ H, IsCherryAnchor H U P Q := by
  obtain ⟨U, hU, hPU, hleast⟩ := hH.exists_least (card_pos.1 (by omega : 0 < P.card))
  have hU2 : 2 ≤ U.card := hP ▸ card_le_card hPU
  obtain ⟨a, b, -, rfl⟩ := card_eq_two.1 hP
  obtain ⟨A, hA, haA⟩ := hH.exists_mem_childClusters hU2 (x := a) (hPU (by simp))
  obtain ⟨B, hB, hbB⟩ := hH.exists_mem_childClusters hU2 (x := b) (hPU (by simp))
  refine ⟨U, hU, A, hA, B, hB, ?_, a, haA, b, rfl, Or.inl ⟨hbB, fun x hx => mem_compl.2 fun hxU => ?_⟩⟩
  · rintro rfl
    obtain ⟨hAH, hAU, -⟩ := mem_childClusters.1 hA
    refine not_subset_of_ssubset hAU (hleast A hAH fun x hx => ?_)
    rcases mem_insert.1 hx with rfl | h
    · exact haA
    · rw [mem_singleton] at h
      exact h ▸ hbB
  · exact disjoint_left.1 hEQ (hleast E hE hPE hxU) hx

/-- A cherry whose only sides are on the side of the other cherry has an anchor: the parent of the largest
cluster containing the other cherry and avoiding it. -/
theorem exists_isCherryAnchor_of_other_side (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) {P Q E : Finset X} (hP : P.card = 2)
    (hE : E ∈ H) (hQE : Q ⊆ E) (hEP : Disjoint E P) (hno : ∀ E' ∈ H, P ⊆ E' → ¬ Disjoint E' Q) :
    ∃ U ∈ H, IsCherryAnchor H U P Q := by
  have hPne : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, hmax⟩ := (H.filter fun D => Q ⊆ D ∧ Disjoint D P).exists_max_image card
    ⟨E, mem_filter.2 ⟨hE, hQE, hEP⟩⟩
  obtain ⟨hBH, hQB, hBP⟩ := mem_filter.1 hB
  have hBu : B ≠ univ := by
    rintro rfl
    obtain ⟨x, hx⟩ := hPne
    exact disjoint_left.1 hBP (mem_univ x) hx
  have hUH := hH.parentCluster_mem hBH hBu
  have hBU := hH.ssubset_parentCluster hBH hBu
  have hBch := hH.mem_childClusters_parentCluster hBH hBu
  generalize parentCluster H B = U at hUH hBU hBch
  have hU2 : 2 ≤ U.card := by
    have h1 := card_lt_card hBU
    have h2 := card_pos.2 (hH.2.2.1 B hBH)
    omega
  obtain ⟨A, hA, hne, hAB⟩ := exists_other_mem (hbin U hUH hU2) hBch
  have hinA : ∀ x ∈ U, x ∉ B → x ∈ A := by
    intro x hxU hxB
    obtain ⟨D, hD, hxD⟩ := hH.exists_mem_childClusters hU2 hxU
    rcases hAB D hD with rfl | rfl
    · exact hxD
    · exact absurd hxD hxB
  have hUP : ¬ Disjoint U P := fun hd => absurd
    (hmax U (mem_filter.2 ⟨hUH, hQB.trans hBU.subset, hd⟩)) (not_le.2 (card_lt_card hBU))
  obtain ⟨a, haU, haP⟩ := not_disjoint_iff.1 hUP
  obtain ⟨b, rfl⟩ := exists_eq_pair_of_mem hP haP
  have hPB : ∀ x ∈ ({a, b} : Finset X), x ∉ B := fun x hx hxB => disjoint_left.1 hBP hxB hx
  have haA := hinA a haU (hPB a (by simp))
  refine ⟨U, hUH, A, hA, B, hBch, hne, a, haA, b, rfl, Or.inr ⟨fun hbU => ?_, hQB⟩⟩
  have hbA := hinA b hbU (hPB b (by simp))
  refine hno A (mem_childClusters.1 hA).1 (fun x hx => ?_) ?_
  · rcases mem_insert.1 hx with rfl | h
    · exact haA
    · rw [mem_singleton] at h
      exact h ▸ hbA
  · exact (hH.disjoint_of_mem_childClusters hA hBch hne).mono_right hQB

/-- A cherry has an anchor as soon as one of the cherries has a side avoiding the other. -/
theorem exists_isCherryAnchor (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) {P Q : Finset X} (hP : P.card = 2)
    (hside : ∃ E ∈ H, (P ⊆ E ∧ Disjoint E Q) ∨ (Q ⊆ E ∧ Disjoint E P)) :
    ∃ U ∈ H, IsCherryAnchor H U P Q := by
  by_cases h : ∃ E ∈ H, P ⊆ E ∧ Disjoint E Q
  · obtain ⟨E, hE, h1, h2⟩ := h
    exact hH.exists_isCherryAnchor_of_side hP hE h1 h2
  · obtain ⟨E, hE, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hside
    · exact absurd ⟨E, hE, h1, h2⟩ h
    · exact hH.exists_isCherryAnchor_of_other_side hbin hP hE h1 h2
        fun E' hE' hPE' hd => h ⟨E', hE', hPE', hd⟩

/-- An anchored cherry gives a side: the anchor, or the child containing the other cherry. -/
theorem _root_.Phylogenetics.IsCherryAnchor.exists_side (hH : IsHierarchy H) {U P Q : Finset X}
    (h : IsCherryAnchor H U P Q) (hU : U ∈ H) :
    ∃ E ∈ H, (P ⊆ E ∧ Disjoint E Q) ∨ (Q ⊆ E ∧ Disjoint E P) := by
  obtain ⟨A, hA, B, hB, hne, a, ha, b, rfl, ⟨hb, hQ⟩ | ⟨hb, hQ⟩⟩ := h
  · refine ⟨U, hU, Or.inl ⟨fun x hx => ?_, disjoint_left.2 fun x hx hxQ => mem_compl.1 (hQ hxQ) hx⟩⟩
    rcases mem_insert.1 hx with rfl | h
    · exact (mem_childClusters.1 hA).2.1.subset ha
    · rw [mem_singleton] at h
      exact h ▸ (mem_childClusters.1 hB).2.1.subset hb
  · refine ⟨B, (mem_childClusters.1 hB).1, Or.inr ⟨hQ, disjoint_left.2 fun x hxB hx => ?_⟩⟩
    rcases mem_insert.1 hx with rfl | h
    · exact hne (hH.eq_of_mem_childClusters hA hB ha hxB)
    · rw [mem_singleton] at h
      exact hb (h ▸ (mem_childClusters.1 hB).2.1.subset hxB)

/-- A node is not an anchor of both cherries. -/
theorem _root_.Phylogenetics.IsCherryAnchor.not_swap (hH : IsHierarchy H) {U P Q : Finset X}
    (h : IsCherryAnchor H U P Q) : ¬ IsCherryAnchor H U Q P := by
  rintro ⟨A', hA', B', hB', hne', c, hc, d, rfl, hcase'⟩
  obtain ⟨A, hA, B, hB, hne, a, ha, b, -, ⟨-, hQ⟩ | ⟨-, hQ⟩⟩ := h
  · exact mem_compl.1 (hQ (by simp)) ((mem_childClusters.1 hA').2.1.subset hc)
  · have hcB : c ∈ B := hQ (by simp)
    have hdB : d ∈ B := hQ (by simp)
    rcases hcase' with ⟨hd, -⟩ | ⟨hd, -⟩
    · exact hne' ((hH.eq_of_mem_childClusters hA' hB hc hcB).trans
        (hH.eq_of_mem_childClusters hB' hB hd hdB).symm)
    · exact hd ((mem_childClusters.1 hB).2.1.subset hdB)

/-- A cluster strictly inside the anchor of a cherry is not an anchor of that cherry. -/
theorem _root_.Phylogenetics.IsCherryAnchor.not_of_ssubset (hH : IsHierarchy H) {U V P Q : Finset X} (hQne : Q.Nonempty)
    (hU : IsCherryAnchor H U P Q) (hVH : V ∈ H) (hVU : V ⊂ U) : ¬ IsCherryAnchor H V P Q := by
  rintro ⟨A', hA', B', hB', hne', a', ha', b', hPe', hcase'⟩
  obtain ⟨A, hA, B, hB, hne, a, ha, b, hPe, hcase⟩ := hU
  obtain ⟨-, hAU, -⟩ := mem_childClusters.1 hA
  obtain ⟨hBH, hBU, -⟩ := mem_childClusters.1 hB
  obtain ⟨-, hA'V, -⟩ := mem_childClusters.1 hA'
  obtain ⟨-, hB'V, -⟩ := mem_childClusters.1 hB'
  have hU2 : 2 ≤ U.card := by
    obtain ⟨x, hx⟩ := hH.2.2.1 B hBH
    refine one_lt_card.2 ⟨a, hAU.subset ha, x, hBU.subset hx, ?_⟩
    rintro rfl
    exact hne (hH.eq_of_mem_childClusters hA hB ha hx)
  obtain ⟨D, hD, hVD⟩ := hH.exists_subset_child hU2 hVH hVU
  have hbP : b ∈ P := by rw [hPe]; simp
  have haP : a ∈ P := by rw [hPe]; simp
  have ha'P : a' ∈ P := by rw [hPe']; simp
  have hPV : b' ∈ B' → P ⊆ V := fun hb' => by
    rw [hPe']
    intro y hy
    rcases mem_insert.1 hy with rfl | h
    · exact hA'V.subset ha'
    · rw [mem_singleton] at h
      exact h ▸ hB'V.subset hb'
  obtain ⟨x, hx⟩ := hQne
  rcases hcase with ⟨hb, hQ⟩ | ⟨hb, hQ⟩ <;> rcases hcase' with ⟨hb', hQ'⟩ | ⟨hb', hQ'⟩
  · -- both are the least cluster containing `P`, so `P` lies in one child of `U`
    exact hne ((hH.eq_of_mem_childClusters hA hD ha (hVD (hPV hb' haP))).trans
      (hH.eq_of_mem_childClusters hB hD hb (hVD (hPV hb' hbP))).symm)
  · exact mem_compl.1 (hQ hx) (hVU.subset (hB'V.subset (hQ' hx)))
  · exact hb (hVU.subset (hPV hb' hbP))
  · have hDB : D = B := hH.eq_of_mem_childClusters hD hB (hVD (hB'V.subset (hQ' hx))) (hQ hx)
    have ha'B : a' ∈ B := hDB ▸ hVD (hA'V.subset ha')
    rw [hPe] at ha'P
    rcases mem_insert.1 ha'P with rfl | h
    · exact hne (hH.eq_of_mem_childClusters hA hB ha ha'B)
    · rw [mem_singleton] at h
      subst h
      exact hb (hBU.subset ha'B)

/-- The anchor of a cherry is unique. -/
theorem _root_.Phylogenetics.IsCherryAnchor.unique (hH : IsHierarchy H) {U V P Q : Finset X} (hQne : Q.Nonempty)
    (hU : IsCherryAnchor H U P Q) (hV : IsCherryAnchor H V P Q) (hUH : U ∈ H) (hVH : V ∈ H) :
    U = V := by
  have facts : ∀ {W : Finset X}, IsCherryAnchor H W P Q → (∃ x ∈ P, x ∈ W) ∧ (P ⊆ W ∨ Q ⊆ W) := by
    rintro W ⟨A, hA, B, hB, -, a, ha, b, rfl, hcase⟩
    have haW := (mem_childClusters.1 hA).2.1.subset ha
    refine ⟨⟨a, by simp, haW⟩, ?_⟩
    rcases hcase with ⟨hb, -⟩ | ⟨-, hQ⟩
    · refine Or.inl fun x hx => ?_
      rcases mem_insert.1 hx with rfl | h
      · exact haW
      · rw [mem_singleton] at h
        exact h ▸ (mem_childClusters.1 hB).2.1.subset hb
    · exact Or.inr (hQ.trans (mem_childClusters.1 hB).2.1.subset)
  obtain ⟨x, hxU, hxV⟩ : ∃ x, x ∈ U ∧ x ∈ V := by
    obtain ⟨⟨y, hyP, hyU⟩, hU'⟩ := facts hU
    obtain ⟨⟨z, hzP, hzV⟩, hV'⟩ := facts hV
    rcases hU' with h | h
    · exact ⟨z, h hzP, hzV⟩
    · rcases hV' with h' | h'
      · exact ⟨y, hyU, h' hyP⟩
      · obtain ⟨t, ht⟩ := hQne
        exact ⟨t, h ht, h' ht⟩
  by_contra hne
  rcases hH.subset_or_subset_of_mem hUH hVH hxU hxV with h | h
  · exact hV.not_of_ssubset hH hQne hUH (ssubset_of_subset_of_ne h hne) hU
  · exact hU.not_of_ssubset hH hQne hVH (ssubset_of_subset_of_ne h (Ne.symm hne)) hV

omit [Fintype X] in
private theorem inter_union_eq_left {A P Q : Finset X} (hd : Disjoint P Q) (h : A ∩ (P ∪ Q) = P) :
    P ⊆ A ∧ Disjoint A Q := by
  refine ⟨fun x hx => ?_, disjoint_left.2 fun x hxA hxQ => ?_⟩
  · rw [← h] at hx
    exact (mem_inter.1 hx).1
  · have : x ∈ A ∩ (P ∪ Q) := mem_inter.2 ⟨hxA, mem_union_right _ hxQ⟩
    rw [h] at this
    exact disjoint_left.1 hd this hxQ

/-- The tree of a hierarchy displays the quartet tree with cherries `P`, `Q` exactly when a cluster contains one
cherry and avoids the other. -/
theorem _root_.Phylogenetics.displays_unroot_iff_exists_side {s : QuartetTree X} {P Q : Finset X}
    (hs : s.val = {P, Q}) (hd : Disjoint P Q) (ht : s.taxa = P ∪ Q) (hP : P.Nonempty)
    (hQ : Q.Nonempty) :
    Displays (unroot H) s ↔ ∃ E ∈ H, (P ⊆ E ∧ Disjoint E Q) ∨ (Q ⊆ E ∧ Disjoint E P) := by
  have hne : ∀ {E Y : Finset X}, Y.Nonempty → Disjoint E Y → E ≠ univ := by
    rintro E Y ⟨y, hy⟩ hE rfl
    exact disjoint_left.1 hE (mem_univ y) hy
  constructor
  · rintro ⟨A, hA, hAs⟩
    rw [hs, ht] at hAs
    have hcases : (P ⊆ A ∧ Disjoint A Q) ∨ (Q ⊆ A ∧ Disjoint A P) := by
      rcases mem_insert.1 hAs with h | h
      · exact Or.inl (inter_union_eq_left hd h)
      · rw [mem_singleton, union_comm] at h
        exact Or.inr (inter_union_eq_left hd.symm h)
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact ⟨A, hA', hcases⟩
    · refine ⟨Aᶜ, hA', ?_⟩
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inr ⟨fun x hx => mem_compl.2 fun hxA => disjoint_left.1 h2 hxA hx,
          disjoint_left.2 fun x hx hxP => mem_compl.1 hx (h1 hxP)⟩
      · refine Or.inl ⟨fun x hx => mem_compl.2 fun hxA => disjoint_left.1 h2 hxA hx,
          disjoint_left.2 fun x hx hxQ => mem_compl.1 hx (h1 hxQ)⟩
  · rintro ⟨E, hE, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨E, mem_unroot.2 (Or.inl ⟨hE, hne hQ h2⟩), ?_⟩
      have : E ∩ s.taxa = P := by
        rw [ht, inter_union_distrib_left, inter_eq_right.2 h1, disjoint_iff_inter_eq_empty.1 h2,
          union_empty]
      rw [this, hs]
      simp
    · refine ⟨E, mem_unroot.2 (Or.inl ⟨hE, hne hP h2⟩), ?_⟩
      have : E ∩ s.taxa = Q := by
        rw [ht, inter_union_distrib_left, inter_eq_right.2 h1, disjoint_iff_inter_eq_empty.1 h2,
          empty_union]
      rw [this, hs]
      simp

/-- **Each quartet is associated to exactly two nodes** (Mirarab et al. 2014, Section 2): on a binary hierarchy, a displayed quartet tree has exactly two anchors, one for
each cherry, and a quartet tree that is not displayed has none. The anchor of a cherry is the least cluster containing it, if that cluster avoids the other cherry
(`exists_isCherryAnchor_of_side`), and otherwise the parent of the largest cluster containing the other cherry and
avoiding it (`exists_isCherryAnchor_of_other_side`). -/
theorem card_filter_isAnchorOf (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) (s : QuartetTree X) :
    (H.filter fun U => IsAnchorOf H U s).card = if Displays (unroot H) s then 2 else 0 := by
  obtain ⟨P, Q, hs, hP, hQ, hd, ht⟩ := s.exists_eq_pair
  have hPne : P.Nonempty := card_pos.1 (by omega)
  have hQne : Q.Nonempty := card_pos.1 (by omega)
  have hsdP : s.taxa \ P = Q := by rw [ht, union_sdiff_cancel_left hd]
  have hsdQ : s.taxa \ Q = P := by rw [ht, union_sdiff_cancel_right hd]
  have hiff : ∀ U, IsAnchorOf H U s ↔ IsCherryAnchor H U P Q ∨ IsCherryAnchor H U Q P := by
    intro U
    rw [isAnchorOf_iff]
    constructor
    · rintro ⟨R, hR, h⟩
      rw [hs] at hR
      rcases mem_insert.1 hR with rfl | hR
      · rw [hsdP] at h
        exact Or.inl h
      · rw [mem_singleton] at hR
        subst hR
        rw [hsdQ] at h
        exact Or.inr h
    · rintro (h | h)
      · exact ⟨P, by simp [hs], by rwa [hsdP]⟩
      · exact ⟨Q, by simp [hs], by rwa [hsdQ]⟩
  have hdisp := displays_unroot_iff_exists_side (H := H) hs hd ht hPne hQne
  split_ifs with hD
  · have hside := hdisp.1 hD
    obtain ⟨U₁, hU₁, hA₁⟩ := hH.exists_isCherryAnchor hbin hP hside
    obtain ⟨U₂, hU₂, hA₂⟩ := hH.exists_isCherryAnchor hbin hQ (by
      obtain ⟨E, hE, h⟩ := hside
      exact ⟨E, hE, h.symm⟩)
    have hne : U₁ ≠ U₂ := by
      rintro rfl
      exact hA₁.not_swap hH hA₂
    have hfilter : (H.filter fun U => IsAnchorOf H U s) = {U₁, U₂} := by
      ext U
      simp only [mem_filter, mem_insert, mem_singleton, hiff]
      constructor
      · rintro ⟨hU, h | h⟩
        · exact Or.inl (h.unique hH hQne hA₁ hU hU₁)
        · exact Or.inr (h.unique hH hPne hA₂ hU hU₂)
      · rintro (rfl | rfl)
        · exact ⟨hU₁, Or.inl hA₁⟩
        · exact ⟨hU₂, Or.inr hA₂⟩
    rw [hfilter, card_pair hne]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro U hU h
    rcases (hiff U).1 h with h | h
    · exact hD (hdisp.2 (h.exists_side hH hU))
    · obtain ⟨E, hE, h'⟩ := h.exists_side hH hU
      exact hD (hdisp.2 ⟨E, hE, h'.symm⟩)

end IsHierarchy

/-- **The anchor identity** (Mirarab et al. 2014, Section 2: "the final score needs to be divided by two to get the
quartet score"): for a binary rooted tree `H` and any weights, twice the quartet score of the unrooted tree of `H` is
the sum over its nodes of the weights of the tripartitions there. By `nodeWeight_eq_zero` and
`nodeWeight_eq_tripartitionWeight` a leaf contributes nothing and a node with children `A`, `B` contributes
`tripartitionWeight w A B Uᶜ`; the root, which is not a node of the unrooted tree, contributes nothing either, by
`tripartitionWeight_empty`. -/
theorem two_mul_quartetSupport_unroot {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) (w : QuartetTree X → ℝ) :
    2 * quartetSupport w (unroot H) = ∑ U ∈ H, nodeWeight w H U := by
  unfold quartetSupport nodeWeight
  rw [mul_sum, sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, hH.card_filter_isAnchorOf hbin s]
  split_ifs <;> simp

/-- **The anchor identity, over the internal nodes.** For a binary rooted tree `H` with children `l U`, `r U` at each
cluster `U` with at least two taxa, twice the quartet score of the unrooted tree of `H` is the sum of the weights
`W(l U|r U|Uᶜ)` over its internal nodes, which are the clusters other than `univ` with at least two taxa. -/
theorem two_mul_quartetSupport_eq_sum_tripartitionWeight {H : Finset (Finset X)} (hH : IsHierarchy H)
    (w : QuartetTree X → ℝ) {l r : Finset X → Finset X}
    (hlr : ∀ U ∈ H, 2 ≤ U.card → l U ≠ r U ∧ childClusters H U = {l U, r U}) :
    2 * quartetSupport w (unroot H) =
      ∑ U ∈ H.filter (fun U => 2 ≤ U.card ∧ U ≠ univ), tripartitionWeight w (l U) (r U) Uᶜ := by
  have hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2 := fun A hA h2 => by
    obtain ⟨hne, hch⟩ := hlr A hA h2
    rw [hch, card_pair hne]
  rw [two_mul_quartetSupport_unroot hH hbin, ← sum_filter_of_ne (p := fun U => 2 ≤ U.card ∧ U ≠ univ)]
  · refine sum_congr rfl fun U hU => ?_
    obtain ⟨hUH, h2, -⟩ := mem_filter.1 hU
    exact nodeWeight_eq_tripartitionWeight w (hlr U hUH h2).1 (hlr U hUH h2).2
  · intro U hU hne
    by_contra hcon
    by_cases h2 : 2 ≤ U.card
    · have hu : U = univ := by
        by_contra h
        exact hcon ⟨h2, h⟩
      subst hu
      apply hne
      rw [nodeWeight_eq_tripartitionWeight w (hlr _ hU h2).1 (hlr _ hU h2).2, compl_univ,
        tripartitionWeight_empty]
    · have hc1 : U.card = 1 := by
        have := card_pos.2 (hH.2.2.1 U hU)
        omega
      obtain ⟨x, rfl⟩ := card_eq_one.1 hc1
      exact hne (nodeWeight_eq_zero w (hH.childClusters_singleton x))

/-- The anchor identity for a binary tree `T`, on one of its binary rootings. By
`two_mul_quartetSupport_eq_sum_tripartitionWeight` it holds on all of them. -/
theorem IsBinaryTree.exists_two_mul_quartetSupport {T : Finset (Finset X)} (hT : IsBinaryTree T)
    (w : QuartetTree X → ℝ) :
    ∃ (H : Finset (Finset X)) (l r : Finset X → Finset X), IsHierarchy H ∧ unroot H = T ∧
      (∀ U ∈ H, 2 ≤ U.card → l U ≠ r U ∧ childClusters H U = {l U, r U}) ∧
      2 * quartetSupport w T =
        ∑ U ∈ H.filter (fun U => 2 ≤ U.card ∧ U ≠ univ), tripartitionWeight w (l U) (r U) Uᶜ := by
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  have hex : ∀ U, ∃ a b, U ∈ H → 2 ≤ U.card → a ≠ b ∧ childClusters H U = {a, b} := by
    intro U
    by_cases hU : U ∈ H ∧ 2 ≤ U.card
    · obtain ⟨a, b, hne, hch⟩ := card_eq_two.1 (hbin U hU.1 hU.2)
      exact ⟨a, b, fun _ _ => ⟨hne, hch⟩⟩
    · exact ⟨∅, ∅, fun h1 h2 => absurd ⟨h1, h2⟩ hU⟩
  choose l r hlr using hex
  exact ⟨H, l, r, hH, rfl, hlr, two_mul_quartetSupport_eq_sum_tripartitionWeight hH w hlr⟩

/-! ### Binary rooted trees on a set of taxa with clusters in a family -/

/-- `R` is a binary rooted tree on the taxa `C`, given by its clusters, whose clusters other than `C` lie in `𝒞`.
These are the objects over which the recursion of Mirarab et al. 2014 maximizes: the clusters of a rooted tree on `A`,
other than `A`, must lie in `X*`. -/
inductive IsBinaryClusterTree (𝒞 : Finset (Finset X)) : Finset X → Finset (Finset X) → Prop
  | leaf (x : X) : IsBinaryClusterTree 𝒞 {x} {{x}}
  | node {A B : Finset X} {RA RB : Finset (Finset X)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hAB : Disjoint A B)
      (hRA : IsBinaryClusterTree 𝒞 A RA) (hRB : IsBinaryClusterTree 𝒞 B RB) :
      IsBinaryClusterTree 𝒞 (A ∪ B) (insert (A ∪ B) (RA ∪ RB))

/-- The total weight of a rooted tree: the sum of the weights of its nodes. -/
def treeWeight (w : QuartetTree X → ℝ) (R : Finset (Finset X)) : ℝ := ∑ U ∈ R, nodeWeight w R U

private theorem childClusters_eq_of_forall {R R' : Finset (Finset X)} {U : Finset X} (hR' : R' ⊆ R)
    (h : ∀ V ∈ R, V ⊂ U → V ∈ R') : childClusters R U = childClusters R' U := by
  ext V
  simp only [mem_childClusters]
  constructor
  · rintro ⟨hV, hVU, hmax⟩
    exact ⟨h V hV hVU, hVU, fun C hC => hmax C (hR' hC)⟩
  · rintro ⟨hV, hVU, hmax⟩
    exact ⟨hR' hV, hVU, fun C hC hVC hCU => hmax C (h C hC hCU) hVC hCU⟩

namespace IsBinaryClusterTree

variable {𝒞 : Finset (Finset X)} {C : Finset X} {R : Finset (Finset X)}

omit [Fintype X] in
theorem self_mem (h : IsBinaryClusterTree 𝒞 C R) : C ∈ R := by
  cases h with
  | leaf x => exact mem_singleton_self _
  | node _ _ _ _ _ => exact mem_insert_self _ _

omit [Fintype X] in
theorem subset (h : IsBinaryClusterTree 𝒞 C R) : ∀ U ∈ R, U ⊆ C := by
  induction h with
  | leaf x =>
    intro U hU
    rw [mem_singleton] at hU
    rw [hU]
  | node _ _ _ _ _ ihA ihB =>
    intro U hU
    rcases mem_insert.1 hU with rfl | hU
    · exact Subset.refl _
    · rcases mem_union.1 hU with hU | hU
      · exact (ihA U hU).trans subset_union_left
      · exact (ihB U hU).trans subset_union_right

omit [Fintype X] in
theorem nonempty (h : IsBinaryClusterTree 𝒞 C R) : ∀ U ∈ R, U.Nonempty := by
  induction h with
  | leaf x =>
    intro U hU
    rw [mem_singleton] at hU
    rw [hU]
    exact singleton_nonempty x
  | node _ _ _ hRA _ ihA ihB =>
    intro U hU
    rcases mem_insert.1 hU with rfl | hU
    · exact (ihA _ hRA.self_mem).mono subset_union_left
    · rcases mem_union.1 hU with hU | hU
      · exact ihA U hU
      · exact ihB U hU

omit [Fintype X] in
theorem mem_of_ne (h : IsBinaryClusterTree 𝒞 C R) : ∀ U ∈ R, U ≠ C → U ∈ 𝒞 := by
  induction h with
  | leaf x =>
    intro U hU hne
    exact absurd (mem_singleton.1 hU) hne
  | @node A B RA RB hA hB _ _ _ ihA ihB =>
    intro U hU hne
    rcases mem_insert.1 hU with h | hU
    · exact absurd h hne
    · rcases mem_union.1 hU with hU | hU
      · by_cases hUA : U = A
        · exact hUA ▸ hA
        · exact ihA U hU hUA
      · by_cases hUB : U = B
        · exact hUB ▸ hB
        · exact ihB U hU hUB

omit [Fintype X] in
theorem laminar (h : IsBinaryClusterTree 𝒞 C R) :
    ∀ U ∈ R, ∀ V ∈ R, U ⊆ V ∨ V ⊆ U ∨ Disjoint U V := by
  induction h with
  | leaf x =>
    intro U hU V hV
    rw [mem_singleton] at hU hV
    exact Or.inl (by rw [hU, hV])
  | @node A B RA RB _ _ hAB hRA hRB ihA ihB =>
    intro U hU V hV
    have hsub : ∀ W ∈ RA ∪ RB, W ⊆ A ∪ B := fun W hW => by
      rcases mem_union.1 hW with hW | hW
      · exact (hRA.subset W hW).trans subset_union_left
      · exact (hRB.subset W hW).trans subset_union_right
    rcases mem_insert.1 hU with rfl | hU'
    · rcases mem_insert.1 hV with rfl | hV'
      · exact Or.inl (Subset.refl _)
      · exact Or.inr (Or.inl (hsub V hV'))
    · rcases mem_insert.1 hV with rfl | hV'
      · exact Or.inl (hsub U hU')
      · rcases mem_union.1 hU' with hU' | hU' <;> rcases mem_union.1 hV' with hV' | hV'
        · exact ihA U hU' V hV'
        · exact Or.inr (Or.inr (hAB.mono (hRA.subset U hU') (hRB.subset V hV')))
        · exact Or.inr (Or.inr (hAB.symm.mono (hRB.subset U hU') (hRA.subset V hV')))
        · exact ihB U hU' V hV'

omit [Fintype X] in
theorem singleton_mem (h : IsBinaryClusterTree 𝒞 C R) : ∀ x ∈ C, {x} ∈ R := by
  induction h with
  | leaf x =>
    intro y hy
    rw [mem_singleton] at hy
    rw [hy]
    exact mem_singleton_self _
  | node _ _ _ _ _ ihA ihB =>
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact mem_insert_of_mem (mem_union_left _ (ihA x hx))
    · exact mem_insert_of_mem (mem_union_right _ (ihB x hx))

omit [Fintype X] in
private theorem ssubset_union_left_of {A B : Finset X} (hB : B.Nonempty) (hAB : Disjoint A B) :
    A ⊂ A ∪ B := by
  obtain ⟨x, hx⟩ := hB
  exact (ssubset_iff_of_subset subset_union_left).2
    ⟨x, mem_union_right _ hx, fun hxA => disjoint_left.1 hAB hxA hx⟩

/-- Below a node of the left subtree, a tree and its left subtree have the same children. -/
private theorem childClusters_insert_left {A B T : Finset X} {RA RB : Finset (Finset X)}
    (hRA : IsBinaryClusterTree 𝒞 A RA) (hRB : IsBinaryClusterTree 𝒞 B RB) (hAB : Disjoint A B)
    (hT : A ⊆ T) {U : Finset X} (hU : U ∈ RA) :
    childClusters (insert T (RA ∪ RB)) U = childClusters RA U := by
  refine childClusters_eq_of_forall
    (fun V hV => mem_insert_of_mem (mem_union_left _ hV)) fun V hV hVU => ?_
  have hUA := hRA.subset U hU
  rcases mem_insert.1 hV with rfl | hV
  · exact absurd (hVU.trans_subset hUA) (not_ssubset_of_subset hT)
  · rcases mem_union.1 hV with hV | hV
    · exact hV
    · obtain ⟨x, hx⟩ := hRB.nonempty V hV
      exact absurd (hRB.subset V hV hx) (disjoint_left.1 hAB (hUA (hVU.subset hx)))

/-- Below a node of the right subtree, a tree and its right subtree have the same children. -/
private theorem childClusters_insert_right {A B T : Finset X} {RA RB : Finset (Finset X)}
    (hRA : IsBinaryClusterTree 𝒞 A RA) (hRB : IsBinaryClusterTree 𝒞 B RB) (hAB : Disjoint A B)
    (hT : B ⊆ T) {U : Finset X} (hU : U ∈ RB) :
    childClusters (insert T (RA ∪ RB)) U = childClusters RB U := by
  rw [union_comm RA RB]
  exact childClusters_insert_left hRB hRA hAB.symm hT hU

/-- The children of the root of a tree are the roots of its two subtrees. -/
private theorem childClusters_node {A B : Finset X} {RA RB : Finset (Finset X)}
    (hRA : IsBinaryClusterTree 𝒞 A RA) (hRB : IsBinaryClusterTree 𝒞 B RB) (hAB : Disjoint A B) :
    childClusters (insert (A ∪ B) (RA ∪ RB)) (A ∪ B) = {A, B} := by
  have hAne := hRA.nonempty A hRA.self_mem
  have hBne := hRB.nonempty B hRB.self_mem
  have hAT := ssubset_union_left_of hBne hAB
  have hBT : B ⊂ A ∪ B := union_comm A B ▸ ssubset_union_left_of hAne hAB.symm
  have hAm : A ∈ insert (A ∪ B) (RA ∪ RB) := mem_insert_of_mem (mem_union_left _ hRA.self_mem)
  have hBm : B ∈ insert (A ∪ B) (RA ∪ RB) := mem_insert_of_mem (mem_union_right _ hRB.self_mem)
  ext V
  rw [mem_childClusters]
  constructor
  · rintro ⟨hV, hVT, hmax⟩
    rcases mem_insert.1 hV with rfl | hV
    · exact absurd hVT (ssubset_irrefl _)
    · rcases mem_union.1 hV with hV | hV
      · have hVA : V = A := by
          by_contra hne
          exact hmax A hAm (ssubset_of_subset_of_ne (hRA.subset V hV) hne) hAT
        simp [hVA]
      · have hVB : V = B := by
          by_contra hne
          exact hmax B hBm (ssubset_of_subset_of_ne (hRB.subset V hV) hne) hBT
        simp [hVB]
  · intro hV
    rcases mem_insert.1 hV with rfl | hV
    · refine ⟨hAm, hAT, fun W hW hVW hWT => ?_⟩
      rcases mem_insert.1 hW with rfl | hW
      · exact ssubset_irrefl _ hWT
      · rcases mem_union.1 hW with hW | hW
        · exact not_subset_of_ssubset hVW (hRA.subset W hW)
        · obtain ⟨x, hx⟩ := hAne
          exact disjoint_left.1 hAB hx (hRB.subset W hW (hVW.subset hx))
    · rw [mem_singleton] at hV
      subst hV
      refine ⟨hBm, hBT, fun W hW hVW hWT => ?_⟩
      rcases mem_insert.1 hW with rfl | hW
      · exact ssubset_irrefl _ hWT
      · rcases mem_union.1 hW with hW | hW
        · obtain ⟨x, hx⟩ := hBne
          exact disjoint_left.1 hAB (hRA.subset W hW (hVW.subset hx)) hx
        · exact not_subset_of_ssubset hVW (hRB.subset W hW)

/-- Every cluster of a binary cluster tree with at least two taxa has two children. -/
theorem binary (h : IsBinaryClusterTree 𝒞 C R) :
    ∀ U ∈ R, 2 ≤ U.card → (childClusters R U).card = 2 := by
  induction h with
  | leaf x =>
    intro U hU hc
    rw [mem_singleton] at hU
    rw [hU, card_singleton] at hc
    omega
  | @node A B RA RB _ _ hAB hRA hRB ihA ihB =>
    intro U hU hc
    rcases mem_insert.1 hU with rfl | hU
    · rw [childClusters_node hRA hRB hAB, card_pair]
      rintro rfl
      obtain ⟨x, hx⟩ := hRA.nonempty A hRA.self_mem
      exact disjoint_left.1 hAB hx hx
    · rcases mem_union.1 hU with hU | hU
      · rw [childClusters_insert_left hRA hRB hAB subset_union_left hU]
        exact ihA U hU hc
      · rw [childClusters_insert_right hRA hRB hAB subset_union_right hU]
        exact ihB U hU hc

/-- The weight of a tree with subtrees `RA`, `RB`: the recursion's summand. -/
theorem treeWeight_node (w : QuartetTree X → ℝ) {A B : Finset X} {RA RB : Finset (Finset X)}
    (hRA : IsBinaryClusterTree 𝒞 A RA) (hRB : IsBinaryClusterTree 𝒞 B RB) (hAB : Disjoint A B) :
    treeWeight w (insert (A ∪ B) (RA ∪ RB)) =
      treeWeight w RA + treeWeight w RB + tripartitionWeight w A B (A ∪ B)ᶜ := by
  have hAne := hRA.nonempty A hRA.self_mem
  have hBne := hRB.nonempty B hRB.self_mem
  have hnot : A ∪ B ∉ RA ∪ RB := by
    intro hm
    rcases mem_union.1 hm with hm | hm
    · exact not_subset_of_ssubset (ssubset_union_left_of hBne hAB) (hRA.subset _ hm)
    · have hBT : B ⊂ A ∪ B := union_comm A B ▸ ssubset_union_left_of hAne hAB.symm
      exact not_subset_of_ssubset hBT (hRB.subset _ hm)
  have hdisj : Disjoint RA RB := disjoint_left.2 fun U hUA hUB => by
    obtain ⟨x, hx⟩ := hRA.nonempty U hUA
    exact disjoint_left.1 hAB (hRA.subset U hUA hx) (hRB.subset U hUB hx)
  have hne : A ≠ B := by
    rintro rfl
    obtain ⟨x, hx⟩ := hAne
    exact disjoint_left.1 hAB hx hx
  unfold treeWeight
  rw [sum_insert hnot, sum_union hdisj,
    nodeWeight_eq_tripartitionWeight w hne (childClusters_node hRA hRB hAB),
    sum_congr rfl fun U hU => nodeWeight_congr w
      (childClusters_insert_left hRA hRB hAB subset_union_left hU),
    sum_congr rfl fun U hU => nodeWeight_congr w
      (childClusters_insert_right hRA hRB hAB subset_union_right hU)]
  ring

theorem treeWeight_leaf (w : QuartetTree X → ℝ) (x : X) : treeWeight w {{x}} = 0 := by
  unfold treeWeight
  rw [sum_singleton]
  refine nodeWeight_eq_zero w ?_
  ext V
  simp only [mem_childClusters, mem_singleton, notMem_empty, iff_false]
  rintro ⟨rfl, h, -⟩
  exact ssubset_irrefl _ h

/-- The part below a cluster `C` of a binary hierarchy whose non-root clusters lie in `𝒞` is a binary cluster
tree. -/
theorem filter_subset {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2)
    (h𝒞 : ∀ U ∈ H, U ≠ univ → U ∈ 𝒞) {C : Finset X} (hC : C ∈ H) :
    IsBinaryClusterTree 𝒞 C (H.filter (· ⊆ C)) := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    have hpos : 0 < C.card := card_pos.2 (hH.2.2.1 C hC)
    by_cases h1 : C.card = 1
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
      have hf : H.filter (· ⊆ {x}) = {{x}} := by
        ext U
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hU, hsub⟩
          exact (subset_singleton_iff.1 hsub).resolve_left (hH.2.2.1 U hU).ne_empty
        · rintro rfl
          exact ⟨hC, Subset.refl _⟩
      rw [hf]
      exact .leaf x
    · have h2 : 2 ≤ C.card := by omega
      obtain ⟨A, B, hne, hch⟩ := card_eq_two.1 (hbin C hC h2)
      have hA : A ∈ childClusters H C := by simp [hch]
      have hB : B ∈ childClusters H C := by simp [hch]
      obtain ⟨hAH, hAC, -⟩ := mem_childClusters.1 hA
      obtain ⟨hBH, hBC, -⟩ := mem_childClusters.1 hB
      have hAB : Disjoint A B := hH.disjoint_of_mem_childClusters hA hB hne
      have hCe : A ∪ B = C := by
        have := hH.sup_childClusters h2
        rw [hch] at this
        simpa using this
      have hAu : A ≠ univ := fun e => not_subset_of_ssubset hAC (e ▸ subset_univ C)
      have hBu : B ≠ univ := fun e => not_subset_of_ssubset hBC (e ▸ subset_univ C)
      have hrec := IsBinaryClusterTree.node (h𝒞 A hAH hAu) (h𝒞 B hBH hBu) hAB
        (ih _ (hn ▸ card_lt_card hAC) hAH rfl) (ih _ (hn ▸ card_lt_card hBC) hBH rfl)
      rw [hCe] at hrec
      convert hrec using 1
      ext U
      simp only [mem_filter, mem_insert, mem_union]
      constructor
      · rintro ⟨hU, hUC⟩
        by_cases hUe : U = C
        · exact Or.inl hUe
        · obtain ⟨D, hD, hUD⟩ := hH.exists_subset_child h2 hU (ssubset_of_subset_of_ne hUC hUe)
          rw [hch] at hD
          rcases mem_insert.1 hD with rfl | hD
          · exact Or.inr (Or.inl ⟨hU, hUD⟩)
          · rw [mem_singleton] at hD
            subst hD
            exact Or.inr (Or.inr ⟨hU, hUD⟩)
      · rintro (rfl | ⟨hU, hUA⟩ | ⟨hU, hUB⟩)
        · exact ⟨hC, Subset.refl _⟩
        · exact ⟨hU, hUA.trans hAC.subset⟩
        · exact ⟨hU, hUB.trans hBC.subset⟩

/-- A binary hierarchy whose non-root clusters lie in `𝒞` is a binary cluster tree on all the taxa. -/
theorem of_isHierarchy {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2)
    (h𝒞 : ∀ U ∈ H, U ≠ univ → U ∈ 𝒞) : IsBinaryClusterTree 𝒞 univ H := by
  have := filter_subset hH hbin h𝒞 hH.1
  rwa [filter_true_of_mem fun _ _ => subset_univ _] at this

/-- A binary cluster tree on all the taxa is a hierarchy. -/
theorem isHierarchy (h : IsBinaryClusterTree 𝒞 univ R) : IsHierarchy R :=
  ⟨h.self_mem, fun x => h.singleton_mem x (mem_univ x), h.nonempty, h.laminar⟩

/-- The unrooted tree of a binary cluster tree on all the taxa is a binary tree. -/
theorem isBinaryTree_unroot (h : IsBinaryClusterTree 𝒞 univ R) : IsBinaryTree (unroot R) :=
  ⟨R, h.isHierarchy, rfl, h.binary⟩

/-- The unrooted tree of a binary cluster tree on all the taxa has its sides in `𝒞`, when `𝒞` is the set of sides
of a set of bipartitions, closed under complements. -/
theorem unroot_subset (h : IsBinaryClusterTree 𝒞 univ R) (h𝒞 : ∀ A ∈ 𝒞, Aᶜ ∈ 𝒞) : unroot R ⊆ 𝒞 := by
  intro U hU
  rcases mem_unroot.1 hU with ⟨hU, hne⟩ | ⟨hU, hne⟩
  · exact h.mem_of_ne U hU hne
  · simpa only [compl_compl] using h𝒞 _ (h.mem_of_ne _ hU hne)

/-- The anchor identity, for a binary cluster tree on all the taxa. -/
theorem two_mul_quartetSupport (h : IsBinaryClusterTree 𝒞 univ R) (w : QuartetTree X → ℝ) :
    2 * quartetSupport w (unroot R) = treeWeight w R :=
  two_mul_quartetSupport_unroot h.isHierarchy h.binary w

end IsBinaryClusterTree

/-- The binary cluster trees on all the taxa are the binary hierarchies with non-root clusters in `𝒞`. -/
theorem isBinaryClusterTree_univ_iff {𝒞 R : Finset (Finset X)} :
    IsBinaryClusterTree 𝒞 univ R ↔
      IsHierarchy R ∧ (∀ A ∈ R, 2 ≤ A.card → (childClusters R A).card = 2) ∧
        ∀ U ∈ R, U ≠ univ → U ∈ 𝒞 :=
  ⟨fun h => ⟨h.isHierarchy, h.binary, h.mem_of_ne⟩, fun h => .of_isHierarchy h.1 h.2.1 h.2.2⟩

/-- A binary tree with sides in `𝒞` has a rooting that is a binary cluster tree. -/
theorem IsBinaryTree.exists_isBinaryClusterTree {𝒞 T : Finset (Finset X)} (hT : IsBinaryTree T)
    (hsub : T ⊆ 𝒞) : ∃ H, IsBinaryClusterTree 𝒞 univ H ∧ unroot H = T := by
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  exact ⟨H, .of_isHierarchy hH hbin fun U hU hne => hsub (mem_unroot.2 (Or.inl ⟨hU, hne⟩)), rfl⟩

/-! ### The dynamic program -/

/-- The allowed splits of `C` (Mirarab et al. 2014, Section 2): the nonempty `A' ⊂ C` with `A' ∈ X*` and
`C - A' ∈ X*`. Each unordered split appears in both orders, which changes nothing in a maximum. -/
def astralSplits (𝒞 : Finset (Finset X)) (C : Finset X) : Finset (Finset X) :=
  𝒞.filter fun A => A.Nonempty ∧ A ⊂ C ∧ C \ A ∈ 𝒞

omit [Fintype X] in
theorem card_lt_of_mem_astralSplits {𝒞 : Finset (Finset X)} {C A : Finset X}
    (h : A ∈ astralSplits 𝒞 C) : A.card < C.card :=
  card_lt_card (mem_filter.1 h).2.2.1

omit [Fintype X] in
theorem card_sdiff_lt_of_mem_astralSplits {𝒞 : Finset (Finset X)} {C A : Finset X}
    (h : A ∈ astralSplits 𝒞 C) : (C \ A).card < C.card := by
  obtain ⟨-, hne, hAC, -⟩ := mem_filter.1 h
  exact card_lt_card (sdiff_ssubset hAC.subset hne)

/-- The recursion of ASTRAL (Mirarab et al. 2014, Section 2):
`C(A) = max {C(A') + C(A - A') + W(A'|A - A'|S - A)}`, over the allowed splits of `A`, with the boundary condition
`C({x}) = 0`. The value `⊥` means that `A` has no binary tree with clusters in `𝒞`. -/
def astralValue (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) (C : Finset X) : WithBot ℝ :=
  if C.card = 1 then 0 else
    (astralSplits 𝒞 C).attach.sup fun A =>
      astralValue w 𝒞 A.1 + astralValue w 𝒞 (C \ A.1) +
        ((tripartitionWeight w A.1 (C \ A.1) Cᶜ : ℝ) : WithBot ℝ)
termination_by C.card
decreasing_by
  · exact card_lt_of_mem_astralSplits A.2
  · exact card_sdiff_lt_of_mem_astralSplits A.2

theorem astralValue_of_card_eq_one (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) {C : Finset X}
    (h : C.card = 1) : astralValue w 𝒞 C = 0 := by
  rw [astralValue, ite_eq_left h]

theorem astralValue_of_card_ne_one (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) {C : Finset X}
    (h : C.card ≠ 1) :
    astralValue w 𝒞 C = (astralSplits 𝒞 C).sup fun A =>
      astralValue w 𝒞 A + astralValue w 𝒞 (C \ A) +
        ((tripartitionWeight w A (C \ A) Cᶜ : ℝ) : WithBot ℝ) := by
  rw [astralValue, ite_eq_right h]
  exact sup_attach (astralSplits 𝒞 C) fun A =>
    astralValue w 𝒞 A + astralValue w 𝒞 (C \ A) +
      ((tripartitionWeight w A (C \ A) Cᶜ : ℝ) : WithBot ℝ)

/-- The allowed splits of `C` attaining the maximum in the recursion, among which backtracking chooses. -/
def optimalSplits (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) (C : Finset X) :
    Finset (Finset X) :=
  (astralSplits 𝒞 C).filter fun A =>
    astralValue w 𝒞 C = astralValue w 𝒞 A + astralValue w 𝒞 (C \ A) +
      ((tripartitionWeight w A (C \ A) Cᶜ : ℝ) : WithBot ℝ)

/-- Backtracking (Mirarab et al. 2014, Section 2, "backtracking gives the final tree"), under any rule for breaking
ties: `R` is a tree that backtracking can produce from `C`. -/
inductive IsTraceback (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) :
    Finset X → Finset (Finset X) → Prop
  | leaf (x : X) : IsTraceback w 𝒞 {x} {{x}}
  | node {C A : Finset X} {R₁ R₂ : Finset (Finset X)} (hA : A ∈ optimalSplits w 𝒞 C)
      (h₁ : IsTraceback w 𝒞 A R₁) (h₂ : IsTraceback w 𝒞 (C \ A) R₂) :
      IsTraceback w 𝒞 C (insert C (R₁ ∪ R₂))

/-- Backtracking with one rule for breaking ties, an arbitrary choice among the optimal splits. On a `C` with value
`⊥` the result means nothing; `isTraceback_astralTrace` applies when the value of `C` is not `⊥`. -/
def astralTrace (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) (C : Finset X) :
    Finset (Finset X) :=
  if h : (optimalSplits w 𝒞 C).Nonempty then
    insert C (astralTrace w 𝒞 h.choose ∪ astralTrace w 𝒞 (C \ h.choose))
  else {C}
termination_by C.card
decreasing_by
  · exact card_lt_of_mem_astralSplits (mem_filter.1 h.choose_spec).1
  · exact card_sdiff_lt_of_mem_astralSplits (mem_filter.1 h.choose_spec).1

/-- The output of ASTRAL on the weights `w` with allowed clusters `𝒞`: the unrooted tree of the tree obtained
by backtracking from all the taxa. -/
def astralTree (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) : Finset (Finset X) :=
  unroot (astralTrace w 𝒞 univ)

variable {w : QuartetTree X → ℝ} {𝒞 : Finset (Finset X)} {C : Finset X} {R : Finset (Finset X)}

/-- A binary tree on `C` with clusters in `𝒞` has weight at most the value of `C`. -/
theorem IsBinaryClusterTree.coe_treeWeight_le (h : IsBinaryClusterTree 𝒞 C R) :
    ((treeWeight w R : ℝ) : WithBot ℝ) ≤ astralValue w 𝒞 C := by
  induction h with
  | leaf x =>
    rw [IsBinaryClusterTree.treeWeight_leaf, astralValue_of_card_eq_one w 𝒞 (card_singleton x)]
    exact le_rfl
  | @node A B RA RB hA hB hAB hRA hRB ihA ihB =>
    have hAne := hRA.nonempty A hRA.self_mem
    have hBne := hRB.nonempty B hRB.self_mem
    have hcard : (A ∪ B).card ≠ 1 := by
      rw [card_union_of_disjoint hAB]
      have h1 := card_pos.2 hAne
      have h2 := card_pos.2 hBne
      omega
    have hAT : A ⊂ A ∪ B := by
      obtain ⟨x, hx⟩ := hBne
      exact (ssubset_iff_of_subset subset_union_left).2
        ⟨x, mem_union_right _ hx, fun hxA => disjoint_left.1 hAB hxA hx⟩
    have hsd : (A ∪ B) \ A = B := union_sdiff_cancel_left hAB
    have hmem : A ∈ astralSplits 𝒞 (A ∪ B) := mem_filter.2 ⟨hA, hAne, hAT, by rwa [hsd]⟩
    rw [IsBinaryClusterTree.treeWeight_node w hRA hRB hAB, astralValue_of_card_ne_one w 𝒞 hcard]
    refine le_trans ?_ (le_sup hmem)
    simp only [hsd]
    rw [WithBot.coe_add, WithBot.coe_add]
    exact add_le_add (add_le_add ihA ihB) le_rfl

/-- What backtracking produces is a binary tree with clusters in `𝒞` of weight the value of `C`. -/
theorem IsTraceback.spec (h : IsTraceback w 𝒞 C R) :
    IsBinaryClusterTree 𝒞 C R ∧ astralValue w 𝒞 C = ((treeWeight w R : ℝ) : WithBot ℝ) := by
  induction h with
  | leaf x =>
    exact ⟨.leaf x, by
      rw [astralValue_of_card_eq_one w 𝒞 (card_singleton x), IsBinaryClusterTree.treeWeight_leaf]
      rfl⟩
  | @node C A R₁ R₂ hA _ _ ih₁ ih₂ =>
    obtain ⟨hsplit, hval⟩ := mem_filter.1 hA
    obtain ⟨hA𝒞, -, hAC, hcompl⟩ := mem_filter.1 hsplit
    have hAB : Disjoint A (C \ A) := disjoint_sdiff
    have hCe : A ∪ (C \ A) = C := union_sdiff_of_subset hAC.subset
    have htree := IsBinaryClusterTree.node hA𝒞 hcompl hAB ih₁.1 ih₂.1
    have hw := IsBinaryClusterTree.treeWeight_node w ih₁.1 ih₂.1 hAB
    rw [hCe] at htree hw
    refine ⟨htree, ?_⟩
    rw [hval, ih₁.2, ih₂.2, hw, WithBot.coe_add, WithBot.coe_add]

/-- The rule of `astralTrace` is a backtracking rule, on a feasible `C`. -/
theorem isTraceback_astralTrace (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) {C : Finset X}
    (hC : astralValue w 𝒞 C ≠ ⊥) : IsTraceback w 𝒞 C (astralTrace w 𝒞 C) := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases h1 : C.card = 1
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
      have hemp : ¬ (optimalSplits w 𝒞 {x}).Nonempty := by
        rintro ⟨A, hA⟩
        obtain ⟨-, hne, hAC, -⟩ := mem_filter.1 (mem_filter.1 hA).1
        have h1' := card_lt_card hAC
        have h2' := card_pos.2 hne
        rw [card_singleton] at h1'
        omega
      rw [astralTrace, dite_eq_right hemp]
      exact .leaf x
    · have hsup := astralValue_of_card_ne_one w 𝒞 h1
      have hne : (astralSplits 𝒞 C).Nonempty := by
        rw [nonempty_iff_ne_empty]
        rintro he
        rw [he, sup_empty] at hsup
        exact hC hsup
      obtain ⟨A₀, hA₀, hval₀⟩ := exists_mem_eq_sup (astralSplits 𝒞 C) hne fun A =>
        astralValue w 𝒞 A + astralValue w 𝒞 (C \ A) +
          ((tripartitionWeight w A (C \ A) Cᶜ : ℝ) : WithBot ℝ)
      have hopt : (optimalSplits w 𝒞 C).Nonempty :=
        ⟨A₀, mem_filter.2 ⟨hA₀, hsup.trans hval₀⟩⟩
      rw [astralTrace, dite_eq_left hopt]
      have hA := hopt.choose_spec
      generalize hopt.choose = A at hA
      obtain ⟨hsplit, hval⟩ := mem_filter.1 hA
      rw [hval] at hC
      have hbot : astralValue w 𝒞 A ≠ ⊥ ∧ astralValue w 𝒞 (C \ A) ≠ ⊥ := by
        constructor
        · intro hb
          exact hC (by rw [hb]; simp)
        · intro hb
          exact hC (by rw [hb]; simp)
      exact .node hA
        (ih _ (hn ▸ card_lt_of_mem_astralSplits hsplit) hbot.1 rfl)
        (ih _ (hn ▸ card_sdiff_lt_of_mem_astralSplits hsplit) hbot.2 rfl)

/-- `C` has a binary tree with clusters in `𝒞` exactly when its value is not `⊥`. -/
theorem astralValue_ne_bot_iff : astralValue w 𝒞 C ≠ ⊥ ↔ ∃ R, IsBinaryClusterTree 𝒞 C R := by
  constructor
  · exact fun h => ⟨_, (isTraceback_astralTrace w 𝒞 h).spec.1⟩
  · rintro ⟨R, hR⟩ hb
    have := hR.coe_treeWeight_le (w := w)
    rw [hb, le_bot_iff] at this
    exact WithBot.coe_ne_bot this

/-- **Correctness of the recursion, over clusters.** If `C` has a binary tree with clusters in `𝒞`, the value of `C`
is the largest weight of such a tree, and backtracking returns a tree attaining it. -/
theorem astralValue_eq_max (w : QuartetTree X → ℝ) (𝒞 : Finset (Finset X)) {C : Finset X}
    (h : ∃ R, IsBinaryClusterTree 𝒞 C R) :
    IsBinaryClusterTree 𝒞 C (astralTrace w 𝒞 C) ∧
      astralValue w 𝒞 C = ((treeWeight w (astralTrace w 𝒞 C) : ℝ) : WithBot ℝ) ∧
      ∀ R, IsBinaryClusterTree 𝒞 C R → treeWeight w R ≤ treeWeight w (astralTrace w 𝒞 C) := by
  obtain ⟨hR, hval⟩ := (isTraceback_astralTrace w 𝒞 (astralValue_ne_bot_iff.2 h)).spec
  refine ⟨hR, hval, fun R' hR' => ?_⟩
  have := hR'.coe_treeWeight_le (w := w)
  rw [hval] at this
  exact_mod_cast this

/-- `T` is an optimum of the quartet score among the binary trees with sides in `𝒞`, with the value of the recursion
at all the taxa being twice its score. -/
structure IsAstralOptimal (w : QuartetTree X → ℝ) (𝒞 T : Finset (Finset X)) : Prop where
  isBinaryTree : IsBinaryTree T
  subset : T ⊆ 𝒞
  le : ∀ T', IsBinaryTree T' → T' ⊆ 𝒞 → quartetSupport w T' ≤ quartetSupport w T
  value : astralValue w 𝒞 univ = ((2 * quartetSupport w T : ℝ) : WithBot ℝ)

/-- **Theorem 1 of Mirarab et al. 2014, its optimality part** ("ASTRAL finds an optimal solution to MQSST"), for any
rule for breaking ties: when `𝒞` is the family of the sides of a set of bipartitions, the tree that backtracking
produces from all the taxa is an optimum of the quartet score among the binary trees with sides in `𝒞`, and the
value of the recursion is twice its score. -/
theorem IsTraceback.isAstralOptimal (h : IsTraceback w 𝒞 univ R) (h𝒞 : ∀ A ∈ 𝒞, Aᶜ ∈ 𝒞) :
    IsAstralOptimal w 𝒞 (unroot R) := by
  obtain ⟨hR, hval⟩ := h.spec
  refine ⟨hR.isBinaryTree_unroot, hR.unroot_subset h𝒞, fun T hT hsub => ?_, ?_⟩
  · obtain ⟨H, hH, rfl⟩ := hT.exists_isBinaryClusterTree hsub
    have hle := hH.coe_treeWeight_le (w := w)
    rw [hval] at hle
    have hle' : treeWeight w H ≤ treeWeight w R := by exact_mod_cast hle
    have h1 := hH.two_mul_quartetSupport w
    have h2 := hR.two_mul_quartetSupport w
    linarith
  · rw [hval, hR.two_mul_quartetSupport w]

/-- If the search space is nonempty, then backtracking from all the taxa can run. -/
theorem astralValue_univ_ne_bot {T : Finset (Finset X)} (hT : IsBinaryTree T) (hsub : T ⊆ 𝒞) :
    astralValue w 𝒞 univ ≠ ⊥ := by
  obtain ⟨H, hH, -⟩ := hT.exists_isBinaryClusterTree hsub
  exact astralValue_ne_bot_iff.2 ⟨H, hH⟩

/-- **Theorem 1 of Mirarab et al. 2014, its optimality part**, for the output `astralTree`: when `𝒞` is the family of
the sides of a set of bipartitions and the search space is nonempty, the output is an optimum of the quartet
score among the binary trees with sides in `𝒞`. -/
theorem astralTree_isAstralOptimal (w : QuartetTree X → ℝ) (h𝒞 : ∀ A ∈ 𝒞, Aᶜ ∈ 𝒞)
    (hne : ∃ T, IsBinaryTree T ∧ T ⊆ 𝒞) : IsAstralOptimal w 𝒞 (astralTree w 𝒞) := by
  obtain ⟨T, hT, hsub⟩ := hne
  exact (isTraceback_astralTrace w 𝒞 (astralValue_univ_ne_bot hT hsub)).isAstralOptimal h𝒞

end Phylogenetics
