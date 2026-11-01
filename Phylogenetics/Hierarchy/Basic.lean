module

public import Phylogenetics.Hierarchy.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Common

/-!
# Hierarchies: clusters, children, parents, induced trees and splits

The combinatorics of a family of clusters `H` on a finite set, on its own: the results here assume
no edge lengths and no coalescent.

## Main results

* `IsHierarchy.subset_or_subset_of_mem`: clusters with a common element are nested.
* `lca H T`: the smallest cluster containing `T`; `IsHierarchy.lca_mem`, `subset_lca`,
  `lca_subset`, `IsHierarchy.lca_eq_iff`, `IsHierarchy.lca_pair_eq_of_mem_childClusters`.
* `mem_childClusters`, `IsHierarchy.disjoint_of_mem_childClusters`,
  `IsHierarchy.exists_mem_childClusters`, `IsHierarchy.sup_childClusters`,
  `IsHierarchy.two_le_card_childClusters`: the children of a cluster with at least two elements
  partition it; `IsHierarchy.childClusters_eq`, `IsHierarchy.childClusters_eq_pair`,
  `IsHierarchy.childClusters_eq_triple`: recognizing the children.
* `isBinaryHierarchy_iff_card_childClusters`: a hierarchy is binary if and only if every cluster
  with at least two elements has exactly two children.
* `IsHierarchy.subset_of_mem_childClusters`, `IsHierarchy.existsUnique_mem_childClusters`,
  `IsHierarchy.exists_mem_childClusters_superset`: every cluster strictly inside a cluster lies
  inside a child.
* `parentCluster H A`: the parent of a cluster; `IsHierarchy.parentCluster_mem`,
  `IsHierarchy.ssubset_parentCluster`, `parentCluster_subset`,
  `IsHierarchy.mem_childClusters_parentCluster`, `IsHierarchy.existsUnique_parent`.
* `IsHierarchy.mem_of_triples`: rooted triples determine the clusters of a hierarchy.
* `mem_restrictClusters`, `IsHierarchy.mem_restrictClusters_iff`, `subtype_lca_eq`: the clusters of
  an induced tree are the nonempty traces of clusters, and each is the trace of the smallest cluster
  containing it; `IsHierarchy.restrict`: an induced tree is a hierarchy.
* `mem_unroot`, `compl_mem_unroot`, `IsHierarchy.compatible_of_mem_unroot`: the splits of an unrooted
  tree are pairwise compatible; `mem_restrictSplits`, `unroot_restrictClusters`: unrooting commutes
  with restricting.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Children: first facts -/

theorem mem_childClusters {H : Finset (Finset X)} {A B : Finset X} :
    B ∈ childClusters H A ↔ B ∈ H ∧ B ⊂ A ∧ ∀ C ∈ H, B ⊂ C → ¬ C ⊂ A :=
  mem_filter

theorem childClusters_subset (H : Finset (Finset X)) (A : Finset X) : childClusters H A ⊆ H :=
  filter_subset _ _

/-- In a hierarchy, the children of a cluster with at least two elements partition it, and a
singleton has no children. -/
theorem IsHierarchy.childClusters_singleton {H : Finset (Finset X)} (hH : IsHierarchy H) (x : X) :
    childClusters H {x} = ∅ := by
  unfold childClusters
  rw [Finset.filter_eq_empty_iff]
  rintro B hB ⟨hBx, -⟩
  rw [Finset.ssubset_singleton_iff] at hBx
  subst hBx
  exact Finset.not_nonempty_empty (hH.2.2.1 _ hB)

/-- Two distinct children of a cluster of a hierarchy are disjoint. -/
theorem IsHierarchy.disjoint_of_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) (hBC : B ≠ C) :
    Disjoint B C := by
  rw [mem_childClusters] at hB hC
  rcases hH.2.2.2 B hB.1 C hC.1 with h | h | h
  · exact absurd hC.2.1 (hB.2.2 C hC.1 (lt_of_le_of_ne h hBC))
  · exact absurd hB.2.1 (hC.2.2 B hB.1 (lt_of_le_of_ne h hBC.symm))
  · exact h

/-! ### Clusters with a common element are nested -/

namespace IsHierarchy

variable {H : Finset (Finset X)}

omit [DecidableEq X] in
/-- Two clusters of a hierarchy with a common element are nested. -/
theorem subset_or_subset_of_mem (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H) (hB : B ∈ H)
    {x : X} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hH.2.2.2 A hA B hB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hxB (disjoint_left.1 h hxA)

omit [DecidableEq X] in
/-- Two clusters of a hierarchy that are not disjoint are nested. -/
theorem subset_or_subset_of_not_disjoint (hH : IsHierarchy H) {A B : Finset X} (hA : A ∈ H)
    (hB : B ∈ H) (hAB : ¬ Disjoint A B) : A ⊆ B ∨ B ⊆ A := by
  obtain ⟨x, hxA, hxB⟩ := not_disjoint_iff.1 hAB
  exact hH.subset_or_subset_of_mem hA hB hxA hxB

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under union (the union of two of them is one of them). -/
private theorem hier_sup_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊔ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [sup_eq_right.2 h]
  · rwa [sup_eq_left.2 h]

/-- The clusters of a hierarchy containing a common element `x` and satisfying `p` are closed
under intersection. -/
private theorem hier_inf_mem (hH : IsHierarchy H) (x : X) (p : Finset X → Prop) :
    ∀ C ∈ {C | C ∈ H ∧ x ∈ C ∧ p C}, ∀ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C},
      C ⊓ D ∈ {C | C ∈ H ∧ x ∈ C ∧ p C} := by
  rintro C hC D hD
  rcases hH.subset_or_subset_of_mem hC.1 hD.1 hC.2.1 hD.2.1 with h | h
  · rwa [inf_eq_left.2 h]
  · rwa [inf_eq_right.2 h]

end IsHierarchy

/-! ### The smallest cluster containing a set -/

/-- The smallest cluster of `H` containing `T`: the intersection of the clusters of `H` that
contain `T`. For a hierarchy `H` and a nonempty `T` it is a cluster of `H` (`IsHierarchy.lca_mem`),
the cluster of the most recent common ancestor of the taxa in `T`. -/
def lca (H : Finset (Finset X)) (T : Finset X) : Finset X :=
  (H.filter (T ⊆ ·)).inf id

/-- A set is contained in the smallest cluster containing it. -/
theorem subset_lca (H : Finset (Finset X)) (T : Finset X) : T ⊆ lca H T :=
  Finset.le_inf fun _ hC => (mem_filter.1 hC).2

/-- The smallest cluster containing `T` is contained in every cluster containing `T`. -/
theorem lca_subset {H : Finset (Finset X)} {T C : Finset X} (hC : C ∈ H) (hTC : T ⊆ C) :
    lca H T ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hTC⟩)

/-- Characterization of the clusters containing the smallest cluster containing `T`. -/
theorem lca_subset_iff {H : Finset (Finset X)} {T C : Finset X} (hC : C ∈ H) :
    lca H T ⊆ C ↔ T ⊆ C :=
  ⟨fun h => (subset_lca H T).trans h, lca_subset hC⟩

/-- The smallest cluster containing a set is monotone in the set. -/
theorem lca_mono (H : Finset (Finset X)) {T T' : Finset X} (h : T ⊆ T') : lca H T ⊆ lca H T' :=
  Finset.le_inf fun _ hC => lca_subset (mem_filter.1 hC).1 (h.trans (mem_filter.1 hC).2)

/-- The smallest cluster containing a cluster is the cluster itself. -/
theorem lca_of_mem {H : Finset (Finset X)} {A : Finset X} (hA : A ∈ H) : lca H A = A :=
  Subset.antisymm (lca_subset hA Subset.rfl) (subset_lca H A)

namespace IsHierarchy

variable {H : Finset (Finset X)}

/-- In a hierarchy, the smallest cluster containing a nonempty set is a cluster. -/
theorem lca_mem (hH : IsHierarchy H) {T : Finset X} (hT : T.Nonempty) : lca H T ∈ H := by
  obtain ⟨t, ht⟩ := hT
  have := Finset.inf_mem {C | C ∈ H ∧ t ∈ C ∧ T ⊆ C} ⟨hH.1, mem_univ t, subset_univ T⟩
    (hier_inf_mem hH t (T ⊆ ·)) (H.filter (T ⊆ ·)) id
    (fun C hC => ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2 ht, (mem_filter.1 hC).2⟩)
  exact this.1

/-- Characterization of the smallest cluster containing a nonempty set. -/
theorem lca_eq_iff (hH : IsHierarchy H) {T C : Finset X} (hT : T.Nonempty) :
    lca H T = C ↔ C ∈ H ∧ T ⊆ C ∧ ∀ D ∈ H, T ⊆ D → C ⊆ D := by
  constructor
  · rintro rfl
    exact ⟨hH.lca_mem hT, subset_lca H T, fun D hD hTD => lca_subset hD hTD⟩
  · rintro ⟨hC, hTC, hmin⟩
    exact Subset.antisymm (lca_subset hC hTC) (hmin _ (hH.lca_mem hT) (subset_lca H T))

end IsHierarchy

/-! ### The children of a cluster of a hierarchy -/

/-- Every element of a cluster `A` with at least two elements lies in a child of `A`. -/
theorem IsHierarchy.exists_mem_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) {x : X} (hx : x ∈ A) : ∃ B ∈ childClusters H A, x ∈ B := by
  have hxA : ({x} : Finset X) ⊂ A := by
    refine (singleton_subset_iff.2 hx).ssubset_of_ne ?_
    rintro rfl
    simp at hA
  obtain ⟨B, hB, hmax⟩ := (H.filter fun C => x ∈ C ∧ C ⊂ A).exists_max_image card
    ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x, hxA⟩⟩
  rw [mem_filter] at hB
  refine ⟨B, mem_childClusters.2 ⟨hB.1, hB.2.2, fun C hC hBC hCA => ?_⟩, hB.2.1⟩
  have := hmax C (mem_filter.2 ⟨hC, hBC.subset hB.2.1, hCA⟩)
  exact absurd (card_lt_card hBC) (not_lt.2 this)

/-- The children of a cluster `A` with at least two elements cover it. -/
theorem IsHierarchy.sup_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : (childClusters H A).sup id = A := by
  refine le_antisymm (Finset.sup_le fun B hB => (mem_childClusters.1 hB).2.1.subset) ?_
  intro x hx
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA hx
  exact Finset.mem_sup.2 ⟨B, hB, hxB⟩

/-- The children of a cluster are pairwise disjoint. -/
theorem IsHierarchy.pairwiseDisjoint_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    (A : Finset X) : (childClusters H A : Set (Finset X)).PairwiseDisjoint id :=
  fun _ hB _ hC hBC => hH.disjoint_of_mem_childClusters hB hC hBC

/-- A cluster with at least two elements has at least two children. -/
theorem IsHierarchy.two_le_card_childClusters {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} (hA : 2 ≤ #A) : 2 ≤ #(childClusters H A) := by
  by_contra hlt
  have hle : #(childClusters H A) ≤ 1 := by omega
  obtain ⟨x, hx⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨B, hB, -⟩ := hH.exists_mem_childClusters hA hx
  rw [Finset.card_le_one_iff] at hle
  have hAB : A ⊆ B := fun y hy => by
    obtain ⟨C, hC, hyC⟩ := hH.exists_mem_childClusters hA hy
    exact hle hC hB ▸ hyC
  exact not_subset_of_ssubset (mem_childClusters.1 hB).2.1 hAB

/-- A characterization of the children: a family `T ⊆ H` of at least two pairwise disjoint
clusters covering `A`, such that every cluster of `H` strictly inside `A` lies inside one of
them, is the family of children of `A`. -/
theorem IsHierarchy.childClusters_eq {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A : Finset X} {T : Finset (Finset X)} (hT : T ⊆ H)
    (hdisj : (T : Set (Finset X)).PairwiseDisjoint id) (hsup : T.sup id = A) (h2 : 2 ≤ #T)
    (hcov : ∀ E ∈ H, E ⊂ A → ∃ B ∈ T, E ⊆ B) : childClusters H A = T := by
  have hsubA : ∀ B ∈ T, B ⊆ A := fun B hB => hsup ▸ le_sup (f := id) hB
  have hssubA : ∀ B ∈ T, B ⊂ A := by
    intro B hB
    refine (hsubA B hB).ssubset_of_ne ?_
    rintro rfl
    obtain ⟨C, hC, hCB⟩ := exists_mem_ne (by omega : 1 < #T) B
    have hdis : Disjoint C B := hdisj hC hB hCB
    obtain ⟨y, hy⟩ := hH.2.2.1 C (hT hC)
    exact Finset.disjoint_left.1 hdis hy (hsubA C hC hy)
  have heq : ∀ B ∈ T, ∀ B' ∈ T, ∀ E ∈ H, B ⊆ E → E ⊆ B' → B = B' := by
    intro B hB B' hB' E hE hBE hEB'
    by_contra hne
    obtain ⟨y, hy⟩ := hH.2.2.1 B (hT hB)
    exact Finset.disjoint_left.1 (hdisj hB hB' hne) hy (hEB' (hBE hy))
  ext B
  constructor
  · intro hB
    obtain ⟨hBH, hBA, hmax⟩ := mem_childClusters.1 hB
    obtain ⟨B', hB', hBB'⟩ := hcov B hBH hBA
    rcases hBB'.eq_or_ssubset with h | h
    · exact h ▸ hB'
    · exact absurd (hssubA B' hB') (hmax B' (hT hB') h)
  · intro hB
    refine mem_childClusters.2 ⟨hT hB, hssubA B hB, fun C hC hBC hCA => ?_⟩
    obtain ⟨B', hB', hCB'⟩ := hcov C hC hCA
    have := heq B hB B' hB' C hC hBC.subset hCB'
    subst this
    exact absurd (hBC.trans_le hCB') (lt_irrefl _)

/-- Two disjoint clusters whose union is `A` are the children of `A`. -/
theorem IsHierarchy.childClusters_eq_pair {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) (hA : B ∪ C = A) :
    childClusters H A = {B, C} := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  have hne : B ≠ C := by
    rintro rfl
    exact Finset.disjoint_left.1 hBC hb hb
  refine hH.childClusters_eq (by simp [insert_subset_iff, hB, hC]) ?_ (by simp [hA]) ?_ ?_
  · intro P hP Q hQ hPQ
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hP hQ
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
    · exact absurd rfl hPQ
    · exact hBC
    · exact hBC.symm
    · exact absurd rfl hPQ
  · rw [card_pair hne]
  · intro E hE hEA
    simp only [mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
    by_cases hEC : Disjoint E C
    · left
      intro y hy
      have := hEA.subset hy
      rw [← hA, mem_union] at this
      exact this.resolve_right (Finset.disjoint_left.1 hEC hy)
    by_cases hEB : Disjoint E B
    · right
      intro y hy
      have := hEA.subset hy
      rw [← hA, mem_union] at this
      exact this.resolve_left (Finset.disjoint_left.1 hEB hy)
    exfalso
    obtain ⟨y, hyE, hyB⟩ := Finset.not_disjoint_iff.1 hEB
    obtain ⟨z, hzE, hzC⟩ := Finset.not_disjoint_iff.1 hEC
    have hBE : B ⊆ E := by
      rcases hH.2.2.2 E hE B hB with h | h | h
      · exact absurd (h hzE) (Finset.disjoint_right.1 hBC hzC)
      · exact h
      · exact absurd hyB (Finset.disjoint_left.1 h hyE)
    have hCE : C ⊆ E := by
      rcases hH.2.2.2 E hE C hC with h | h | h
      · exact absurd (h hyE) (Finset.disjoint_left.1 hBC hyB)
      · exact h
      · exact absurd hzC (Finset.disjoint_left.1 h hzE)
    exact not_subset_of_ssubset hEA (hA ▸ union_subset hBE hCE)

/-- Three pairwise disjoint clusters whose union is `A`, no two of which have a union in the
hierarchy, are the children of `A`. -/
theorem IsHierarchy.childClusters_eq_triple {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B C D : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hD : D ∈ H) (hBC : Disjoint B C)
    (hBD : Disjoint B D) (hCD : Disjoint C D) (hA : B ∪ C ∪ D = A) (hBC' : B ∪ C ∉ H)
    (hBD' : B ∪ D ∉ H) (hCD' : C ∪ D ∉ H) : childClusters H A = {B, C, D} := by
  have hne : ∀ {P Q : Finset X}, P ∈ H → Disjoint P Q → P ≠ Q := by
    intro P Q hP hPQ h
    subst h
    obtain ⟨y, hy⟩ := hH.2.2.1 P hP
    exact Finset.disjoint_left.1 hPQ hy hy
  have hBC0 := hne hB hBC
  have hBD0 := hne hB hBD
  have hCD0 := hne hC hCD
  refine hH.childClusters_eq (by simp [insert_subset_iff, hB, hC, hD]) ?_ ?_ ?_ ?_
  · intro P hP Q hQ hPQ
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hP hQ
    rcases hP with rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hPQ
      | exact hBC | exact hBC.symm | exact hBD | exact hBD.symm | exact hCD | exact hCD.symm
  · simp [← hA, union_assoc]
  · rw [card_insert_of_notMem (by simp [hBC0, hBD0]), card_pair hCD0]
    omega
  · intro E hE hEA
    simp only [mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left]
    by_contra hcon
    rw [not_or, not_or] at hcon
    have key : ∀ P ∈ H, ¬ E ⊆ P → P ⊆ E ∨ Disjoint E P := fun P hP h => by
      rcases hH.2.2.2 E hE P hP with h' | h' | h'
      · exact absurd h' h
      · exact Or.inl h'
      · exact Or.inr h'
    have hEsub : ∀ x ∈ E, x ∈ B ∨ x ∈ C ∨ x ∈ D := fun x hx => by
      have := hEA.subset hx
      rw [← hA] at this
      simpa [or_assoc] using this
    obtain ⟨y, hy⟩ := hH.2.2.1 E hE
    rcases key B hB hcon.1 with hB' | hB' <;> rcases key C hC hcon.2.1 with hC' | hC' <;>
      rcases key D hD hcon.2.2 with hD' | hD'
    · exact not_subset_of_ssubset hEA (hA ▸ union_subset (union_subset hB' hC') hD')
    · refine hBC' ?_
      have : E = B ∪ C := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact mem_union_left _ h
          · exact mem_union_right _ h
          · exact absurd h (Finset.disjoint_left.1 hD' hx)
        · rcases mem_union.1 hx with h | h
          · exact hB' h
          · exact hC' h
      exact this ▸ hE
    · refine hBD' ?_
      have : E = B ∪ D := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact mem_union_left _ h
          · exact absurd h (Finset.disjoint_left.1 hC' hx)
          · exact mem_union_right _ h
        · rcases mem_union.1 hx with h | h
          · exact hB' h
          · exact hD' h
      exact this ▸ hE
    · refine hcon.1 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.1 hC' hx)
      · exact absurd h (Finset.disjoint_left.1 hD' hx)
    · refine hCD' ?_
      have : E = C ∪ D := by
        ext x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases hEsub x hx with h | h | h
          · exact absurd h (Finset.disjoint_left.1 hB' hx)
          · exact mem_union_left _ h
          · exact mem_union_right _ h
        · rcases mem_union.1 hx with h | h
          · exact hC' h
          · exact hD' h
      exact this ▸ hE
    · refine hcon.2.1 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact absurd h (Finset.disjoint_left.1 hB' hx)
      · exact h
      · exact absurd h (Finset.disjoint_left.1 hD' hx)
    · refine hcon.2.2 fun x hx => ?_
      rcases hEsub x hx with h | h | h
      · exact absurd h (Finset.disjoint_left.1 hB' hx)
      · exact absurd h (Finset.disjoint_left.1 hC' hx)
      · exact h
    · rcases hEsub y hy with h | h | h
      · exact Finset.disjoint_left.1 hB' hy h
      · exact Finset.disjoint_left.1 hC' hy h
      · exact Finset.disjoint_left.1 hD' hy h

/-- A hierarchy is binary if and only if every cluster with at least two elements has exactly two
children. -/
theorem isBinaryHierarchy_iff_card_childClusters {G : Finset (Finset X)} :
    IsBinaryHierarchy G ↔ IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → #(childClusters G A) = 2 := by
  refine and_congr_right fun hG => forall₂_congr fun A hA => imp_congr_right fun hA2 => ?_
  constructor
  · rintro ⟨B, hB, C, hC, hBC, hBCA⟩
    rw [hG.childClusters_eq_pair hB hC hBC hBCA]
    refine card_pair fun h => ?_
    subst h
    obtain ⟨y, hy⟩ := hG.2.2.1 B hB
    exact Finset.disjoint_left.1 hBC hy hy
  · intro h
    obtain ⟨B, C, hBC, hch⟩ := card_eq_two.1 h
    have hB : B ∈ childClusters G A := hch ▸ mem_insert_self _ _
    have hC : C ∈ childClusters G A := hch ▸ mem_insert_of_mem (mem_singleton_self _)
    refine ⟨B, (mem_childClusters.1 hB).1, C, (mem_childClusters.1 hC).1,
      hG.disjoint_of_mem_childClusters hB hC hBC, ?_⟩
    have := hG.sup_childClusters hA2
    rwa [hch, sup_insert, sup_singleton] at this

/-! ### Children -/

namespace IsHierarchy

variable {H : Finset (Finset X)}

/-- A cluster strictly contained in `A` that meets a child `B` of `A` is contained in `B`. -/
theorem subset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ H) (hCA : C ⊂ A) (hBC : ¬ Disjoint B C) : C ⊆ B := by
  rw [mem_childClusters] at hB
  rcases hH.subset_or_subset_of_not_disjoint hB.1 hC hBC with h | h
  · by_contra hCB
    exact hB.2.2 C hC (ssubset_of_subset_not_subset h hCB) hCA
  · exact h

/-- Every element `x` of a cluster `A ≠ {x}` lies in a child of `A` (the cluster `A` need not be a
member of `H`). -/
theorem exists_mem_childClusters_of_ne (hH : IsHierarchy H) {A : Finset X} {x : X} (hx : x ∈ A)
    (hAx : A ≠ {x}) : ∃ B ∈ childClusters H A, x ∈ B := by
  set F := H.filter (fun C => x ∈ C ∧ C ⊂ A)
  have hF : F.Nonempty := ⟨{x}, mem_filter.2 ⟨hH.2.1 x, mem_singleton_self x,
    ssubset_of_subset_not_subset (singleton_subset_iff.2 hx)
      (fun h => hAx (Subset.antisymm h (singleton_subset_iff.2 hx)))⟩⟩
  have hmem : F.sup' hF id ∈ {C | C ∈ H ∧ x ∈ C ∧ C ⊂ A} :=
    Finset.sup'_mem _ (hier_sup_mem hH x (· ⊂ A)) F hF id (fun C hC => mem_filter.1 hC)
  refine ⟨F.sup' hF id, mem_childClusters.2 ⟨hmem.1, hmem.2.2, fun C hC hBC hCA => ?_⟩,
    hmem.2.1⟩
  have : C ⊆ F.sup' hF id :=
    Finset.le_sup' id (mem_filter.2 ⟨hC, hBC.subset hmem.2.1, hCA⟩)
  exact not_subset_of_ssubset hBC this

/-- The children of a cluster with at least two elements partition it: every element lies in
exactly one child. -/
theorem existsUnique_mem_childClusters (hH : IsHierarchy H) {A : Finset X} (hA : 2 ≤ #A)
    {x : X} (hx : x ∈ A) : ∃! B, B ∈ childClusters H A ∧ x ∈ B := by
  obtain ⟨B, hB, hxB⟩ := hH.exists_mem_childClusters hA hx
  refine ⟨B, ⟨hB, hxB⟩, fun C ⟨hC, hxC⟩ => ?_⟩
  by_contra hCB
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hC hB hCB) hxC hxB

/-- A cluster strictly contained in `A` is contained in a child of `A`. -/
theorem exists_mem_childClusters_superset (hH : IsHierarchy H) {A B : Finset X} (hB : B ∈ H)
    (hBA : B ⊂ A) : ∃ C ∈ childClusters H A, B ⊆ C := by
  obtain ⟨b, hb⟩ := hH.2.2.1 B hB
  have hAb : A ≠ {b} := by
    rintro rfl
    exact not_subset_of_ssubset hBA (singleton_subset_iff.2 hb)
  obtain ⟨C, hC, hbC⟩ := hH.exists_mem_childClusters_of_ne (hBA.subset hb) hAb
  exact ⟨C, hC, hH.subset_of_mem_childClusters hC hB hBA (not_disjoint_iff.2 ⟨b, hbC, hb⟩)⟩

/-- Two taxa in different children of a cluster `A` have `A` as their smallest common cluster. -/
theorem lca_pair_eq_of_mem_childClusters (hH : IsHierarchy H) {A B₁ B₂ : Finset X} (hA : A ∈ H)
    (hB₁ : B₁ ∈ childClusters H A) (hB₂ : B₂ ∈ childClusters H A) (hne : B₁ ≠ B₂) {a₁ a₂ : X}
    (ha₁ : a₁ ∈ B₁) (ha₂ : a₂ ∈ B₂) : lca H {a₁, a₂} = A := by
  have hA₁ : a₁ ∈ A := (mem_childClusters.1 hB₁).2.1.subset ha₁
  have hA₂ : a₂ ∈ A := (mem_childClusters.1 hB₂).2.1.subset ha₂
  refine (hH.lca_eq_iff (insert_nonempty a₁ {a₂})).2 ⟨hA, ?_, fun D hD hsub => ?_⟩
  · rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨hA₁, hA₂⟩
  · rw [insert_subset_iff, singleton_subset_iff] at hsub
    rcases hH.subset_or_subset_of_mem hD hA hsub.1 hA₁ with h | h
    · by_contra hDA
      have hD' : D ⊂ A := ssubset_of_subset_not_subset h fun h' => hDA h'
      have h₁ := hH.subset_of_mem_childClusters hB₁ hD hD'
        (not_disjoint_iff.2 ⟨a₁, ha₁, hsub.1⟩)
      exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB₁ hB₂ hne) (h₁ hsub.2) ha₂
    · exact h

end IsHierarchy

/-! ### Parents -/

/-- The parent of a cluster `A` of `H`: the smallest cluster of `H` strictly containing `A` (the
intersection of the clusters of `H` strictly containing `A`). -/
def parentCluster (H : Finset (Finset X)) (A : Finset X) : Finset X :=
  (H.filter (A ⊂ ·)).inf id

/-- The parent of `A` is contained in every cluster strictly containing `A`. -/
theorem parentCluster_subset {H : Finset (Finset X)} {A C : Finset X} (hC : C ∈ H)
    (hAC : A ⊂ C) : parentCluster H A ⊆ C :=
  Finset.inf_le (f := id) (mem_filter.2 ⟨hC, hAC⟩)

namespace IsHierarchy

variable {H : Finset (Finset X)}

private theorem hier_parentCluster_aux (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : parentCluster H A ∈ H ∧ A ⊂ parentCluster H A := by
  obtain ⟨a, ha⟩ := hH.2.2.1 A hA
  have := Finset.inf_mem {C | C ∈ H ∧ a ∈ C ∧ A ⊂ C} ⟨hH.1, mem_univ a, ssubset_univ_iff.2 hAu⟩
    (hier_inf_mem hH a (A ⊂ ·)) (H.filter (A ⊂ ·)) id
    (fun C hC => ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2.subset ha, (mem_filter.1 hC).2⟩)
  exact ⟨this.1, this.2.2⟩

/-- The parent of a cluster other than `univ` is a cluster. -/
theorem parentCluster_mem (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H) (hAu : A ≠ univ) :
    parentCluster H A ∈ H :=
  (hier_parentCluster_aux hH hA hAu).1

/-- A cluster other than `univ` is strictly contained in its parent. -/
theorem ssubset_parentCluster (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : A ⊂ parentCluster H A :=
  (hier_parentCluster_aux hH hA hAu).2

/-- A cluster other than `univ` is a child of its parent. -/
theorem mem_childClusters_parentCluster (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H)
    (hAu : A ≠ univ) : A ∈ childClusters H (parentCluster H A) :=
  mem_childClusters.2 ⟨hA, hH.ssubset_parentCluster hA hAu,
    fun _ hC hAC hCP => not_subset_of_ssubset hCP (parentCluster_subset hC hAC)⟩

/-- The parent of a child of a cluster `P` is `P`. -/
theorem parentCluster_eq_of_mem_childClusters (hH : IsHierarchy H) {A P : Finset X}
    (hP : P ∈ H) (h : A ∈ childClusters H P) : parentCluster H A = P := by
  obtain ⟨hA, hAP, hmax⟩ := mem_childClusters.1 h
  have hAu : A ≠ univ := fun e => not_subset_of_ssubset hAP (e ▸ subset_univ P)
  have hPm := hH.parentCluster_mem hA hAu
  have hAPm := hH.ssubset_parentCluster hA hAu
  obtain ⟨a, ha⟩ := hH.2.2.1 A hA
  apply Subset.antisymm (parentCluster_subset hP hAP)
  rcases hH.subset_or_subset_of_mem hP hPm (hAP.subset ha) (hAPm.subset ha) with h1 | h1
  · exact h1
  · by_contra h2
    exact hmax _ hPm hAPm (ssubset_of_subset_not_subset h1 h2)

/-- Every cluster other than `univ` has a unique parent. -/
theorem existsUnique_parent (hH : IsHierarchy H) {A : Finset X} (hA : A ∈ H) (hAu : A ≠ univ) :
    ∃! P, P ∈ H ∧ A ∈ childClusters H P :=
  ⟨parentCluster H A, ⟨hH.parentCluster_mem hA hAu, hH.mem_childClusters_parentCluster hA hAu⟩,
    fun _ ⟨hP, h⟩ => (hH.parentCluster_eq_of_mem_childClusters hP h).symm⟩

end IsHierarchy

/-! ### Induced subtrees -/

omit [Fintype X] in
/-- The clusters of the induced tree on `S` are the nonempty traces on `S` of the clusters. -/
theorem mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictClusters S H ↔ ∃ A ∈ H, (A ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictClusters
  rw [mem_image]
  simp only [mem_filter, and_assoc]

/-- The splits of the induced unrooted tree on `S` are the traces of the splits whose two sides
both meet `S`. -/
theorem mem_restrictSplits {S : Finset X} {T : Finset (Finset X)} {C : Finset S} :
    C ∈ restrictSplits S T ↔
      ∃ A ∈ T, (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty ∧ A.subtype (· ∈ S) = C := by
  unfold restrictSplits
  rw [mem_image]
  simp only [mem_filter, and_assoc]

omit [Fintype X] in
/-- The trace of `A` on `S` is nonempty if and only if `A` meets `S`. -/
theorem subtype_nonempty_iff {S A : Finset X} :
    (A.subtype (· ∈ S)).Nonempty ↔ (A ∩ S).Nonempty := by
  constructor
  · rintro ⟨⟨x, hxS⟩, hx⟩
    exact ⟨x, mem_inter.2 ⟨mem_subtype.1 hx, hxS⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, (mem_inter.1 hx).2⟩, mem_subtype.2 (mem_inter.1 hx).1⟩

/-- The trace of the complement is the complement of the trace. -/
theorem subtype_compl {S : Finset X} (A : Finset X) :
    Aᶜ.subtype (· ∈ S) = (A.subtype (· ∈ S))ᶜ := by
  ext x
  simp [mem_subtype, mem_compl]

/-- The trace of `A` on `S` is not all of `S` if and only if `Aᶜ` meets `S`. -/
theorem subtype_ne_univ_iff {S A : Finset X} :
    A.subtype (· ∈ S) ≠ univ ↔ (Aᶜ ∩ S).Nonempty := by
  rw [← subtype_nonempty_iff, subtype_compl, Ne, ← compl_eq_empty_iff,
    ← not_nonempty_iff_eq_empty, not_not]

omit [Fintype X] in
/-- Mapping the trace of `A` on `S` (a set of elements of `S`) back to `X` gives `A ∩ S`. -/
theorem map_subtype_eq_inter (S A : Finset X) :
    (A.subtype (· ∈ S)).map (Function.Embedding.subtype _) = A ∩ S := by
  rw [subtype_map, filter_mem_eq_inter]

omit [Fintype X] in
/-- The trace of a cluster meeting `S` is a cluster of the induced tree on `S`. -/
theorem subtype_mem_restrictClusters {S : Finset X} {H : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ H) (hAS : (A ∩ S).Nonempty) : A.subtype (· ∈ S) ∈ restrictClusters S H :=
  mem_restrictClusters.2 ⟨A, hA, hAS, rfl⟩

/-- A cluster `C` of the induced tree on `S` is the trace of the smallest cluster containing it. -/
theorem subtype_lca_eq {S : Finset X} {H : Finset (Finset X)} {C : Finset S}
    (hC : C ∈ restrictClusters S H) :
    (lca H (C.map (Function.Embedding.subtype _))).subtype (· ∈ S) = C := by
  obtain ⟨A, hA, -, rfl⟩ := mem_restrictClusters.1 hC
  apply Subset.antisymm
  · intro x hx
    rw [mem_subtype] at hx ⊢
    apply lca_subset hA _ hx
    rw [map_subtype_eq_inter]
    exact inter_subset_left
  · intro x hx
    rw [mem_subtype]
    apply subset_lca
    exact mem_map_of_mem _ hx

/-- In a hierarchy, the clusters of the induced tree on `S` are exactly the nonempty `C` that are
the trace of the smallest cluster containing them. -/
theorem IsHierarchy.mem_restrictClusters_iff {H : Finset (Finset X)} (hH : IsHierarchy H)
    {S : Finset X} {C : Finset S} :
    C ∈ restrictClusters S H ↔
      C.Nonempty ∧ (lca H (C.map (Function.Embedding.subtype _))).subtype (· ∈ S) = C := by
  constructor
  · intro hC
    obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
    exact ⟨subtype_nonempty_iff.2 hAS, subtype_lca_eq hC⟩
  · rintro ⟨hne, h⟩
    rw [← h]
    refine subtype_mem_restrictClusters (hH.lca_mem hne.map) ?_
    rw [← subtype_nonempty_iff, h]
    exact hne

/-- Restricting a hierarchy to a nonempty set of taxa preserves all hierarchy laws. -/
theorem IsHierarchy.restrict {H : Finset (Finset X)} (hH : IsHierarchy H)
    (S : Finset X) (hS : S.Nonempty) : IsHierarchy (restrictClusters S H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold restrictClusters
    rw [mem_image]
    refine ⟨univ, mem_filter.2 ⟨hH.1, by simpa using hS⟩, ?_⟩
    simp
  · intro x
    unfold restrictClusters
    rw [mem_image]
    refine ⟨{x.1}, mem_filter.2 ⟨hH.2.1 x.1, ⟨x.1, by simp [x.2]⟩⟩, ?_⟩
    ext ⟨y, hy⟩
    rw [mem_subtype, mem_singleton, mem_singleton, Subtype.ext_iff]
  · intro C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨y, hy⟩ := (mem_filter.1 hA).2
    rw [mem_inter] at hy
    exact ⟨⟨y, hy.2⟩, by simp [hy.1]⟩
  · intro C hC D hD
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
    rcases hH.2.2.2 A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 with h | h | h
    · exact Or.inl (subtype_mono h)
    · exact Or.inr (Or.inl (subtype_mono h))
    · refine Or.inr (Or.inr ?_)
      rw [Finset.disjoint_left] at h ⊢
      intro a ha hb
      exact h (mem_subtype.1 ha) (mem_subtype.1 hb)


/-! ### Unrooted trees -/

section Unroot

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sides of the splits of the unrooted tree of `G`: the non-root clusters of `G` and their
complements. -/
theorem mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    A ∈ unroot G ↔ (A ∈ G ∧ A ≠ univ) ∨ (Aᶜ ∈ G ∧ Aᶜ ≠ univ) := by
  unfold unroot
  simp only [mem_union, mem_erase, mem_image]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨B, ⟨hB1, hB2⟩, rfl⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨by rwa [compl_compl], by rwa [compl_compl]⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨Aᶜ, ⟨h2, h1⟩, compl_compl A⟩

/-- The unrooted tree of `G` is closed under complements. -/
theorem compl_mem_unroot {G : Finset (Finset L)} {A : Finset L} :
    Aᶜ ∈ unroot G ↔ A ∈ unroot G := by
  rw [mem_unroot, mem_unroot, compl_compl, or_comm]

end Unroot

/-- Compatibility of two sets of taxa is symmetric. -/
theorem compatible_symm {A B : Finset X}
    (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) :
    B ⊆ A ∨ A ⊆ B ∨ Disjoint B A ∨ B ∪ A = univ := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (union_comm A B ▸ h)))

/-- Compatibility of two sets of taxa is preserved by complementing one of them. -/
private theorem hier_compat_compl {A B : Finset X}
    (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) :
    Aᶜ ⊆ B ∨ B ⊆ Aᶜ ∨ Disjoint Aᶜ B ∨ Aᶜ ∪ B = univ := by
  rcases h with h | h | h | h
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    by_cases hx : x ∈ A
    · exact mem_union_right _ (h hx)
    · exact mem_union_left _ (mem_compl.2 hx)
  · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hxA hxB => mem_compl.1 hxA (h hxB))))
  · exact Or.inr (Or.inl fun x hxB => mem_compl.2 fun hxA => disjoint_left.1 h hxA hxB)
  · refine Or.inl fun x hx => ?_
    have : x ∈ A ∪ B := h ▸ mem_univ x
    exact (mem_union.1 this).resolve_left (mem_compl.1 hx)

/-- The splits of the unrooted tree of a hierarchy are pairwise compatible: for two sides `A`, `B`
of splits, one contains the other, or they are disjoint, or they cover all taxa. -/
theorem IsHierarchy.compatible_of_mem_unroot {H : Finset (Finset X)} (hH : IsHierarchy H)
    {A B : Finset X} (hA : A ∈ unroot H) (hB : B ∈ unroot H) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ := by
  have base : ∀ P ∈ H, ∀ Q ∈ H, P ⊆ Q ∨ Q ⊆ P ∨ Disjoint P Q ∨ P ∪ Q = univ :=
    fun P hP Q hQ => by
      rcases hH.2.2.2 P hP Q hQ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  have right : ∀ A B : Finset X, (A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ) →
      A ⊆ Bᶜ ∨ Bᶜ ⊆ A ∨ Disjoint A Bᶜ ∨ A ∪ Bᶜ = univ :=
    fun A B h => compatible_symm (hier_compat_compl (compatible_symm h))
  rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩ <;>
    rcases mem_unroot.1 hB with ⟨hB', -⟩ | ⟨hB', -⟩
  · exact base A hA' B hB'
  · simpa only [compl_compl] using right A Bᶜ (base A hA' Bᶜ hB')
  · simpa only [compl_compl] using hier_compat_compl (base Aᶜ hA' B hB')
  · simpa only [compl_compl] using right _ _ (hier_compat_compl (base Aᶜ hA' Bᶜ hB'))

/-! ### Rooted triples -/

/-- Rooted triples determine the clusters of a hierarchy: if for all `a, a' ∈ A` and `b ∉ A` some
cluster of `H` contains `a` and `a'` but not `b`, then `A` is a cluster of `H`. -/
theorem IsHierarchy.mem_of_triples {H : Finset (Finset X)} (hH : IsHierarchy H) {A : Finset X}
    (hA : A.Nonempty) (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ H, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ H := by
  obtain ⟨a, ha⟩ := hA
  suffices hsub : lca H A ⊆ A by
    rw [← Subset.antisymm hsub (subset_lca _ A)]
    exact hH.lca_mem ⟨a, ha⟩
  intro b hbL
  by_contra hbA
  -- the clusters containing `a` but not `b` form a chain; its largest member contains `A`
  set F := H.filter (fun C => a ∈ C ∧ b ∉ C)
  obtain ⟨C₀, hC₀, haC₀, -, hbC₀⟩ := h a ha a ha b hbA
  have hF : F.Nonempty := ⟨C₀, mem_filter.2 ⟨hC₀, haC₀, hbC₀⟩⟩
  have hU : F.sup' hF id ∈ {C | C ∈ H ∧ a ∈ C ∧ b ∉ C} :=
    Finset.sup'_mem _ (IsHierarchy.hier_sup_mem hH a (b ∉ ·)) F hF id
      (fun C hC => mem_filter.1 hC)
  have hAU : A ⊆ F.sup' hF id := fun a' ha' => by
    obtain ⟨C, hC, haC, ha'C, hbC⟩ := h a ha a' ha' b hbA
    exact Finset.le_sup' id (mem_filter.2 ⟨hC, haC, hbC⟩) ha'C
  exact hU.2.2 (lca_subset hU.1 hAU hbL)

/-- Restricting clusters and then taking split sides agrees with restricting split sides. -/
theorem unroot_restrictClusters (H : Finset (Finset X)) (S : Finset X) :
    unroot (restrictClusters S H) = restrictSplits S (unroot H) := by
  ext C
  rw [mem_unroot, mem_restrictSplits]
  constructor
  · rintro (⟨hC, hCu⟩ | ⟨hC, hCu⟩)
    · obtain ⟨A, hA, hAS, rfl⟩ := mem_restrictClusters.1 hC
      refine ⟨A, mem_unroot.2 (Or.inl ⟨hA, ?_⟩), hAS, subtype_ne_univ_iff.1 hCu, rfl⟩
      rintro rfl
      exact hCu (subtype_univ _)
    · obtain ⟨A, hA, hAS, hAC⟩ := mem_restrictClusters.1 hC
      have hAu : A ≠ univ := by
        rintro rfl
        exact hCu (hAC ▸ subtype_univ _)
      refine ⟨Aᶜ, compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hA, hAu⟩)),
        subtype_ne_univ_iff.1 (hAC ▸ hCu), by rwa [compl_compl], ?_⟩
      rw [subtype_compl, hAC, compl_compl]
  · rintro ⟨A, hA, hAS, hAcS, rfl⟩
    rcases mem_unroot.1 hA with ⟨hA', -⟩ | ⟨hA', -⟩
    · exact Or.inl ⟨subtype_mem_restrictClusters hA' hAS, subtype_ne_univ_iff.2 hAcS⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← subtype_compl]
        exact subtype_mem_restrictClusters hA' hAcS
      · rw [← subtype_compl]
        exact subtype_ne_univ_iff.2 (by rwa [compl_compl])

end Phylogenetics
