module

public import Phylogenetics.Tree.Defs
public import Phylogenetics.Hierarchy.Basic
public import Phylogenetics.Network.CutHierarchy
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Unrooted trees through their split families

The combinatorics of unrooted trees, on the representation by sides of splits of
`Phylogenetics.Tree.Defs`.

## Main results

* `IsUnrootedTree` is characterized by pairwise compatibility (`isUnrootedTree_iff`);
* the vertices of a tree of degree at least three are its *vertex partitions* (`IsVertexPartition`):
  partitions of the taxa into sides of the tree such that every split of the tree has a side inside a
  block;
* a quartet that a tree does not resolve has a unique centre among these vertices
  (`existsUnique_center`);
* a split with two taxa on each side lies in the tree when all its quartets are displayed
  (`mem_of_forall_displays`).
* `treeOfBlobs_isUnrootedTree`: the tree of blobs of a phylogenetic network is an unrooted tree;
* `QuartetTree.exists_eq_pair`, `quartetOfCherry`, `quartetTree`, `card_treesOn`,
  `QuartetTree.card_alternatives`: the three quartet trees on a set of four taxa;
* `IsUnrootedTree.displays_unique`, `IsBinaryTree.exists_displays`: an unrooted tree displays at most one
  quartet tree on a set of four taxa, and a binary tree exactly one;
* `IsUnrootedTree.contractSides`: contracting edges keeps an unrooted tree.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]


/-- A binary unrooted tree has a rooting that is a binary hierarchy. -/
theorem isBinaryTree_iff {T : Finset (Finset X)} :
    IsBinaryTree T ↔ ∃ H : Finset (Finset X), IsBinaryHierarchy H ∧ unroot H = T := by
  constructor
  · rintro ⟨H, hH, rfl, hb⟩
    exact ⟨H, isBinaryHierarchy_iff_card_childClusters.2 ⟨hH, hb⟩, rfl⟩
  · rintro ⟨H, hH, rfl⟩
    obtain ⟨hH, hb⟩ := isBinaryHierarchy_iff_card_childClusters.1 hH
    exact ⟨H, hH, rfl, hb⟩

/-- The laws of a family of sides of splits: the sides are nonempty and proper, closed under
complement, include the singletons, and are pairwise compatible. -/
structure IsSplitFamily (T : Finset (Finset X)) : Prop where
  nonempty : ∀ A ∈ T, A.Nonempty
  compl_nonempty : ∀ A ∈ T, Aᶜ.Nonempty
  compl_mem : ∀ A ∈ T, Aᶜ ∈ T
  singleton_mem : ∀ x : X, {x} ∈ T
  compatible : ∀ A ∈ T, ∀ B ∈ T, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ

theorem IsUnrootedTree.nonempty_of_mem {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : A ∈ T) : A.Nonempty := by
  obtain ⟨H, hH, rfl⟩ := hT
  rcases mem_unroot.1 hA with ⟨h, -⟩ | ⟨-, h⟩
  · exact hH.2.2.1 A h
  · exact nonempty_iff_ne_empty.2 fun he => h ((compl_eq_univ_iff A).2 he)

theorem IsUnrootedTree.compl_mem {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : A ∈ T) : Aᶜ ∈ T := by
  obtain ⟨H, -, rfl⟩ := hT
  exact compl_mem_unroot.2 hA

theorem IsUnrootedTree.compatible {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A B : Finset X}
    (hA : A ∈ T) (hB : B ∈ T) : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ := by
  obtain ⟨H, hH, rfl⟩ := hT
  exact hH.compatible_of_mem_unroot hA hB

/-- A side of a tree has at least two taxa around it. -/
theorem IsUnrootedTree.two_le_card_of_mem {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {A : Finset X} (hA : A ∈ T) : 2 ≤ Fintype.card X := by
  have h1 := card_pos.2 (hT.nonempty_of_mem hA)
  have h2 := card_pos.2 (hT.nonempty_of_mem (hT.compl_mem hA))
  rw [card_compl] at h2
  omega

theorem isSplitFamily_unroot {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hX : 2 ≤ Fintype.card X) : IsSplitFamily (unroot H) := by
  have hT : IsUnrootedTree (unroot H) := ⟨H, hH, rfl⟩
  refine ⟨fun A hA => hT.nonempty_of_mem hA, fun A hA => hT.nonempty_of_mem (hT.compl_mem hA),
    fun A hA => hT.compl_mem hA, fun x => ?_, fun A hA B hB => hT.compatible hA hB⟩
  refine mem_unroot.2 (Or.inl ⟨hH.2.1 x, fun h => ?_⟩)
  have := congrArg card h
  rw [card_singleton, card_univ] at this
  omega

/-- A tree on at least two taxa is a split family. -/
theorem IsUnrootedTree.isSplitFamily {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hX : 2 ≤ Fintype.card X) : IsSplitFamily T := by
  obtain ⟨H, hH, rfl⟩ := hT
  exact isSplitFamily_unroot hH hX

/-- The rooting of an unrooted tree at the taxon `r`: its sides avoiding `r`, with the root and `{r}`. -/
def rootedAt (T : Finset (Finset X)) (r : X) : Finset (Finset X) :=
  insert univ (insert {r} (T.filter fun A => r ∉ A))

theorem mem_rootedAt {T : Finset (Finset X)} {r : X} {A : Finset X} :
    A ∈ rootedAt T r ↔ A = univ ∨ A = {r} ∨ (A ∈ T ∧ r ∉ A) := by
  simp only [rootedAt, mem_insert, mem_filter]

theorem rootedAt_isHierarchy {T : Finset (Finset X)} (hT : IsSplitFamily T) (r : X) :
    IsHierarchy (rootedAt T r) := by
  refine ⟨mem_rootedAt.2 (Or.inl rfl), fun x => ?_, fun A hA => ?_, fun A hA B hB => ?_⟩
  · by_cases hx : x = r
    · exact mem_rootedAt.2 (Or.inr (Or.inl (by rw [hx])))
    · exact mem_rootedAt.2 (Or.inr (Or.inr ⟨hT.singleton_mem x, by
        simpa using fun h : r = x => hx h.symm⟩))
  · rcases mem_rootedAt.1 hA with rfl | rfl | ⟨h, -⟩
    · exact ⟨r, mem_univ r⟩
    · exact singleton_nonempty r
    · exact hT.nonempty A h
  · rcases mem_rootedAt.1 hA with rfl | rfl | ⟨hA, hrA⟩
    · exact Or.inr (Or.inl (subset_univ B))
    · rcases mem_rootedAt.1 hB with rfl | rfl | ⟨hB, hrB⟩
      · exact Or.inl (subset_univ _)
      · exact Or.inl (Subset.refl _)
      · exact Or.inr (Or.inr (disjoint_singleton_left.2 hrB))
    · rcases mem_rootedAt.1 hB with rfl | rfl | ⟨hB, hrB⟩
      · exact Or.inl (subset_univ _)
      · exact Or.inr (Or.inr (disjoint_singleton_right.2 hrA))
      · rcases hT.compatible A hA B hB with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · have : r ∈ A ∪ B := h ▸ mem_univ r
          rcases mem_union.1 this with h' | h'
          · exact absurd h' hrA
          · exact absurd h' hrB

theorem unroot_rootedAt {T : Finset (Finset X)} (hT : IsSplitFamily T)
    (r : X) : unroot (rootedAt T r) = T := by
  ext A
  rw [mem_unroot]
  constructor
  · rintro (⟨hA, hne⟩ | ⟨hA, hne⟩)
    · rcases mem_rootedAt.1 hA with rfl | rfl | ⟨hA, -⟩
      · exact absurd rfl hne
      · exact hT.singleton_mem r
      · exact hA
    · have : Aᶜ ∈ T := by
        rcases mem_rootedAt.1 hA with h | h | ⟨hA, -⟩
        · exact absurd h hne
        · rw [h]; exact hT.singleton_mem r
        · exact hA
      simpa only [compl_compl] using hT.compl_mem _ this
  · intro hA
    by_cases hr : r ∈ A
    · refine Or.inr ⟨mem_rootedAt.2 (Or.inr (Or.inr ⟨hT.compl_mem A hA, by simpa using hr⟩)), ?_⟩
      intro h
      exact (hT.nonempty A hA).ne_empty ((compl_eq_univ_iff A).1 h)
    · refine Or.inl ⟨mem_rootedAt.2 (Or.inr (Or.inr ⟨hA, hr⟩)), ?_⟩
      intro h
      exact (hT.compl_nonempty A hA).ne_empty ((compl_eq_empty_iff A).2 h)

/-- For at least two taxa, unrooted trees are exactly the pairwise compatible split families. -/
theorem isUnrootedTree_iff (hX : 2 ≤ Fintype.card X) (T : Finset (Finset X)) :
    IsUnrootedTree T ↔ IsSplitFamily T := by
  refine ⟨fun h => h.isSplitFamily hX, fun h => ?_⟩
  have : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨r⟩ := this
  exact ⟨rootedAt T r, rootedAt_isHierarchy h r, unroot_rootedAt h r⟩

/-- The tree of blobs is an unrooted tree. -/
theorem treeOfBlobs_isUnrootedTree {V E : Type*} {N : RootedNetwork V E X} (hN : N.IsPhylogenetic)
    [Nonempty X] : IsUnrootedTree (treeOfBlobs N) := by
  obtain ⟨r⟩ := ‹Nonempty X›
  refine ⟨N.cutHierarchy r, N.cutHierarchy_isHierarchy hN r, ?_⟩
  ext A
  rw [N.mem_unroot_cutHierarchy hN r A]
  simp only [treeOfBlobs, mem_filter, mem_univ, true_and]

/-! ### Quartet trees -/

omit [Fintype X] in
theorem QuartetTree.exists_eq_pair (s : QuartetTree X) :
    ∃ B C, s.val = {B, C} ∧ B.card = 2 ∧ C.card = 2 ∧ Disjoint B C ∧ s.taxa = B ∪ C := by
  obtain ⟨hc, h2, hd⟩ := s.property
  obtain ⟨B, C, hBC, hs⟩ := card_eq_two.1 hc
  have hB : B ∈ s.val := by simp [hs]
  have hC : C ∈ s.val := by simp [hs]
  refine ⟨B, C, hs, h2 B hB, h2 C hC, hd B hB C hC hBC, ?_⟩
  simp [QuartetTree.taxa, hs]

omit [Fintype X] in
/-- A quartet tree has four taxa. -/
theorem QuartetTree.card_taxa (s : QuartetTree X) : s.taxa.card = 4 := by
  obtain ⟨B, C, -, hB, hC, hd, ht⟩ := s.exists_eq_pair
  rw [ht, card_union_of_disjoint hd, hB, hC]

omit [Fintype X] in
theorem QuartetTree.card_of_mem (s : QuartetTree X) {B : Finset X} (hB : B ∈ s.val) : B.card = 2 :=
  s.property.2.1 B hB

omit [Fintype X] in
theorem QuartetTree.subset_taxa (s : QuartetTree X) {B : Finset X} (hB : B ∈ s.val) : B ⊆ s.taxa := by
  obtain ⟨C, D, hs, -, -, -, ht⟩ := s.exists_eq_pair
  rw [ht]
  rw [hs] at hB
  rcases mem_insert.1 hB with rfl | h
  · exact subset_union_left
  · rw [mem_singleton] at h
    subst h
    exact subset_union_right

omit [Fintype X] in
/-- The cherry of a quartet tree other than `B` is the rest of its taxa. -/
theorem QuartetTree.sdiff_mem (s : QuartetTree X) {B : Finset X} (hB : B ∈ s.val) :
    s.taxa \ B ∈ s.val := by
  obtain ⟨C, D, hs, -, -, hd, ht⟩ := s.exists_eq_pair
  rw [ht]
  rw [hs] at hB ⊢
  rcases mem_insert.1 hB with rfl | h
  · rw [union_sdiff_cancel_left hd]; simp
  · rw [mem_singleton] at h
    subst h
    rw [union_sdiff_cancel_right hd]; simp

omit [Fintype X] in
/-- A quartet tree is its two cherries. -/
theorem QuartetTree.eq_pair_of_mem (s : QuartetTree X) {B : Finset X} (hB : B ∈ s.val) :
    s.val = {B, s.taxa \ B} := by
  obtain ⟨C, D, hs, -, -, hd, ht⟩ := s.exists_eq_pair
  rw [ht]
  rw [hs] at hB ⊢
  rcases mem_insert.1 hB with rfl | h
  · rw [union_sdiff_cancel_left hd]
  · rw [mem_singleton] at h
    subst h
    rw [union_sdiff_cancel_right hd, pair_comm]

omit [Fintype X] in
/-- Quartet trees on the same taxa sharing a cherry are equal. -/
theorem QuartetTree.eq_of_taxa_eq_of_mem {r s : QuartetTree X} (h : r.taxa = s.taxa) {B : Finset X}
    (hr : B ∈ r.val) (hs : B ∈ s.val) : r = s := by
  apply Subtype.ext
  rw [r.eq_pair_of_mem hr, s.eq_pair_of_mem hs, h]

/-- A cherry and its complement in a set of four taxa form a quartet tree. -/
def quartetOfCherry (q B : Finset X) (hq : q.card = 4) (hB : B ⊆ q) (h2 : B.card = 2) :
    QuartetTree X :=
  ⟨{B, q \ B}, by
    have hc : (q \ B).card = 2 := by rw [card_sdiff_of_subset hB]; omega
    have hne : B ≠ q \ B := by
      intro h
      obtain ⟨x, hx⟩ := card_pos.1 (show 0 < B.card by omega)
      have := h ▸ hx
      exact (mem_sdiff.1 this).2 hx
    refine ⟨card_pair hne, ?_, ?_⟩
    · intro C hC
      rcases mem_insert.1 hC with rfl | h
      · exact h2
      · rw [mem_singleton] at h
        rw [h, hc]
    · intro C hC D hD hCD
      rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
      · exact absurd rfl hCD
      · rw [mem_singleton] at hD
        rw [hD]
        exact disjoint_sdiff
      · rw [mem_singleton] at hC
        rw [hC]
        exact sdiff_disjoint
      · rw [mem_singleton] at hC hD
        exact absurd (hC.trans hD.symm) hCD⟩

omit [Fintype X] in
@[simp] theorem quartetOfCherry_val (q B : Finset X) (hq : q.card = 4) (hB : B ⊆ q) (h2 : B.card = 2) :
    (quartetOfCherry q B hq hB h2).val = {B, q \ B} := rfl

@[simp] theorem quartetOfCherry_taxa (q B : Finset X) (hq : q.card = 4) (hB : B ⊆ q)
    (h2 : B.card = 2) : (quartetOfCherry q B hq hB h2).taxa = q := by
  simpa [QuartetTree.taxa] using hB

theorem mem_treesOn {q : Finset X} {r : QuartetTree X} : r ∈ treesOn q ↔ r.taxa = q := by
  simp [treesOn]

theorem QuartetTree.mem_alternatives {s r : QuartetTree X} :
    r ∈ s.alternatives ↔ r.taxa = s.taxa ∧ r ≠ s := by
  simp [QuartetTree.alternatives]

omit [Fintype X] in
/-- Four taxa forming a set of four elements are distinct. -/
theorem ne_of_card_four {a b c d : X} (h : ({a, b, c, d} : Finset X).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have key : ∀ u v w z : X, ({u, v, w, z} : Finset X).card = 4 → u ≠ v := by
    rintro u v w z h rfl
    have : ({u, u, w, z} : Finset X).card ≤ 3 := by
      rw [Finset.insert_idem]; exact Finset.card_le_three
    omega
  refine ⟨key _ _ _ _ h, ?_, ?_, ?_, ?_, ?_⟩
  · apply key a c b d; rw [← h]; congr 1; grind
  · apply key a d b c; rw [← h]; congr 1; grind
  · apply key b c a d; rw [← h]; congr 1; grind
  · apply key b d a c; rw [← h]; congr 1; grind
  · apply key c d a b; rw [← h]; congr 1; grind

/-- The quartet tree with cherries `{a, b}` and `{c, d}`. -/
def quartetTree (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) : QuartetTree X :=
  ⟨{{a, b}, {c, d}}, by
    have hab : a ≠ b := by
      rintro rfl
      have : ({a, a, c, d} : Finset X).card ≤ 3 := by
        rw [insert_idem]; exact card_le_three
      omega
    have hac : a ≠ c := by
      rintro rfl
      have : ({a, b, a, d} : Finset X).card ≤ 3 := by
        have : ({a, b, a, d} : Finset X) = {a, b, d} := by ext x; simp; tauto
        rw [this]; exact card_le_three
      omega
    have had : a ≠ d := by
      rintro rfl
      have : ({a, b, c, a} : Finset X).card ≤ 3 := by
        have : ({a, b, c, a} : Finset X) = {a, b, c} := by ext x; simp; tauto
        rw [this]; exact card_le_three
      omega
    have hbc : b ≠ c := by
      rintro rfl
      have : ({a, b, b, d} : Finset X).card ≤ 3 := by
        have : ({a, b, b, d} : Finset X) = {a, b, d} := by ext x; simp
        rw [this]; exact card_le_three
      omega
    have hbd : b ≠ d := by
      rintro rfl
      have : ({a, b, c, b} : Finset X).card ≤ 3 := by
        have : ({a, b, c, b} : Finset X) = {a, b, c} := by ext x; simp; tauto
        rw [this]; exact card_le_three
      omega
    have hcd : c ≠ d := by
      rintro rfl
      have : ({a, b, c, c} : Finset X).card ≤ 3 := by
        have : ({a, b, c, c} : Finset X) = {a, b, c} := by ext x; simp
        rw [this]; exact card_le_three
      omega
    have hne : ({a, b} : Finset X) ≠ {c, d} := by
      intro h'
      have : a ∈ ({c, d} : Finset X) := h' ▸ (by simp)
      simp [hac, had] at this
    refine ⟨card_pair hne, ?_, ?_⟩
    · intro C hC
      rcases mem_insert.1 hC with rfl | hC
      · exact card_pair hab
      · rw [mem_singleton] at hC
        rw [hC]
        exact card_pair hcd
    · intro C hC D hD hCD
      rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
      · exact absurd rfl hCD
      · rw [mem_singleton] at hD
        subst hD
        simp [hac.symm, had.symm, hbc.symm, hbd.symm]
      · rw [mem_singleton] at hC
        subst hC
        simp [hac, had, hbc, hbd]
      · rw [mem_singleton] at hC hD
        exact absurd (hC.trans hD.symm) hCD⟩

omit [Fintype X] in
@[simp] theorem quartetTree_val (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).val = {{a, b}, {c, d}} := rfl

omit [Fintype X] in
@[simp] theorem quartetTree_taxa (a b c d : X) (h : ({a, b, c, d} : Finset X).card = 4) :
    (quartetTree a b c d h).taxa = {a, b, c, d} := by
  ext x
  simp [QuartetTree.taxa]
  tauto

theorem card_treesOn {q : Finset X} (hq : q.card = 4) : (treesOn q).card = 3 := by
  obtain ⟨a, ha⟩ := card_pos.1 (show 0 < q.card by omega)
  have h3 : (q.erase a).card = 3 := by rw [card_erase_of_mem ha]; omega
  obtain ⟨b, c, d, hbc, hbd, hcd, he⟩ := card_eq_three.1 h3
  have hq' : q = {a, b, c, d} := by rw [← he, insert_erase ha]
  have hab : a ∉ ({b, c, d} : Finset X) := by rw [← he]; simp
  simp only [mem_insert, mem_singleton, not_or] at hab
  obtain ⟨hab, hac, had⟩ := hab
  have c1 : ({a, b, c, d} : Finset X).card = 4 := hq' ▸ hq
  have c2 : ({a, c, b, d} : Finset X).card = 4 := by
    rw [← c1]; congr 1; ext x; simp; tauto
  have c3 : ({a, d, b, c} : Finset X).card = 4 := by
    rw [← c1]; congr 1; ext x; simp; tauto
  have hsub : treesOn q = {quartetTree a b c d c1, quartetTree a c b d c2, quartetTree a d b c c3} := by
    ext r
    simp only [mem_treesOn, mem_insert, mem_singleton]
    constructor
    · intro hr
      have har : a ∈ r.taxa := hr ▸ ha
      obtain ⟨B, hB, haB⟩ : ∃ B ∈ r.val, a ∈ B := by
        simpa [QuartetTree.taxa, mem_sup] using har
      have hBq : B ⊆ q := hr ▸ r.subset_taxa hB
      have hBc := r.card_of_mem hB
      obtain ⟨x, hx⟩ : ∃ x, B.erase a = {x} :=
        card_eq_one.1 (by rw [card_erase_of_mem haB]; omega)
      have hBe : B = {a, x} := by rw [← hx, insert_erase haB]
      have hxq : x ∈ q.erase a := by
        have : x ∈ B.erase a := by simp [hx]
        exact mem_erase.2 ⟨(mem_erase.1 this).1, hBq (mem_erase.1 this).2⟩
      rw [he] at hxq
      simp only [mem_insert, mem_singleton] at hxq
      rcases hxq with rfl | rfl | rfl
      · left
        apply QuartetTree.eq_of_taxa_eq_of_mem (B := {a, x}) (by simp [hr, hq']) (hBe ▸ hB) (by simp)
      · right; left
        apply QuartetTree.eq_of_taxa_eq_of_mem (B := {a, x}) (by
          rw [hr, hq', quartetTree_taxa]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
      · right; right
        apply QuartetTree.eq_of_taxa_eq_of_mem (B := {a, x}) (by
          rw [hr, hq', quartetTree_taxa]; ext y; simp; tauto) (hBe ▸ hB) (by simp)
    · rintro (rfl | rfl | rfl)
      · simp [hq']
      · rw [hq', quartetTree_taxa]; ext y; simp; tauto
      · rw [hq', quartetTree_taxa]; ext y; simp; tauto
  rw [hsub]
  apply card_eq_three.2
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · intro h
    have h1 : ({a, b} : Finset X) ∈ (quartetTree a c b d c2).val := h ▸ (by simp)
    simp only [quartetTree_val, mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · have : b ∈ ({a, c} : Finset X) := h1 ▸ (by simp)
      simp [Ne.symm hab, hbc] at this
    · have : a ∈ ({b, d} : Finset X) := h1 ▸ (by simp)
      simp [hab, had] at this
  · intro h
    have h1 : ({a, b} : Finset X) ∈ (quartetTree a d b c c3).val := h ▸ (by simp)
    simp only [quartetTree_val, mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · have : b ∈ ({a, d} : Finset X) := h1 ▸ (by simp)
      simp [Ne.symm hab, hbd] at this
    · have : a ∈ ({b, c} : Finset X) := h1 ▸ (by simp)
      simp [hab, hac] at this
  · intro h
    have h1 : ({a, c} : Finset X) ∈ (quartetTree a d b c c3).val := h ▸ (by simp)
    simp only [quartetTree_val, mem_insert, mem_singleton] at h1
    rcases h1 with h1 | h1
    · have : c ∈ ({a, d} : Finset X) := h1 ▸ (by simp)
      simp [Ne.symm hac, hcd] at this
    · have : a ∈ ({b, c} : Finset X) := h1 ▸ (by simp)
      simp [hab, hac] at this

/-- The two notions of a displayed quartet agree: a rooted tree `G`, through its unrooted tree, displays
the quartet tree `ab|ce` exactly when `geneTreeDisplays G a b c e` holds. No law of hierarchies is
needed. -/
theorem displays_unroot_quartetTree_iff {G : Finset (Finset X)} {a b c e : X}
    (h : ({a, b, c, e} : Finset X).card = 4) :
    Displays (unroot G) (quartetTree a b c e h) ↔ geneTreeDisplays G a b c e = true := by
  obtain ⟨hab, hac, hae, hbc, hbe, hce⟩ := ne_of_card_four h
  simp only [geneTreeDisplays, decide_eq_true_eq, Displays, quartetTree_val, quartetTree_taxa,
    mem_insert, mem_singleton]
  have hsets : ∀ A : Finset X, A ∩ {a, b, c, e} = {a, b} ↔ a ∈ A ∧ b ∈ A ∧ c ∉ A ∧ e ∉ A := by
    intro A
    constructor
    · intro hA
      have hm : ∀ x, x ∈ A ∧ (x = a ∨ x = b ∨ x = c ∨ x = e) ↔ x = a ∨ x = b := by
        intro x
        have := Finset.ext_iff.1 hA x
        simpa [mem_inter] using this
      refine ⟨((hm a).2 (Or.inl rfl)).1, ((hm b).2 (Or.inr rfl)).1, fun hc => ?_, fun he => ?_⟩
      · rcases (hm c).1 ⟨hc, by simp⟩ with h' | h' <;> simp_all
      · rcases (hm e).1 ⟨he, by simp⟩ with h' | h' <;> simp_all
    · rintro ⟨ha, hb, hc, he⟩
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hx hc
        · exact absurd hx he
      · rintro (rfl | rfl)
        · simp [ha]
        · simp [hb]
  have hsets' : ∀ A : Finset X, A ∩ {a, b, c, e} = {c, e} ↔ c ∈ A ∧ e ∈ A ∧ a ∉ A ∧ b ∉ A := by
    intro A
    constructor
    · intro hA
      have hm : ∀ x, x ∈ A ∧ (x = a ∨ x = b ∨ x = c ∨ x = e) ↔ x = c ∨ x = e := by
        intro x
        have := Finset.ext_iff.1 hA x
        simpa [mem_inter] using this
      refine ⟨((hm c).2 (Or.inl rfl)).1, ((hm e).2 (Or.inr rfl)).1, fun ha => ?_, fun hb => ?_⟩
      · rcases (hm a).1 ⟨ha, by simp⟩ with h' | h' <;> simp_all
      · rcases (hm b).1 ⟨hb, by simp⟩ with h' | h' <;> simp_all
    · rintro ⟨hc, he, ha, hb⟩
      ext x
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
        · exact absurd hx ha
        · exact absurd hx hb
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · simp [hc]
        · simp [he]
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_unroot.1 hA with ⟨hAG, -⟩ | ⟨hAG, -⟩
    · rcases hAs with hAs | hAs
      · exact ⟨A, hAG, Or.inl ((hsets A).1 hAs)⟩
      · exact ⟨A, hAG, Or.inr ((hsets' A).1 hAs)⟩
    · rcases hAs with hAs | hAs
      · obtain ⟨h1, h2, h3, h4⟩ := (hsets A).1 hAs
        exact ⟨Aᶜ, hAG, Or.inr ⟨mem_compl.2 h3, mem_compl.2 h4, by simpa using h1, by simpa using h2⟩⟩
      · obtain ⟨h1, h2, h3, h4⟩ := (hsets' A).1 hAs
        exact ⟨Aᶜ, hAG, Or.inl ⟨mem_compl.2 h3, mem_compl.2 h4, by simpa using h1, by simpa using h2⟩⟩
  · rintro ⟨C, hC, hc | hc⟩
    · refine ⟨C, mem_unroot.2 (Or.inl ⟨hC, ?_⟩), Or.inl ((hsets C).2 hc)⟩
      rintro rfl
      exact hc.2.2.1 (mem_univ c)
    · refine ⟨C, mem_unroot.2 (Or.inl ⟨hC, ?_⟩), Or.inr ((hsets' C).2 hc)⟩
      rintro rfl
      exact hc.2.2.1 (mem_univ a)

theorem QuartetTree.alternatives_eq (s : QuartetTree X) :
    s.alternatives = (treesOn s.taxa).erase s := by
  ext r
  simp [QuartetTree.mem_alternatives, mem_treesOn, and_comm]

theorem QuartetTree.card_alternatives (s : QuartetTree X) : s.alternatives.card = 2 := by
  rw [s.alternatives_eq, card_erase_of_mem (mem_treesOn.2 rfl), card_treesOn s.card_taxa]

/-- A tree displays at most one quartet tree on a set of four taxa. -/
theorem IsUnrootedTree.displays_unique {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {s s' : QuartetTree X} (hs : Displays T s) (hs' : Displays T s') (h : s.taxa = s'.taxa) :
    s = s' := by
  obtain ⟨A, hA, hAs⟩ := hs
  obtain ⟨A', hA', hAs'⟩ := hs'
  rw [← h] at hAs'
  have hc := s.card_of_mem hAs
  have hc' := s'.card_of_mem hAs'
  have hq := s.card_taxa
  rcases hT.compatible hA hA' with hsub | hsub | hdis | hun
  · have : A ∩ s.taxa = A' ∩ s.taxa :=
      eq_of_subset_of_card_le (inter_subset_inter_right hsub) (by omega)
    exact QuartetTree.eq_of_taxa_eq_of_mem h hAs (this ▸ hAs')
  · have : A' ∩ s.taxa = A ∩ s.taxa :=
      eq_of_subset_of_card_le (inter_subset_inter_right hsub) (by omega)
    exact QuartetTree.eq_of_taxa_eq_of_mem h (this ▸ hAs) hAs'
  · have hsd := s.sdiff_mem hAs
    have : A' ∩ s.taxa = s.taxa \ (A ∩ s.taxa) := by
      apply eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_inter.1 hx
        exact mem_sdiff.2 ⟨h2, fun h3 => disjoint_left.1 hdis (mem_inter.1 h3).1 h1⟩
      · rw [card_sdiff_of_subset inter_subset_right]; omega
    exact QuartetTree.eq_of_taxa_eq_of_mem h (this ▸ hsd) hAs'
  · have hsd := s'.sdiff_mem hAs'
    have : s'.taxa \ (A' ∩ s.taxa) = A ∩ s.taxa := by
      rw [← h]
      apply eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_sdiff.1 hx
        have : x ∈ A ∪ A' := hun ▸ mem_univ x
        rcases mem_union.1 this with h3 | h3
        · exact mem_inter.2 ⟨h3, h1⟩
        · exact absurd (mem_inter.2 ⟨h3, h1⟩) h2
      · rw [card_sdiff_of_subset inter_subset_right]; omega
    exact QuartetTree.eq_of_taxa_eq_of_mem h hAs (this ▸ hsd)

omit [Fintype X] in
theorem Displays.mono {T T' : Finset (Finset X)} (h : T ⊆ T') {s : QuartetTree X}
    (hs : Displays T s) : Displays T' s := by
  obtain ⟨A, hA, hAs⟩ := hs
  exact ⟨A, h hA, hAs⟩

/-- A side tracing a pair on four taxa displays the corresponding quartet tree. -/
theorem displays_quartetOfCherry {T : Finset (Finset X)} {A q : Finset X} (hA : A ∈ T)
    (hq : q.card = 4) (h2 : (A ∩ q).card = 2) :
    Displays T (quartetOfCherry q (A ∩ q) hq inter_subset_right h2) :=
  ⟨A, hA, by simp⟩

/-- A binary tree displays a quartet tree on every set of four taxa. -/
theorem IsBinaryTree.exists_displays {T : Finset (Finset X)} (hT : IsBinaryTree T) {q : Finset X}
    (hq : q.card = 4) : ∃ s ∈ treesOn q, Displays T s := by
  obtain ⟨H, hH, rfl, hbin⟩ := hT
  obtain ⟨D, hD, hmin⟩ := (H.filter fun D => 2 ≤ (D ∩ q).card).exists_min_image card
    ⟨univ, mem_filter.2 ⟨hH.1, by simp [hq]⟩⟩
  obtain ⟨hDH, hD2⟩ := mem_filter.1 hD
  have hDc : 2 ≤ D.card := hD2.trans (card_le_card inter_subset_left)
  obtain ⟨C₁, C₂, -, hch⟩ := card_eq_two.1 (hbin D hDH hDc)
  have hsup := hH.sup_childClusters hDc
  rw [hch] at hsup
  have hsmall : ∀ C ∈ childClusters H D, (C ∩ q).card ≤ 1 := by
    intro C hC
    by_contra hlt
    obtain ⟨hCH, hCD, -⟩ := mem_childClusters.1 hC
    have := hmin C (mem_filter.2 ⟨hCH, by omega⟩)
    exact absurd (card_lt_card hCD) (by omega)
  have h1 := hsmall C₁ (by simp [hch])
  have h2 := hsmall C₂ (by simp [hch])
  have hDe : D = C₁ ∪ C₂ := by
    rw [← hsup]; simp
  have hle : (D ∩ q).card ≤ 2 := by
    rw [hDe, union_inter_distrib_right]
    exact (card_union_le _ _).trans (by omega)
  have heq : (D ∩ q).card = 2 := le_antisymm hle hD2
  refine ⟨quartetOfCherry q (D ∩ q) hq inter_subset_right heq, by simp [mem_treesOn], ?_⟩
  apply displays_quartetOfCherry _ hq heq
  refine mem_unroot.2 (Or.inl ⟨hDH, ?_⟩)
  rintro rfl
  rw [univ_inter] at heq
  omega

/-- The least cluster of a hierarchy containing a nonempty set. -/
theorem IsHierarchy.exists_least {H : Finset (Finset X)} (hH : IsHierarchy H) {A : Finset X}
    (hA : A.Nonempty) : ∃ C ∈ H, A ⊆ C ∧ ∀ D ∈ H, A ⊆ D → C ⊆ D := by
  obtain ⟨C, hC, hmin⟩ := (H.filter fun D => A ⊆ D).exists_min_image card
    ⟨univ, mem_filter.2 ⟨hH.1, subset_univ A⟩⟩
  obtain ⟨hCH, hAC⟩ := mem_filter.1 hC
  refine ⟨C, hCH, hAC, fun D hD hAD => ?_⟩
  obtain ⟨a, ha⟩ := hA
  rcases hH.subset_or_subset_of_mem hCH hD (hAC ha) (hAD ha) with h | h
  · exact h
  · have := eq_of_subset_of_card_le h (hmin D (mem_filter.2 ⟨hD, hAD⟩))
    exact this ▸ Subset.refl _

/-- A cluster strictly inside a cluster lies inside one of its children. -/
theorem IsHierarchy.exists_subset_child {H : Finset (Finset X)} (hH : IsHierarchy H) {K E : Finset X}
    (hK : 2 ≤ K.card) (hE : E ∈ H) (hEK : E ⊂ K) : ∃ D ∈ childClusters H K, E ⊆ D := by
  obtain ⟨x, hx⟩ := hH.2.2.1 E hE
  obtain ⟨D, hD, hxD⟩ := hH.exists_mem_childClusters hK (hEK.subset hx)
  refine ⟨D, hD, ?_⟩
  obtain ⟨hDH, -, hmax⟩ := mem_childClusters.1 hD
  rcases hH.subset_or_subset_of_mem hE hDH hx hxD with h | h
  · exact h
  · by_cases hDE : D = E
    · exact hDE ▸ Subset.refl _
    · exact absurd hEK (hmax E hE (ssubset_of_subset_of_ne h hDE))

/-- A tree displaying the quartet trees of a split with at least two taxa on each side has that
split. (This is the case of Steel's quartet theorem for splits with two taxa on each side;
`Phylogenetics.mem_unroot_iff_quartets` states it for species trees.) -/
theorem mem_of_forall_displays {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : 2 ≤ A.card) (hA' : 2 ≤ Aᶜ.card)
    (h : ∀ s ∈ bipartitionQuartets A, Displays T s) : A ∈ T := by
  have hX : 2 ≤ Fintype.card X := hA.trans (card_le_univ A)
  have hSF := hT.isSplitFamily hX
  obtain ⟨b, hb⟩ := card_pos.1 (show 0 < Aᶜ.card by omega)
  have hbA : b ∉ A := mem_compl.1 hb
  have hH := rootedAt_isHierarchy hSF b
  have hAne : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨C, hC, hAC, hleast⟩ := hH.exists_least hAne
  by_cases hCA : C = A
  · subst hCA
    rcases mem_rootedAt.1 hC with rfl | rfl | ⟨hC, -⟩
    · exact absurd (mem_univ b) hbA
    · exact absurd (mem_singleton_self b) hbA
    · exact hC
  exfalso
  have hAC' : A ⊂ C := ssubset_of_subset_of_ne hAC (Ne.symm hCA)
  obtain ⟨b₂, hb₂C, hb₂A, hb₂b⟩ : ∃ b₂ ∈ C, b₂ ∉ A ∧ b₂ ≠ b := by
    rcases mem_rootedAt.1 hC with rfl | rfl | ⟨-, hbC⟩
    · obtain ⟨b₂, h1, h2⟩ := exists_mem_ne (by omega : 1 < Aᶜ.card) b
      exact ⟨b₂, mem_univ _, mem_compl.1 h1, h2⟩
    · have := card_le_card hAC
      rw [card_singleton] at this
      omega
    · obtain ⟨b₂, h1, h2⟩ := exists_of_ssubset hAC'
      exact ⟨b₂, h1, h2, fun e => hbC (e ▸ h1)⟩
  have hCc : 2 ≤ C.card := hA.trans (card_le_card hAC)
  obtain ⟨a₁, ha₁⟩ := hAne
  obtain ⟨C₁, hC₁, ha₁C₁⟩ := hH.exists_mem_childClusters hCc (hAC ha₁)
  obtain ⟨hC₁H, hC₁C, hC₁max⟩ := mem_childClusters.1 hC₁
  obtain ⟨a₂, ha₂, ha₂C₁⟩ : ∃ a₂ ∈ A, a₂ ∉ C₁ := by
    by_contra hcon
    push Not at hcon
    exact not_subset_of_ssubset hC₁C (hleast C₁ hC₁H hcon)
  have ha₁₂ : a₁ ≠ a₂ := fun e => ha₂C₁ (e ▸ ha₁C₁)
  have ha₁b : a₁ ≠ b := fun e => hbA (e ▸ ha₁)
  have ha₂b : a₂ ≠ b := fun e => hbA (e ▸ ha₂)
  have ha₁b₂ : a₁ ≠ b₂ := fun e => hb₂A (e ▸ ha₁)
  have ha₂b₂ : a₂ ≠ b₂ := fun e => hb₂A (e ▸ ha₂)
  have hcard : ({a₁, a₂, b, b₂} : Finset X).card = 4 := by
    rw [card_insert_of_notMem (by simp [ha₁₂, ha₁b, ha₁b₂]),
      card_insert_of_notMem (by simp [ha₂b, ha₂b₂]), card_pair hb₂b.symm]
  set s := quartetTree a₁ a₂ b b₂ hcard with hs
  have hstaxa : s.taxa = {a₁, a₂, b, b₂} := quartetTree_taxa _ _ _ _ _
  have hAq : A ∩ s.taxa = {a₁, a₂} := by
    rw [hstaxa]
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hx hbA
      · exact absurd hx hb₂A
    · rintro (rfl | rfl)
      · exact ⟨ha₁, Or.inl rfl⟩
      · exact ⟨ha₂, Or.inr (Or.inl rfl)⟩
  have hsmem : s ∈ bipartitionQuartets A := by
    simp only [bipartitionQuartets, mem_filter, mem_univ, true_and]
    rw [hAq]
    simp [hs]
  obtain ⟨D, hD, hDs⟩ := h s hsmem
  -- the side of the split avoiding `b`
  obtain ⟨D', hD', h1, h2, h3, h4⟩ : ∃ D' ∈ T, a₁ ∈ D' ∧ a₂ ∈ D' ∧ b ∉ D' ∧ b₂ ∉ D' := by
    rw [hstaxa] at hDs
    simp only [hs, quartetTree_val, mem_insert, mem_singleton] at hDs
    rcases hDs with hDs | hDs
    · have hmem := fun x => Finset.ext_iff.1 hDs x
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨D, hD, ((hmem a₁).2 (by simp)).1, ((hmem a₂).2 (by simp)).1, ?_, ?_⟩
      · intro hbD
        have := (hmem b).1 ⟨hbD, by simp⟩
        simp [Ne.symm ha₁b, Ne.symm ha₂b] at this
      · intro hbD
        have := (hmem b₂).1 ⟨hbD, by simp⟩
        simp [Ne.symm ha₁b₂, Ne.symm ha₂b₂] at this
    · have hmem := fun x => Finset.ext_iff.1 hDs x
      simp only [mem_inter, mem_insert, mem_singleton] at hmem
      refine ⟨Dᶜ, hSF.compl_mem D hD, ?_, ?_, ?_, ?_⟩
      · refine mem_compl.2 fun hx => ?_
        have := (hmem a₁).1 ⟨hx, by simp⟩
        simp [ha₁b, ha₁b₂] at this
      · refine mem_compl.2 fun hx => ?_
        have := (hmem a₂).1 ⟨hx, by simp⟩
        simp [ha₂b, ha₂b₂] at this
      · simpa using ((hmem b).2 (by simp)).1
      · simpa using ((hmem b₂).2 (by simp)).1
  have hD'H : D' ∈ rootedAt T b := mem_rootedAt.2 (Or.inr (Or.inr ⟨hD', h3⟩))
  rcases hH.subset_or_subset_of_mem hC hD'H (hAC ha₁) h1 with hsub | hsub
  · exact h4 (hsub hb₂C)
  · have hD'C : D' ⊂ C := ssubset_of_subset_of_ne hsub fun e => h4 (e ▸ hb₂C)
    rcases hH.subset_or_subset_of_mem hC₁H hD'H ha₁C₁ h1 with hs1 | hs1
    · by_cases he : C₁ = D'
      · exact ha₂C₁ (he ▸ h2)
      · exact hC₁max D' hD'H (ssubset_of_subset_of_ne hs1 he) hD'C
    · exact ha₂C₁ (hs1 h2)

/-- A tree displaying all the quartet trees that another tree displays resolves it. -/
theorem subset_of_forall_displays {T T' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hT' : IsUnrootedTree T') (h : ∀ s, Displays T' s → Displays T s) : T' ⊆ T := by
  intro A hA
  have hX := hT'.two_le_card_of_mem hA
  have hSF := hT.isSplitFamily hX
  by_cases h1 : A.card ≤ 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 (le_antisymm h1 (card_pos.2 (hT'.nonempty_of_mem hA)))
    exact hSF.singleton_mem x
  by_cases h2 : Aᶜ.card ≤ 1
  · have hc := hT'.compl_mem hA
    obtain ⟨x, hx⟩ := card_eq_one.1 (le_antisymm h2 (card_pos.2 (hT'.nonempty_of_mem hc)))
    have : A = {x}ᶜ := by rw [← hx, compl_compl]
    rw [this]
    exact hSF.compl_mem _ (hSF.singleton_mem x)
  refine mem_of_forall_displays hT (by omega) (by omega) fun s hs => h s ⟨A, hA, ?_⟩
  exact (mem_filter.1 hs).2

/-- Contracting internal edges of a tree gives a tree. -/
theorem IsUnrootedTree.contractSides {T C : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hC : C ⊆ internalSides T) : IsUnrootedTree (contractSides T C) := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hSF := hT.isSplitFamily hX
    refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun A hA => hSF.nonempty A (mem_filter.1 hA).1
    · exact fun A hA => hSF.compl_nonempty A (mem_filter.1 hA).1
    · intro A hA
      obtain ⟨hA, h1, h2⟩ := mem_filter.1 hA
      exact mem_filter.2 ⟨hSF.compl_mem A hA, h2, by rwa [compl_compl]⟩
    · intro x
      refine mem_filter.2 ⟨hSF.singleton_mem x, fun h => ?_, fun h => ?_⟩
      · have := (mem_filter.1 (hC h)).2.1
        simp at this
      · have := (mem_filter.1 (hC h)).2.2
        simp at this
    · exact fun A hA B hB => hSF.compatible A (mem_filter.1 hA).1 B (mem_filter.1 hB).1
  · have hempty : ∀ A, A ∉ T := fun A hA => hX (hT.two_le_card_of_mem hA)
    have : Finset.filter (fun A => A ∉ C ∧ Aᶜ ∉ C) T = T := by
      rw [filter_eq_self]
      exact fun A hA => absurd hA (hempty A)
    unfold Phylogenetics.contractSides
    rw [this]
    exact hT

/-! ### Vertices of a tree -/

/-- A vertex of degree at least three of the tree `T`: the partition of the taxa according to the
components of the tree with the vertex deleted. -/
structure IsVertexPartition (T P : Finset (Finset X)) : Prop where
  mem : ∀ B ∈ P, B ∈ T
  pairwiseDisjoint : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C
  cover : P.sup id = univ
  three_le : 3 ≤ P.card
  edge_in_block : ∀ C ∈ T, (∃ B ∈ P, C ⊆ B) ∨ ∃ B ∈ P, Cᶜ ⊆ B

/-- The multifurcations of a tree: its vertices of degree at least four. -/
def multifurcations (T : Finset (Finset X)) : Finset (Finset (Finset X)) :=
  univ.filter fun P => IsVertexPartition T P ∧ 4 ≤ P.card

theorem mem_multifurcations {T P : Finset (Finset X)} :
    P ∈ multifurcations T ↔ IsVertexPartition T P ∧ 4 ≤ P.card := by
  simp [multifurcations]

/-- The taxa of `q` lie in distinct blocks of `P`. -/
def InDistinctBlocks (P : Finset (Finset X)) (q : Finset X) : Prop :=
  ∀ B ∈ P, (B ∩ q).card ≤ 1

theorem IsVertexPartition.exists_mem_block {T P : Finset (Finset X)} (hP : IsVertexPartition T P)
    (x : X) : ∃ B ∈ P, x ∈ B := by
  have : x ∈ P.sup id := hP.cover ▸ mem_univ x
  simpa [mem_sup] using this

/-- Two distinct vertices of a tree: a block at each covers all taxa (the block towards the other
vertex). -/
theorem IsVertexPartition.exists_union_eq_univ {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hP : IsVertexPartition T P) (hP' : IsVertexPartition T P') (hne : P ≠ P') :
    ∃ B ∈ P, ∃ B' ∈ P', B ∪ B' = univ := by
  by_contra hcon
  push Not at hcon
  have hcompl : ∀ {A B : Finset X}, Aᶜ ⊆ B → A ∪ B = univ := fun {A B} h =>
    eq_univ_iff_forall.2 fun x => by
      by_cases hx : x ∈ A
      · exact mem_union_left _ hx
      · exact mem_union_right _ (h (mem_compl.2 hx))
  have h1 : ∀ B ∈ P, ∃ B' ∈ P', B ⊆ B' := by
    intro B hB
    rcases hP'.edge_in_block B (hP.mem B hB) with h | ⟨B', hB', h⟩
    · exact h
    · exact absurd (hcompl h) (hcon B hB B' hB')
  have h2 : ∀ B' ∈ P', ∃ B ∈ P, B' ⊆ B := by
    intro B' hB'
    rcases hP.edge_in_block B' (hP'.mem B' hB') with h | ⟨B, hB, h⟩
    · exact h
    · refine absurd ?_ (hcon B hB B' hB')
      rw [union_comm]
      exact hcompl h
  have key : ∀ {Q Q' : Finset (Finset X)}, IsVertexPartition T Q →
      (∀ B ∈ Q, ∃ B' ∈ Q', B ⊆ B') → (∀ B' ∈ Q', ∃ B ∈ Q, B' ⊆ B) → Q ⊆ Q' := by
    intro Q Q' hQ h1 h2 B hB
    obtain ⟨B', hB', hsub⟩ := h1 B hB
    obtain ⟨B'', hB'', hsub'⟩ := h2 B' hB'
    have hBB : B = B'' := by
      by_contra hn
      obtain ⟨x, hx⟩ := hT.nonempty_of_mem (hQ.mem B hB)
      exact disjoint_left.1 (hQ.pairwiseDisjoint B hB B'' hB'' hn) hx (hsub' (hsub hx))
    have : B = B' := Subset.antisymm hsub (hBB ▸ hsub')
    exact this ▸ hB'
  exact hne (Subset.antisymm (key hP h1 h2) (key hP' h2 h1))

/-- Taxa in distinct blocks of a covering family: at most as many taxa as blocks. -/
theorem card_le_of_inDistinctBlocks {P : Finset (Finset X)} (hcover : P.sup id = univ) {q : Finset X}
    (h : InDistinctBlocks P q) : q.card ≤ P.card := by
  have hsub : q ⊆ P.biUnion fun B => B ∩ q := by
    intro x hx
    have : x ∈ P.sup id := hcover ▸ mem_univ x
    obtain ⟨B, hB, hxB⟩ : ∃ B ∈ P, x ∈ B := by simpa [mem_sup] using this
    exact mem_biUnion.2 ⟨B, hB, mem_inter.2 ⟨hxB, hx⟩⟩
  calc q.card ≤ _ := card_le_card hsub
    _ ≤ ∑ B ∈ P, (B ∩ q).card := card_biUnion_le
    _ ≤ ∑ _B ∈ P, 1 := sum_le_sum h
    _ = P.card := by simp

/-- The partition at the vertex of a rooted tree given by a non-root cluster with two taxa: the
children of the cluster and its complement. -/
theorem IsHierarchy.isVertexPartition_insert_compl {H : Finset (Finset X)} (hH : IsHierarchy H)
    {K : Finset X} (hK : K ∈ H) (hKu : K ≠ univ) (hK2 : 2 ≤ K.card) :
    IsVertexPartition (unroot H) (insert Kᶜ (childClusters H K)) := by
  have hcm : Kᶜ ∈ unroot H := compl_mem_unroot.2 (mem_unroot.2 (Or.inl ⟨hK, hKu⟩))
  have hchild : ∀ D ∈ childClusters H K, D ∈ H ∧ D ⊂ K := fun D hD =>
    ⟨(mem_childClusters.1 hD).1, (mem_childClusters.1 hD).2.1⟩
  have hdisj : ∀ D ∈ childClusters H K, Disjoint Kᶜ D := fun D hD =>
    disjoint_left.2 fun x hx hxD => mem_compl.1 hx ((hchild D hD).2.subset hxD)
  have hnot : Kᶜ ∉ childClusters H K := by
    intro h
    have hne : Kᶜ.Nonempty := hH.2.2.1 _ (hchild _ h).1
    obtain ⟨x, hx⟩ := hne
    exact mem_compl.1 hx ((hchild _ h).2.subset hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · exact hcm
    · refine mem_unroot.2 (Or.inl ⟨(hchild B hB).1, ?_⟩)
      rintro rfl
      exact not_subset_of_ssubset (hchild _ hB).2 (subset_univ K)
  · intro B hB C hC hBC
    rcases mem_insert.1 hB with rfl | hB <;> rcases mem_insert.1 hC with rfl | hC
    · exact absurd rfl hBC
    · exact hdisj C hC
    · exact (hdisj B hB).symm
    · exact hH.disjoint_of_mem_childClusters hB hC hBC
  · rw [sup_insert, hH.sup_childClusters hK2]
    simp
  · rw [card_insert_of_notMem hnot]
    have := hH.two_le_card_childClusters hK2
    omega
  · have base : ∀ E ∈ H, E ≠ univ →
        (∃ B ∈ insert Kᶜ (childClusters H K), E ⊆ B) ∨
          ∃ B ∈ insert Kᶜ (childClusters H K), Eᶜ ⊆ B := by
      intro E hE hEu
      rcases hH.2.2.2 E hE K hK with hs | hs | hd
      · by_cases he : E = K
        · subst he
          exact Or.inr ⟨Eᶜ, mem_insert_self _ _, Subset.refl _⟩
        · obtain ⟨D, hD, hED⟩ := hH.exists_subset_child hK2 hE (ssubset_of_subset_of_ne hs he)
          exact Or.inl ⟨D, mem_insert_of_mem hD, hED⟩
      · exact Or.inr ⟨Kᶜ, mem_insert_self _ _, compl_subset_compl.2 hs⟩
      · exact Or.inl ⟨Kᶜ, mem_insert_self _ _, fun x hx =>
          mem_compl.2 fun hxK => disjoint_left.1 hd hx hxK⟩
    intro C hC
    rcases mem_unroot.1 hC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact base C h1 h2
    · rcases base Cᶜ h1 h2 with h | h
      · exact Or.inr h
      · rw [compl_compl] at h
        exact Or.inl h

/-- A set of four taxa that a tree does not resolve has a unique centre, a multifurcation at whose
blocks the taxa are distinct. -/
theorem existsUnique_center {T : Finset (Finset X)} (hT : IsUnrootedTree T) {q : Finset X}
    (hq : q.card = 4) (hstar : ∀ s ∈ treesOn q, ¬ Displays T s) :
    ∃! P, P ∈ multifurcations T ∧ InDistinctBlocks P q := by
  have hX : 2 ≤ Fintype.card X := by
    have := card_le_univ q
    omega
  have hSF := hT.isSplitFamily hX
  obtain ⟨r, hr⟩ := card_pos.1 (show 0 < q.card by omega)
  have hH := rootedAt_isHierarchy hSF r
  have hun := unroot_rootedAt hSF r
  have hq'c : (q.erase r).card = 3 := by rw [card_erase_of_mem hr]; omega
  obtain ⟨K, hK, hqK, hleast⟩ := hH.exists_least (A := q.erase r)
    (card_pos.1 (by omega))
  have hrc : ({r} : Finset X)ᶜ ∈ rootedAt T r :=
    mem_rootedAt.2 (Or.inr (Or.inr ⟨hSF.compl_mem _ (hSF.singleton_mem r), by simp⟩))
  have hKr : K ⊆ {r}ᶜ := hleast _ hrc (fun x hx => by simpa using (mem_erase.1 hx).1)
  have hrK : r ∉ K := fun h => (by simpa using hKr h : r ≠ r) rfl
  have hKu : K ≠ univ := fun h => hrK (h ▸ mem_univ r)
  have hK2 : 2 ≤ K.card := by
    have := card_le_card hqK
    omega
  have hVP := hH.isVertexPartition_insert_compl hK hKu hK2
  rw [hun] at hVP
  have hdist : InDistinctBlocks (insert Kᶜ (childClusters (rootedAt T r) K)) q := by
    intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · have : Kᶜ ∩ q ⊆ {r} := by
        intro x hx
        obtain ⟨h1, h2⟩ := mem_inter.1 hx
        by_contra hxr
        exact mem_compl.1 h1 (hqK (mem_erase.2 ⟨by simpa using hxr, h2⟩))
      simpa using card_le_card this
    · obtain ⟨hBH, hBK, -⟩ := mem_childClusters.1 hB
      by_contra hlt
      have hBq : B ∩ q ⊆ q.erase r := fun x hx =>
        mem_erase.2 ⟨fun e => hrK (hBK.subset (e ▸ (mem_inter.1 hx).1)), (mem_inter.1 hx).2⟩
      have hle := card_le_card hBq
      have hBT : B ∈ T := by
        rw [← hun]
        refine mem_unroot.2 (Or.inl ⟨hBH, ?_⟩)
        rintro rfl
        exact hKu (eq_univ_of_card _ (le_antisymm (card_le_univ K)
          (by simpa using card_le_card hBK.subset)))
      by_cases h3 : (B ∩ q).card = 2
      · exact hstar _ (mem_treesOn.2 (quartetOfCherry_taxa q (B ∩ q) hq inter_subset_right h3))
          (displays_quartetOfCherry hBT hq h3)
      · have : B ∩ q = q.erase r := eq_of_subset_of_card_le hBq (by omega)
        have hsub : q.erase r ⊆ B := fun x hx => (mem_inter.1 (this ▸ hx)).1
        exact not_subset_of_ssubset hBK (hleast B hBH hsub)
  have huniq : ∀ P', P' ∈ multifurcations T → InDistinctBlocks P' q →
      ∀ P'', P'' ∈ multifurcations T → InDistinctBlocks P'' q → P' = P'' := by
    intro P' hP' hd' P'' hP'' hd''
    by_contra hne
    obtain ⟨B, hB, B', hB', hu⟩ := (mem_multifurcations.1 hP').1.exists_union_eq_univ hT
      (mem_multifurcations.1 hP'').1 hne
    have hsub : q ⊆ (B ∩ q) ∪ (B' ∩ q) := by
      intro x hx
      have : x ∈ B ∪ B' := hu ▸ mem_univ x
      rcases mem_union.1 this with h | h
      · exact mem_union_left _ (mem_inter.2 ⟨h, hx⟩)
      · exact mem_union_right _ (mem_inter.2 ⟨h, hx⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le (B ∩ q) (B' ∩ q)
    have h3 := hd' B hB
    have h4 := hd'' B' hB'
    omega
  refine ⟨_, ⟨mem_multifurcations.2 ⟨hVP, ?_⟩, hdist⟩, fun P' hP' => huniq _ hP'.1 hP'.2 _ ?_ hdist⟩
  · exact hq ▸ card_le_of_inDistinctBlocks hVP.cover hdist
  · exact mem_multifurcations.2 ⟨hVP, hq ▸ card_le_of_inDistinctBlocks hVP.cover hdist⟩

/-- Taxa in distinct blocks of a vertex partition are not resolved by the tree. -/
theorem not_displays_of_inDistinctBlocks {T P : Finset (Finset X)}
    (hP : IsVertexPartition T P) {s : QuartetTree X} (h : InDistinctBlocks P s.taxa) :
    ¬ Displays T s := by
  rintro ⟨A, hA, hAs⟩
  have hc := s.card_of_mem hAs
  have hc' := s.card_of_mem (s.sdiff_mem hAs)
  rcases hP.edge_in_block A hA with ⟨B, hB, hsub⟩ | ⟨B, hB, hsub⟩
  · have := card_le_card (show A ∩ s.taxa ⊆ B ∩ s.taxa from inter_subset_inter_right hsub)
    have := h B hB
    omega
  · have hs : s.taxa \ (A ∩ s.taxa) ⊆ B ∩ s.taxa := by
      intro x hx
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hx
      exact mem_inter.2 ⟨hsub (mem_compl.2 fun hxA => h2 (mem_inter.2 ⟨hxA, h1⟩)), h1⟩
    have := card_le_card hs
    have := h B hB
    omega

end Phylogenetics
