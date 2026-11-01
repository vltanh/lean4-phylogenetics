module

public import Phylogenetics.Hierarchy.SpeciesTree
public import Phylogenetics.Tree.Splits

/-!
# Unrooted trees are determined by their quartets

[M. Steel, *The complexity of reconstructing trees from qualitative characters and subtrees*,
J. Classification 9 (1992) 91–116], used by [E. S. Allman, J. H. Degnan, J. A. Rhodes,
*Identifying the rooted species tree from the distribution of unrooted gene trees under the
coalescent*, J. Math. Biol. 62 (2011) 833–862] in the proofs of their Corollary 6 (binary trees)
and Theorem 9 (Proposition 6 of Steel 1992: every internal edge is distinguished by a quartet);
for trees that need not be binary, [H.-J. Bandelt, A. Dress, *Reconstructing the shape of a tree
from observed dissimilarity data*, Adv. Appl. Math. 7 (1986) 309–343] and [C. Semple, M. Steel,
*Phylogenetics*, Oxford University Press, 2003, Theorem 6.3.5], used in the proof of their
Proposition 11.

In the representation of `Phylogenetics.unroot`, these are statements about the sets of splits of
the unrooted trees `σ⁻` of species trees:

* `mem_unroot_iff_quartets`: a bipartition `A | Aᶜ` with `|A|, |Aᶜ| ≥ 2` is a split of `σ⁻` if and
  only if every quartet `aa'|bb'` with `a, a' ∈ A` and `b, b' ∈ Aᶜ` is displayed by `σ⁻`.
* `exists_distinguishing_quartet`: every internal edge of `σ⁻` is the only edge of `σ⁻` separating
  some quartet `aa'|bb'` (Proposition 6 of Steel 1992, for trees that need not be binary).

Corollary 6 of Allman, Degnan and Rhodes (2011) combines them with its own argument for the edge
lengths.

## Proofs

* `mem_unroot_iff_quartets`: this is `mem_of_forall_displays`, for the unrooted tree of `σ`.
* `exists_distinguishing_quartet`: for a cluster `A` of `σ`, take `a, a'` in different children
  of `A`; if the parent `P` of `A` is not the root, take `b ∈ P \ A` and `b' ∉ P`, and otherwise
  take `b, b' ∈ Aᶜ` such that no cluster strictly contained in `Aᶜ` contains both.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `unroot` is closed under complements. -/
private theorem steel_compl_mem_unroot {G : Finset (Finset X)} {A : Finset X}
    (h : A ∈ unroot G) : Aᶜ ∈ unroot G := by
  rw [mem_unroot] at h ⊢
  rw [compl_compl]
  exact h.symm

/-- A split `A | Aᶜ` (with both sides of size at least 2) is a split of `σ⁻` if and only if every
quartet `aa'|bb'` (`a ≠ a'` in `A`, `b ≠ b'` in `Aᶜ`) is displayed by `σ⁻`, that is, separated by
some split of `σ⁻`. -/
theorem mem_unroot_iff_quartets (σ : SpeciesTree X) {A : Finset X} (hA : 2 ≤ #A)
    (hA' : 2 ≤ #Aᶜ) :
    A ∈ unroot σ.clusters ↔
      ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ Aᶜ, ∀ b' ∈ Aᶜ, a ≠ a' → b ≠ b' →
        ∃ C ∈ unroot σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C ∧ b' ∉ C := by
  constructor
  · intro h a ha a' ha' b hb b' hb' _ _
    exact ⟨A, h, ha, ha', mem_compl.1 hb, mem_compl.1 hb'⟩
  intro hq
  refine mem_of_forall_displays ⟨σ.clusters, σ.isHierarchy, rfl⟩ hA hA' fun s hs => ?_
  have hmem : A ∩ s.taxa ∈ s.val := (mem_filter.1 hs).2
  obtain ⟨a, a', haa, hP⟩ := card_eq_two.1 (s.card_of_mem hmem)
  obtain ⟨b, b', hbb, hQ⟩ := card_eq_two.1 (s.card_of_mem (s.sdiff_mem hmem))
  have hPm : ∀ x, x ∈ A ∧ x ∈ s.taxa ↔ x = a ∨ x = a' := fun x => by
    rw [← mem_inter, hP, mem_insert, mem_singleton]
  have hQm : ∀ x, (x ∈ s.taxa ∧ ¬ (x ∈ A ∧ x ∈ s.taxa)) ↔ x = b ∨ x = b' := fun x => by
    rw [← mem_inter, ← mem_sdiff, hQ, mem_insert, mem_singleton]
  have ha := (hPm a).2 (Or.inl rfl)
  have ha' := (hPm a').2 (Or.inr rfl)
  have hb := (hQm b).2 (Or.inl rfl)
  have hb' := (hQm b').2 (Or.inr rfl)
  have hbA : ∀ {x}, (x ∈ s.taxa ∧ ¬ (x ∈ A ∧ x ∈ s.taxa)) → x ∈ Aᶜ := fun hx =>
    mem_compl.2 fun h => hx.2 ⟨h, hx.1⟩
  obtain ⟨C, hC, h₁, h₂, h₃, h₄⟩ := hq a ha.1 a' ha'.1 b (hbA hb) b' (hbA hb') haa hbb
  refine ⟨C, hC, ?_⟩
  have hCA : C ∩ s.taxa = A ∩ s.taxa := by
    ext x
    simp only [mem_inter]
    by_cases hx : x ∈ s.taxa
    · by_cases hxA : x ∈ A
      · rcases (hPm x).1 ⟨hxA, hx⟩ with rfl | rfl
        · exact ⟨fun _ => ⟨hxA, hx⟩, fun _ => ⟨h₁, hx⟩⟩
        · exact ⟨fun _ => ⟨hxA, hx⟩, fun _ => ⟨h₂, hx⟩⟩
      · rcases (hQm x).1 ⟨hx, fun h => hxA h.1⟩ with rfl | rfl
        · exact ⟨fun h => absurd h.1 h₃, fun h => absurd h.1 hxA⟩
        · exact ⟨fun h => absurd h.1 h₄, fun h => absurd h.1 hxA⟩
    · exact ⟨fun h => absurd h.2 hx, fun h => absurd h.2 hx⟩
  rw [hCA]
  exact hmem

/-- Two taxa `x ≠ y` of a set `N` with at least two elements such that no cluster strictly
contained in `N` contains both. -/
private theorem steel_exists_pair (σ : SpeciesTree X) {N : Finset X} (hN : 2 ≤ #N) :
    ∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ ∀ C ∈ σ.clusters, x ∈ C → y ∈ C → ¬ C ⊂ N := by
  obtain ⟨x, hx⟩ : N.Nonempty := card_pos.1 (by omega)
  have hxN : ({x} : Finset X) ⊂ N := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨singleton_subset_iff.2 hx, ?_⟩
    rintro h
    rw [← h, card_singleton] at hN
    omega
  obtain ⟨M, hM, hMmax⟩ := exists_max_image (σ.clusters.filter fun C => x ∈ C ∧ C ⊂ N) card
    ⟨{x}, mem_filter.2 ⟨σ.singleton_mem x, mem_singleton_self x, hxN⟩⟩
  obtain ⟨hMc, hxM, hMN⟩ := mem_filter.1 hM
  obtain ⟨y, hyN, hyM⟩ := exists_of_ssubset hMN
  refine ⟨x, hx, y, hyN, ?_, ?_⟩
  · rintro rfl
    exact hyM hxM
  · intro C hC hxC hyC hCN
    have hle := hMmax C (mem_filter.2 ⟨hC, hxC, hCN⟩)
    rcases σ.laminar C hC M hMc with h | h | h
    · exact hyM (h hyC)
    · rw [eq_of_subset_of_card_le h hle] at hyM
      exact hyM hyC
    · exact disjoint_left.1 h hxC hxM

/-- Proposition 6 of Steel (1992) for a split `A | Aᶜ` given by a cluster `A` of `σ`. -/
private theorem steel_distinguishing_of_mem_clusters (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ σ.clusters) (hAu : A ≠ univ) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  obtain ⟨z, hz⟩ : A.Nonempty := card_pos.1 (by omega)
  obtain ⟨a, ha, a', ha', haa, hpair⟩ := steel_exists_pair σ hA₁
  -- the clusters containing `a` and `a'` contain `A`
  have hup : ∀ C ∈ σ.clusters, a ∈ C → a' ∈ C → A ⊆ C := by
    intro C hC h1 h2
    rcases σ.laminar C hC A hA with h | h | h
    · have hCA : C = A := by
        by_contra hne
        exact hpair C hC h1 h2 (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)
      rw [hCA]
    · exact h
    · exact absurd ha (disjoint_left.1 h h1)
  -- the parent `P` of `A`
  obtain ⟨P, hP, hPmin⟩ := exists_min_image (σ.clusters.filter fun C => A ⊂ C) card
    ⟨univ, mem_filter.2 ⟨σ.univ_mem, ssubset_univ_iff.2 hAu⟩⟩
  obtain ⟨hPc, hAP⟩ := mem_filter.1 hP
  have hPle : ∀ C ∈ σ.clusters, A ⊂ C → P ⊆ C := by
    intro C hC hAC
    have hle := hPmin C (mem_filter.2 ⟨hC, hAC⟩)
    rcases σ.laminar C hC P hPc with h | h | h
    · rw [eq_of_subset_of_card_le h hle]
    · exact h
    · exact absurd (hAP.1 hz) (disjoint_left.1 h (hAC.1 hz))
  -- two taxa `b, b'` outside `A`
  obtain ⟨b, hb, b', hb', hbb, hP1, hP2⟩ : ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, b ≠ b' ∧
      (∀ C ∈ σ.clusters, A ⊂ C → b ∈ C ∨ b' ∈ C) ∧
      (∀ D ∈ σ.clusters, b ∈ D → b' ∈ D → ¬ D ⊂ Aᶜ) := by
    by_cases hPu : P = univ
    · obtain ⟨b, hb, b', hb', hbb, h⟩ := steel_exists_pair σ hA₂
      refine ⟨b, hb, b', hb', hbb, fun C hC hAC => Or.inl ?_, h⟩
      have := hPle C hC hAC
      rw [hPu] at this
      exact this (mem_univ b)
    · obtain ⟨b, hbP, hbA⟩ := exists_of_ssubset hAP
      obtain ⟨b', hb'⟩ : Pᶜ.Nonempty := by
        rw [nonempty_iff_ne_empty, Ne, compl_eq_empty_iff]
        exact hPu
      rw [mem_compl] at hb'
      refine ⟨b, mem_compl.2 hbA, b', mem_compl.2 (fun h => hb' (hAP.1 h)), ?_, ?_, ?_⟩
      · rintro rfl
        exact hb' hbP
      · intro C hC hAC
        exact Or.inl (hPle C hC hAC hbP)
      · intro D hD hbD hb'D hDA
        rcases σ.laminar D hD P hPc with h | h | h
        · exact hb' (h hb'D)
        · exact mem_compl.1 (hDA.1 (h (hAP.1 hz))) hz
        · exact disjoint_left.1 h hbD hbP
  refine ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, ?_⟩
  intro C hC haC ha'C hbC hb'C
  rcases mem_unroot.1 hC with ⟨hC1, -⟩ | ⟨hC1, -⟩
  · have hAC := hup C hC1 haC ha'C
    by_contra hne
    rcases hP1 C hC1 (Finset.ssubset_iff_subset_ne.2 ⟨hAC, Ne.symm hne⟩) with h | h
    · exact hbC h
    · exact hb'C h
  · have hbD : b ∈ Cᶜ := mem_compl.2 hbC
    have hb'D : b' ∈ Cᶜ := mem_compl.2 hb'C
    have hDA : Cᶜ ⊆ Aᶜ := by
      rcases σ.laminar Cᶜ hC1 A hA with h | h | h
      · exact absurd (h hbD) (mem_compl.1 hb)
      · exact absurd haC (mem_compl.1 (h ha))
      · exact subset_compl_iff_disjoint_right.2 h
    have hEq : Cᶜ = Aᶜ := by
      by_contra hne
      exact hP2 Cᶜ hC1 hbD hb'D (Finset.ssubset_iff_subset_ne.2 ⟨hDA, hne⟩)
    exact compl_injective hEq

/-- Proposition 6 of Steel (1992): every internal edge `A | Aᶜ` of `σ⁻` is the only split of `σ⁻`
separating some quartet `aa'|bb'`. -/
theorem exists_distinguishing_quartet (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) (hA₁ : 2 ≤ #A) (hA₂ : 2 ≤ #Aᶜ) :
    ∃ a ∈ A, ∃ a' ∈ A, ∃ b ∈ Aᶜ, ∃ b' ∈ Aᶜ, a ≠ a' ∧ b ≠ b' ∧
      ∀ C ∈ unroot σ.clusters, a ∈ C → a' ∈ C → b ∉ C → b' ∉ C → C = A := by
  rcases mem_unroot.1 hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · exact steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₁ hA₂
  · obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, h⟩ :=
      steel_distinguishing_of_mem_clusters σ hA1 hA2 hA₂ (by rwa [compl_compl])
    rw [compl_compl] at hb hb'
    refine ⟨b, hb, b', hb', a, ha, a', ha', hbb, haa, ?_⟩
    intro C hC hbC hb'C haC ha'C
    have := h Cᶜ (steel_compl_mem_unroot hC) (mem_compl.2 haC) (mem_compl.2 ha'C)
      (fun h' => mem_compl.1 h' hbC) (fun h' => mem_compl.1 h' hb'C)
    exact compl_injective this

end Phylogenetics
