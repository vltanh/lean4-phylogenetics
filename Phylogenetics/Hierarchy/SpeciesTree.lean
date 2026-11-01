module

public import Phylogenetics.Hierarchy.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Rooted species trees

A *species tree* on the taxa `X` is a hierarchy with a strictly positive length, in coalescent
units, on the edge above each cluster other than the root.

* `SpeciesTree X`, `SpeciesTree.IsBinary`; `SpeciesTree.unrootedLength`: the length of an edge of the
  unrooted tree, where the two edges below the root merge into one;
  `SpeciesTree.SameUnrootedMetricTree`, `SpeciesTree.SameRootedMetricTree`: agreement of metric trees.
* `SpeciesTree.restrict σ S`: the induced species tree `σ⁺(S)` (Allman, Degnan and Rhodes 2011,
  Section 2): its clusters are the nonempty traces `A ∩ S` of the clusters of `σ`, and the length of
  the edge above a trace `C` is the sum of the lengths of the edges above the clusters `A` of `σ`
  with `A ∩ S = C` (the edges that merge when nodes of degree 2 are suppressed).

[E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from the
distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862]

## Main results

* `SpeciesTree.mem_clusters_of_triples`: a set `A` with at least two taxa is a cluster as soon as,
  for all `a, a' ∈ A` and `b ∉ A`, some cluster contains `a` and `a'` but not `b` (rooted
  triples determine a rooted tree).
* `SpeciesTree.isBinary_iff_card_childClusters`: a species tree is binary if and only if every
  cluster with at least two taxa has exactly two children.
* `SpeciesTree.restrict_isBinary`: the induced subtree of a binary species tree is binary.
* `SpeciesTree.sameUnrootedMetricTree_of_card_le_three`: on at most three taxa all unrooted metric
  species trees agree (there is no internal edge).
* `SpeciesTree.restrict_unroot`, `SpeciesTree.restrict_unrootedLength`: induced subtrees and
  unrooting commute, and the unrooted length of a split of `σ(S)` is the sum of the unrooted
  lengths of the splits of `σ` that induce it.
* `SpeciesTree.restrict_unrootedLength_eq_of_unique`: a split of `σ⁻(S)` induced by a single split
  of `σ⁻` has the same length.
* `SpeciesTree.SameRootedMetricTree.refl`/`symm`/`trans`, and the same for
  `SameUnrootedMetricTree`.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A rooted species tree on the taxa `X`: a hierarchy of clusters on `X`, with a strictly positive
length, in coalescent units, on the edge above each cluster other than the root `univ`. The
lengths of pendant edges (above singletons) matter only when several lineages are sampled from a
taxon. -/
structure SpeciesTree (X : Type*) [Fintype X] [DecidableEq X] where
  /-- The clusters: the sets of taxa below the nodes of the tree. -/
  clusters : Finset (Finset X)
  univ_mem : (univ : Finset X) ∈ clusters
  singleton_mem : ∀ x : X, {x} ∈ clusters
  nonempty_of_mem : ∀ A ∈ clusters, A.Nonempty
  laminar : ∀ A ∈ clusters, ∀ B ∈ clusters, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  /-- The length of the edge above each cluster (its value at `univ` and at non-clusters is
  irrelevant). -/
  length : Finset X → ℝ
  length_pos : ∀ A ∈ clusters, A ≠ univ → 0 < length A

namespace SpeciesTree

/-- A species tree is binary if every cluster with at least two taxa is the union of two disjoint
clusters (equivalently, every internal node has exactly two children). -/
def IsBinary (σ : SpeciesTree X) : Prop :=
  ∀ A ∈ σ.clusters, 2 ≤ #A → ∃ B ∈ σ.clusters, ∃ C ∈ σ.clusters, Disjoint B C ∧ B ∪ C = A

/-- The length of the edge of the unrooted species tree that induces the split `A | Aᶜ`: when the
root is suppressed, the two edges below it merge into one. -/
noncomputable def unrootedLength (σ : SpeciesTree X) (A : Finset X) : ℝ :=
  ∑ C ∈ σ.clusters with C ≠ univ ∧ (C = A ∨ C = Aᶜ), σ.length C

/-- Two species trees have the same unrooted metric tree `σ⁻`: the same unrooted topology and the
same lengths of internal edges. -/
def SameUnrootedMetricTree (σ σ' : SpeciesTree X) : Prop :=
  unroot σ.clusters = unroot σ'.clusters ∧
    ∀ A ∈ unroot σ.clusters, 2 ≤ #A → 2 ≤ #Aᶜ → σ.unrootedLength A = σ'.unrootedLength A

/-- Two species trees have the same rooted metric tree `σ⁺`: the same rooted topology and the same
lengths of internal edges. -/
def SameRootedMetricTree (σ σ' : SpeciesTree X) : Prop :=
  σ.clusters = σ'.clusters ∧ ∀ A ∈ σ.clusters, 2 ≤ #A → A ≠ univ → σ.length A = σ'.length A

end SpeciesTree

theorem SpeciesTree.isHierarchy (σ : SpeciesTree X) : IsHierarchy σ.clusters :=
  ⟨σ.univ_mem, σ.singleton_mem, σ.nonempty_of_mem, σ.laminar⟩

namespace SpeciesTree

theorem restrict_univ_mem (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (univ : Finset S) ∈ restrictClusters S σ.clusters := by
  unfold restrictClusters
  rw [mem_image]
  refine ⟨univ, mem_filter.2 ⟨σ.univ_mem, by simpa using hS⟩, ?_⟩
  simp

theorem restrict_singleton_mem (σ : SpeciesTree X) (S : Finset X) (x : S) :
    {x} ∈ restrictClusters S σ.clusters := by
  unfold restrictClusters
  rw [mem_image]
  refine ⟨{x.1}, mem_filter.2 ⟨σ.singleton_mem x.1, ⟨x.1, by simp [x.2]⟩⟩, ?_⟩
  ext ⟨y, hy⟩
  rw [mem_subtype, mem_singleton, mem_singleton, Subtype.ext_iff]

theorem restrict_nonempty_of_mem (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, C.Nonempty := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
  obtain ⟨y, hy⟩ := (mem_filter.1 hA).2
  rw [mem_inter] at hy
  exact ⟨⟨y, hy.2⟩, by simp [hy.1]⟩

theorem restrict_laminar (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, ∀ D ∈ restrictClusters S σ.clusters,
      C ⊆ D ∨ D ⊆ C ∨ Disjoint C D := by
  intro C hC D hD
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
  obtain ⟨B, hB, rfl⟩ := mem_image.1 hD
  rcases σ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 with h | h | h
  · exact Or.inl (subtype_mono h)
  · exact Or.inr (Or.inl (subtype_mono h))
  · refine Or.inr (Or.inr ?_)
    rw [Finset.disjoint_left] at h ⊢
    intro a ha hb
    exact h (mem_subtype.1 ha) (mem_subtype.1 hb)

/-- The length of the edge above the cluster `C` of the induced tree `σ(S)`: the sum of the
lengths of the edges above the clusters of `σ` whose trace on `S` is `C`. -/
noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ A.subtype (· ∈ S) = C, σ.length A

theorem restrictLength_pos (σ : SpeciesTree X) (S : Finset X) :
    ∀ C ∈ restrictClusters S σ.clusters, C ≠ univ → 0 < σ.restrictLength S C := by
  intro C hC hCu
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hC
  have hA' := (mem_filter.1 hA).1
  have hAu : A ≠ univ := by
    rintro rfl
    exact hCu (subtype_univ _)
  unfold restrictLength
  apply Finset.sum_pos
  · intro B hB
    rw [mem_filter] at hB
    exact σ.length_pos B hB.1 hB.2.1
  · exact ⟨A, mem_filter.2 ⟨hA', hAu, rfl⟩⟩

/-- The induced species tree `σ⁺(S)` on a nonempty set of taxa `S`. -/
noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := σ.restrict_univ_mem S hS
  singleton_mem := σ.restrict_singleton_mem S
  nonempty_of_mem := σ.restrict_nonempty_of_mem S
  laminar := σ.restrict_laminar S
  length := σ.restrictLength S
  length_pos := σ.restrictLength_pos S

end SpeciesTree

/-- A species tree is binary if and only if its clusters are a binary hierarchy. -/
theorem SpeciesTree.isBinary_iff_isBinaryHierarchy (σ : SpeciesTree X) :
    σ.IsBinary ↔ IsBinaryHierarchy σ.clusters :=
  ⟨fun h => ⟨σ.isHierarchy, h⟩, fun h => h.2⟩

/-- A species tree is binary if and only if every cluster with at least two taxa has exactly two
children. -/
theorem SpeciesTree.isBinary_iff_card_childClusters (σ : SpeciesTree X) :
    σ.IsBinary ↔ ∀ A ∈ σ.clusters, 2 ≤ #A → #(childClusters σ.clusters A) = 2 := by
  constructor
  · intro hb A hA hA2
    obtain ⟨B, hB, C, hC, hBC, hBCA⟩ := hb A hA hA2
    rw [σ.isHierarchy.childClusters_eq_pair hB hC hBC hBCA]
    refine card_pair fun h => ?_
    subst h
    obtain ⟨y, hy⟩ := σ.nonempty_of_mem B hB
    exact Finset.disjoint_left.1 hBC hy hy
  · intro h A hA hA2
    obtain ⟨B, C, hBC, hch⟩ := card_eq_two.1 (h A hA hA2)
    have hB : B ∈ childClusters σ.clusters A := hch ▸ mem_insert_self _ _
    have hC : C ∈ childClusters σ.clusters A := hch ▸ mem_insert_of_mem (mem_singleton_self _)
    refine ⟨B, (mem_childClusters.1 hB).1, C, (mem_childClusters.1 hC).1,
      σ.isHierarchy.disjoint_of_mem_childClusters hB hC hBC, ?_⟩
    have := σ.isHierarchy.sup_childClusters hA2
    rwa [hch, sup_insert, sup_singleton] at this

/-- In a binary species tree, a cluster with at least two taxa has two children. -/
theorem SpeciesTree.IsBinary.exists_childClusters_eq_pair {σ : SpeciesTree X} (hσ : σ.IsBinary)
    {A : Finset X} (hA : A ∈ σ.clusters) (hA2 : 2 ≤ #A) :
    ∃ B C, B ≠ C ∧ childClusters σ.clusters A = {B, C} :=
  card_eq_two.1 ((σ.isBinary_iff_card_childClusters.1 hσ) A hA hA2)

namespace SpeciesTree

/-- The clusters of the induced tree `σ(S)`. -/
@[simp] theorem restrict_clusters (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).clusters = restrictClusters S σ.clusters := rfl

/-- The edge lengths of the induced tree `σ(S)`. -/
@[simp] theorem restrict_length (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    (σ.restrict S hS).length = σ.restrictLength S := rfl

/-- The length of the edge above a cluster `A ∩ S` of the induced tree, when `A` is the only
cluster of `σ` with this trace. -/
theorem restrictLength_subtype_eq (σ : SpeciesTree X) {S A : Finset X} (hA : A ∈ σ.clusters)
    (hAu : A ≠ univ)
    (h : ∀ B ∈ σ.clusters, B.subtype (· ∈ S) = A.subtype (· ∈ S) → B = A) :
    σ.restrictLength S (A.subtype (· ∈ S)) = σ.length A := by
  unfold restrictLength
  rw [Finset.sum_eq_single_of_mem A (mem_filter.2 ⟨hA, hAu, rfl⟩)]
  intro B hB hBA
  exact absurd (h B (mem_filter.1 hB).1 (mem_filter.1 hB).2.2) hBA

/-- Rooted triples determine the clusters: if for all `a, a' ∈ A` and `b ∉ A` some cluster of
`σ` contains `a` and `a'` but not `b`, then `A` is a cluster of `σ`. -/
theorem mem_clusters_of_triples (σ : SpeciesTree X) {A : Finset X} (hA : A.Nonempty)
    (h : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∉ A, ∃ C ∈ σ.clusters, a ∈ C ∧ a' ∈ C ∧ b ∉ C) :
    A ∈ σ.clusters :=
  σ.isHierarchy.mem_of_triples hA h

/-! ### Induced subtrees of binary trees -/

/-- The induced subtree of a binary species tree is binary. -/
theorem restrict_isBinary {σ : SpeciesTree X} (hσ : σ.IsBinary) (S : Finset X)
    (hS : S.Nonempty) : (σ.restrict S hS).IsBinary := by
  intro C hC hC2
  rw [restrict_clusters] at hC ⊢
  have hH := σ.isHierarchy
  -- `C`, as a set of taxa, and the smallest cluster `lca σ.clusters T` containing it
  set T := C.map (Function.Embedding.subtype (· ∈ S))
  have hTC : #T = #C := card_map _
  have hT : T.Nonempty := card_pos.1 (by omega)
  have hTS : T ⊆ S := fun x hx => by
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact y.2
  have hL : lca σ.clusters T ∈ σ.clusters := hH.lca_mem hT
  have hLC : (lca σ.clusters T).subtype (· ∈ S) = C := subtype_lca_eq hC
  have hL2 : 2 ≤ #(lca σ.clusters T) := by
    have := card_le_card (subset_lca σ.clusters T)
    omega
  obtain ⟨B, hB, D, hD, hBD, hBDL⟩ := hσ _ hL hL2
  -- `T` is contained in neither part, so both traces are nonempty
  have hnot : ∀ E ∈ σ.clusters, E ⊆ lca σ.clusters T → E ≠ lca σ.clusters T → ¬ T ⊆ E :=
    fun E hE hEL hne hTE => hne (Subset.antisymm hEL (lca_subset hE hTE))
  have hBne : B ≠ lca σ.clusters T := by
    intro e
    obtain ⟨d, hd⟩ := σ.nonempty_of_mem D hD
    exact disjoint_left.1 hBD (e ▸ hBDL ▸ mem_union_right B hd) hd
  have hDne : D ≠ lca σ.clusters T := by
    intro e
    obtain ⟨b, hb⟩ := σ.nonempty_of_mem B hB
    exact disjoint_left.1 hBD hb (e ▸ hBDL ▸ mem_union_left D hb)
  have hBS : (B ∩ S).Nonempty := by
    obtain ⟨t, htT, htD⟩ := not_subset.1 (hnot D hD (hBDL ▸ subset_union_right) hDne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_right htD, hTS htT⟩⟩
  have hDS : (D ∩ S).Nonempty := by
    obtain ⟨t, htT, htB⟩ := not_subset.1 (hnot B hB (hBDL ▸ subset_union_left) hBne)
    have htL : t ∈ B ∪ D := hBDL ▸ subset_lca _ T htT
    exact ⟨t, mem_inter.2 ⟨(mem_union.1 htL).resolve_left htB, hTS htT⟩⟩
  refine ⟨B.subtype (· ∈ S), subtype_mem_restrictClusters hB hBS,
    D.subtype (· ∈ S), subtype_mem_restrictClusters hD hDS, ?_, ?_⟩
  · exact disjoint_left.2 fun x hxB hxD =>
      disjoint_left.1 hBD (mem_subtype.1 hxB) (mem_subtype.1 hxD)
  · rw [← hLC, ← hBDL]
    ext x
    simp only [mem_union, mem_subtype]

/-! ### Agreement of metric trees -/

theorem SameRootedMetricTree.refl (σ : SpeciesTree X) : σ.SameRootedMetricTree σ :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

theorem SameRootedMetricTree.symm {σ σ' : SpeciesTree X} (h : σ.SameRootedMetricTree σ') :
    σ'.SameRootedMetricTree σ :=
  ⟨h.1.symm, fun A hA h2 hu => (h.2 A (h.1 ▸ hA) h2 hu).symm⟩

theorem SameRootedMetricTree.trans {σ σ' σ'' : SpeciesTree X} (h : σ.SameRootedMetricTree σ')
    (h' : σ'.SameRootedMetricTree σ'') : σ.SameRootedMetricTree σ'' :=
  ⟨h.1.trans h'.1, fun A hA h2 hu => (h.2 A hA h2 hu).trans (h'.2 A (h.1 ▸ hA) h2 hu)⟩

theorem SameUnrootedMetricTree.refl (σ : SpeciesTree X) : σ.SameUnrootedMetricTree σ :=
  ⟨rfl, fun _ _ _ _ => rfl⟩

theorem SameUnrootedMetricTree.symm {σ σ' : SpeciesTree X} (h : σ.SameUnrootedMetricTree σ') :
    σ'.SameUnrootedMetricTree σ :=
  ⟨h.1.symm, fun A hA h2 h2' => (h.2 A (h.1 ▸ hA) h2 h2').symm⟩

theorem SameUnrootedMetricTree.trans {σ σ' σ'' : SpeciesTree X}
    (h : σ.SameUnrootedMetricTree σ') (h' : σ'.SameUnrootedMetricTree σ'') :
    σ.SameUnrootedMetricTree σ'' :=
  ⟨h.1.trans h'.1, fun A hA h2 h2' => (h.2 A hA h2 h2').trans (h'.2 A (h.1 ▸ hA) h2 h2')⟩

/-- On at most three taxa, the sides of the splits of `σ⁻` are all the proper nonempty subsets. -/
private theorem hier_mem_unroot_of_card_le_three (hX : Fintype.card X ≤ 3) (σ : SpeciesTree X)
    (A : Finset X) : A ∈ unroot σ.clusters ↔ A.Nonempty ∧ A ≠ univ := by
  rw [mem_unroot]
  constructor
  · rintro (⟨hA, hAu⟩ | ⟨hA, hAu⟩)
    · exact ⟨σ.nonempty_of_mem A hA, hAu⟩
    · refine ⟨(compl_ne_univ_iff_nonempty A).1 hAu, ?_⟩
      rintro rfl
      exact (σ.nonempty_of_mem _ hA).ne_empty compl_univ
  · rintro ⟨hne, hAu⟩
    have h1 : 1 ≤ #A := card_pos.2 hne
    have hc : #A + #Aᶜ = Fintype.card X := card_add_card_compl A
    have h2 : 1 ≤ #Aᶜ := card_pos.2 (by
      obtain ⟨x, hx⟩ := (not_forall.1 fun h => hAu (eq_univ_iff_forall.2 h))
      exact ⟨x, mem_compl.2 hx⟩)
    by_cases hA1 : #A = 1
    · obtain ⟨x, rfl⟩ := card_eq_one.1 hA1
      exact Or.inl ⟨σ.singleton_mem x, hAu⟩
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by omega)
      exact Or.inr ⟨hx ▸ σ.singleton_mem x, (compl_ne_univ_iff_nonempty A).2 hne⟩

/-- On at most three taxa there is no internal edge in an unrooted tree. -/
theorem sameUnrootedMetricTree_of_card_le_three (hX : Fintype.card X ≤ 3)
    (σ σ' : SpeciesTree X) : σ.SameUnrootedMetricTree σ' := by
  refine ⟨?_, fun A _ h1 h2 => ?_⟩
  · ext A
    rw [hier_mem_unroot_of_card_le_three hX σ, hier_mem_unroot_of_card_le_three hX σ']
  · have := card_add_card_compl A
    omega

/-! ### Unrooting induced subtrees -/

/-- The unrooted topology of an induced subtree is the induced unrooted topology. -/
theorem restrict_unroot (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    unroot (σ.restrict S hS).clusters = restrictSplits S (unroot σ.clusters) :=
  unroot_restrictClusters σ.clusters S

/-- The length of an internal edge of the unrooted induced subtree `σ⁻(S)`: the sum of the
unrooted lengths of the splits of `σ⁻` that induce its split. -/
theorem restrict_unrootedLength (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty)
    (C : Finset S) (hC₁ : 2 ≤ #C)
    (hC₂ : 2 ≤ #Cᶜ) :
    (σ.restrict S hS).unrootedLength C =
      (1 / 2 : ℝ) * ∑ A ∈ unroot σ.clusters with A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ,
        σ.unrootedLength A := by
  have : Nonempty X := ⟨hS.choose⟩
  have hCne : C.Nonempty := card_pos.1 (by omega)
  have hCcne : Cᶜ.Nonempty := card_pos.1 (by omega)
  have hCu : C ≠ univ := fun e => by
    rw [e, compl_univ] at hCcne
    exact not_nonempty_empty hCcne
  have hCcu : Cᶜ ≠ univ := (compl_ne_univ_iff_nonempty C).2 hCne
  -- `p A`: the trace of `A` is a side of the split `C | Cᶜ`
  set p : Finset X → Prop := fun A => A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ with hp
  have hpc : ∀ A, p Aᶜ ↔ p A := by
    intro A
    simp only [hp, subtype_compl, compl_inj_iff]
    rw [compl_eq_comm, eq_comm (a := Cᶜ)]
    exact or_comm
  set M := ∑ A ∈ σ.clusters with A ≠ univ ∧ p A, σ.length A with hM
  -- the left side is `M`: group the clusters of `σ` by their trace
  have hL : (σ.restrict S hS).unrootedLength C = M := by
    unfold unrootedLength
    rw [restrict_clusters, restrict_length, hM]
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun A => A.subtype (· ∈ S))
      (t := (restrictClusters S σ.clusters).filter (fun D => D ≠ univ ∧ (D = C ∨ D = Cᶜ)))]
    · apply Finset.sum_congr rfl
      intro D hD
      unfold restrictLength
      rw [filter_filter]
      refine Finset.sum_congr (filter_congr fun A _ => ?_) fun _ _ => rfl
      have hD' := (mem_filter.1 hD).2.2
      constructor
      · rintro ⟨⟨h2, -⟩, h3⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        have hpA : p A := by
          show A.subtype (· ∈ S) = C ∨ A.subtype (· ∈ S) = Cᶜ
          rw [h3]
          exact hD'
        exact ⟨⟨h2, hpA⟩, h3⟩
    · intro A hA
      obtain ⟨hA1, -, hA3⟩ := mem_filter.1 hA
      refine mem_filter.2 ⟨mem_restrictClusters.2 ⟨A, hA1, ?_, rfl⟩, ?_, hA3⟩
      · rw [← subtype_nonempty_iff]
        rcases hA3 with h | h <;> rw [h] <;> assumption
      · rcases hA3 with h | h <;> rw [h] <;> assumption
  -- the sum on the right side is `2 * M`: each cluster `A` is counted once as `A` and once as `Aᶜ`
  set f : Finset X → ℝ := fun B => if B ∈ σ.clusters ∧ B ≠ univ then σ.length B else 0 with hf
  have key1 : ∀ A, σ.unrootedLength A = f A + f Aᶜ := by
    intro A
    unfold unrootedLength
    rw [show σ.clusters.filter (fun B => B ≠ univ ∧ (B = A ∨ B = Aᶜ)) =
        ({A, Aᶜ} : Finset (Finset X)).filter (fun B => B ∈ σ.clusters ∧ B ≠ univ) by
      ext B
      simp only [mem_filter, mem_insert, mem_singleton]
      tauto]
    rw [sum_filter, sum_pair ne_compl_self]
  have hT : ∀ A ∈ (unroot σ.clusters).filter p, Aᶜ ∈ (unroot σ.clusters).filter p := by
    intro A hA
    obtain ⟨hA1, hA2⟩ := mem_filter.1 hA
    exact mem_filter.2 ⟨compl_mem_unroot.2 hA1, (hpc A).2 hA2⟩
  have key2 : ∑ A ∈ (unroot σ.clusters).filter p, f Aᶜ =
      ∑ A ∈ (unroot σ.clusters).filter p, f A :=
    Finset.sum_nbij' compl compl hT hT (fun A _ => compl_compl A) (fun A _ => compl_compl A)
      (fun _ _ => rfl)
  have key3 : ∑ A ∈ (unroot σ.clusters).filter p, f A = M := by
    simp only [hf, hM]
    rw [← sum_filter, filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext A
    simp only [mem_filter]
    constructor
    · rintro ⟨-, hpA, hA, hAu⟩
      exact ⟨hA, hAu, hpA⟩
    · rintro ⟨hA, hAu, hpA⟩
      exact ⟨mem_unroot.2 (Or.inl ⟨hA, hAu⟩), hpA, hA, hAu⟩
  have hR : ∑ A ∈ unroot σ.clusters with p A, σ.unrootedLength A = 2 * M := by
    rw [Finset.sum_congr rfl fun A _ => key1 A, sum_add_distrib, key2, key3]
    ring
  rw [hL, hR]
  ring

/-- The two sides of a split have the same unrooted length. -/
theorem unrootedLength_compl (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength Aᶜ = σ.unrootedLength A := by
  unfold unrootedLength
  refine Finset.sum_congr (filter_congr fun B _ => ?_) fun _ _ => rfl
  rw [compl_compl, or_comm]

/-- If `A | Aᶜ` is the only split of `σ⁻` inducing the split `C | Cᶜ` of `σ⁻(S)` (where `C` is the
trace of `A` on `S`), then the two splits have the same length. -/
theorem restrict_unrootedLength_eq_of_unique (σ : SpeciesTree X) (S : Finset X)
    (hS : S.Nonempty) {A : Finset X} (hA : A ∈ unroot σ.clusters) {C : Finset S}
    (hAC : A.subtype (· ∈ S) = C) (hC₁ : 2 ≤ #C) (hC₂ : 2 ≤ #Cᶜ)
    (huniq : ∀ B ∈ unroot σ.clusters,
      B.subtype (· ∈ S) = C ∨ B.subtype (· ∈ S) = Cᶜ → B = A ∨ B = Aᶜ) :
    (σ.restrict S hS).unrootedLength C = σ.unrootedLength A := by
  have : Nonempty X := ⟨hS.choose⟩
  have hCu : C ≠ univ := fun e => by
    have hCcne : Cᶜ.Nonempty := card_pos.1 (by omega)
    rw [e, compl_univ] at hCcne
    exact not_nonempty_empty hCcne
  have hCmem : C ∈ unroot (σ.restrict S hS).clusters := by
    rw [restrict_unroot, mem_restrictSplits]
    refine ⟨A, hA, ?_, subtype_ne_univ_iff.1 (hAC ▸ hCu), hAC⟩
    rw [← subtype_nonempty_iff, hAC]
    exact card_pos.1 (by omega)
  rw [restrict_unrootedLength σ S hS C hC₁ hC₂]
  have hset : (unroot σ.clusters).filter
      (fun B => B.subtype (· ∈ S) = C ∨ B.subtype (· ∈ S) = Cᶜ) = {A, Aᶜ} := by
    ext B
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hB, hBC⟩
      exact huniq B hB hBC
    · rintro (rfl | rfl)
      · exact ⟨hA, Or.inl hAC⟩
      · exact ⟨compl_mem_unroot.2 hA, Or.inr (by rw [subtype_compl, hAC])⟩
  rw [hset, sum_pair ne_compl_self, unrootedLength_compl]
  ring

end SpeciesTree

end Phylogenetics
