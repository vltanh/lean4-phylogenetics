module

public import Phylogenetics.MSC.Basic
public import Phylogenetics.Coalescent.Relabel

/-!
# Relabelling taxa

Everything in the model is natural with respect to bijections of the taxa: relabelling a species
tree relabels its gene tree distributions. The relabelling of families of clusters and Kingman's
coalescent is in `Phylogenetics.Coalescent.Relabel`.

* `SpeciesTree.relabel σ e`: the species tree `σ` with taxa relabelled by `e`.

## Main results

* `forestDist_relabel`: naturality of the multispecies coalescent under relabelling the taxa and
  the lineages; `forestDist_relabel_lineages`: relabelling the lineages only.
* `SpeciesTree.unrootedDist_relabel`, `SpeciesTree.rootedDist_relabel`: the gene tree
  distributions of the relabelled tree are the relabelled distributions.
* `SpeciesTree.sameRootedMetricTree_relabel_iff`, `SpeciesTree.sameUnrootedMetricTree_relabel_iff`:
  relabelling preserves and reflects equality of metric trees.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]


omit [DecidableEq X] [DecidableEq Y] in
private lemma msc_map_eq_univ_iff (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]





section Naturality

variable {L : Type*} [Fintype L] [DecidableEq L] {M : Type*} [Fintype M] [DecidableEq M]


omit [Fintype X] [Fintype Y] in
theorem sampledForest_relabel (e : X ≃ Y) (eL : L ≃ M) {s : L → X} {s' : M → Y}
    (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X) :
    sampledForest s' (A.map e.toEmbedding) = relabelFamily eL (sampledForest s A) := by
  ext C
  rw [mem_sampledForest, mem_relabelFamily, mem_sampledForest]
  constructor
  · rintro ⟨l', hl', rfl⟩
    refine ⟨eL.symm l', ?_, by simp⟩
    have := hs (eL.symm l')
    rw [eL.apply_symm_apply] at this
    rw [this, Finset.mem_map_equiv, e.symm_apply_apply] at hl'
    exact hl'
  · rintro ⟨l, hl, hC⟩
    refine ⟨eL l, ?_, ?_⟩
    · rw [hs]
      exact Finset.mem_map_of_mem _ hl
    · rw [← map_map_symm_equiv eL C, ← hC]
      simp

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype L] [Fintype M] in
private lemma msc_relabelFamily_sup {ι : Type*} [Fintype ι] (eL : L ≃ M)
    (f : ι → Finset (Finset L)) :
    relabelFamily eL (univ.sup f) = univ.sup (fun i => relabelFamily eL (f i)) :=
  Finset.apply_sup_eq_sup_comp (relabelFamily eL) (fun F G => image_union F G) (image_empty _)

private lemma msc_sup_univ_equiv {ι κ α : Type*} [Fintype ι] [Fintype κ] [SemilatticeSup α]
    [OrderBot α] (ψ : ι ≃ κ) (g : κ → α) :
    univ.sup (fun i => g (ψ i)) = univ.sup g := by
  conv_rhs => rw [← Finset.map_univ_equiv ψ, Finset.sup_map]
  rfl

theorem populationKernel_relabel (e : X ≃ Y) (eL : L ≃ M)
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    (A : Finset X) (F G : Finset (Finset L)) :
    populationKernel len' (A.map e.toEmbedding) (relabelFamily eL F) (relabelFamily eL G) =
      populationKernel len A F G := by
  unfold populationKernel
  by_cases hA : A = univ
  · rw [ite_eq_left ((msc_map_eq_univ_iff e A).2 hA), ite_eq_left hA]
    exact kingmanAbsorption_relabelFamily eL F G
  · rw [ite_eq_right (mt (msc_map_eq_univ_iff e A).1 hA), ite_eq_right hA, hlen]
    exact kingmanTransition_relabelFamily eL _ F G

/-- **Naturality of the multispecies coalescent.** Relabelling the taxa along `e` and the
lineages along `eL` (compatibly with the sampling maps) relabels the distribution of the forest
leaving each population. -/
theorem forestDist_relabel (e : X ≃ Y) (eL : L ≃ M) (H : Finset (Finset X))
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} (hlen : ∀ A, len' (A.map e.toEmbedding) = len A)
    {s : L → X} {s' : M → Y} (hs : ∀ l, s' (eL l) = e (s l)) (A : Finset X)
    (G : Finset (Finset L)) :
    forestDist (relabelFamily e H) len' s' (A.map e.toEmbedding) (relabelFamily eL G) =
      forestDist H len s A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e H), forestDist.eq_1 H]
  have hch := childClusters_relabelFamily e H A
  let ψ : childClusters H A ≃ childClusters (relabelFamily e H) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [hch, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (relabelFamilyEquiv eL)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ : ∀ B : childClusters H A, Φ f (ψ B) = relabelFamily eL (f B) := fun B => by
    simp [Φ, Equiv.arrowCongr_apply]
  have hψ : ∀ B : childClusters H A,
      ((ψ B : childClusters (relabelFamily e H) (A.map e.toEmbedding)) : Finset Y) =
        (B : Finset X).map e.toEmbedding := fun B => rfl
  congr 1
  · rw [← ψ.prod_comp]
    refine Finset.prod_congr rfl fun B _ => ?_
    rw [hΦ, hψ]
    exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) = relabelFamily eL (univ.sup f) := by
      rw [msc_relabelFamily_sup, ← msc_sup_univ_equiv ψ]
      simp only [hΦ]
    rw [hsup, sampledForest_relabel e eL hs, ← relabelFamily_union]
    exact populationKernel_relabel e eL hlen A _ G


/-- Relabelling the lineages only. -/
theorem forestDist_relabel_lineages (eL : L ≃ M) (H : Finset (Finset X)) (len : Finset X → ℝ)
    (s : L → X) (A : Finset X) (G : Finset (Finset L)) :
    forestDist H len (s ∘ eL.symm) A (relabelFamily eL G) = forestDist H len s A G := by
  have hmap : ∀ B : Finset X, B.map (Equiv.refl X).toEmbedding = B := fun B => by
    ext x
    simp
  have := forestDist_relabel (Equiv.refl X) eL H (len := len) (len' := len)
    (fun B => by rw [hmap]) (s := s) (s' := s ∘ eL.symm) (fun l => by simp) A G
  rwa [relabelFamily_refl, hmap] at this

end Naturality

theorem SpeciesTree.relabel_univ_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    (univ : Finset Y) ∈ relabelFamily e σ.clusters :=
  mem_image.2 ⟨univ, σ.univ_mem, Finset.map_univ_equiv e⟩

omit [Fintype Y] in
theorem SpeciesTree.relabel_singleton_mem (σ : SpeciesTree X) (e : X ≃ Y) (y : Y) :
    {y} ∈ relabelFamily e σ.clusters :=
  mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩

omit [Fintype Y] in
theorem SpeciesTree.relabel_nonempty_of_mem (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B.Nonempty := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  exact Finset.map_nonempty.2 (σ.nonempty_of_mem A hA)

omit [Fintype Y] in
theorem SpeciesTree.relabel_laminar (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, ∀ C ∈ relabelFamily e σ.clusters,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  intro B hB C hC
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
  rw [Finset.map_subset_map, Finset.map_subset_map, Finset.disjoint_map]
  exact σ.laminar A hA A' hA'

theorem SpeciesTree.relabel_length_pos (σ : SpeciesTree X) (e : X ≃ Y) :
    ∀ B ∈ relabelFamily e σ.clusters, B ≠ univ → 0 < σ.length (B.map e.symm.toEmbedding) := by
  intro B hB hBu
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [map_symm_map_equiv]
  exact σ.length_pos A hA fun h => hBu ((msc_map_eq_univ_iff e A).2 h)

/-- The species tree `σ` with its taxa relabelled by `e`. -/
def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := σ.relabel_univ_mem e
  singleton_mem := σ.relabel_singleton_mem e
  nonempty_of_mem := σ.relabel_nonempty_of_mem e
  laminar := σ.relabel_laminar e
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos := σ.relabel_length_pos e

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

theorem SpeciesTree.relabel_length (σ : SpeciesTree X) (e : X ≃ Y) (B : Finset Y) :
    (σ.relabel e).length B = σ.length (B.map e.symm.toEmbedding) := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A := by
  rw [SpeciesTree.relabel_length, map_symm_map_equiv]

private lemma msc_speciesTree_eq {σ σ' : SpeciesTree X} (h1 : σ.clusters = σ'.clusters)
    (h2 : σ.length = σ'.length) : σ = σ' := by
  cases σ
  cases σ'
  cases h1
  cases h2
  rfl

/-- Relabelling back along `e.symm` gives the original species tree. -/
theorem SpeciesTree.relabel_relabel_symm (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).relabel e.symm = σ := by
  refine msc_speciesTree_eq (relabelFamily_symm e σ.clusters) ?_
  funext A
  show σ.length ((A.map e.symm.symm.toEmbedding).map e.symm.toEmbedding) = σ.length A
  rw [Equiv.symm_symm, map_symm_map_equiv]

private lemma msc_isBinary_relabel {σ : SpeciesTree X} (e : X ≃ Y) (h : σ.IsBinary) :
    (σ.relabel e).IsBinary := by
  intro B hB hB2
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [Finset.card_map] at hB2
  obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := h A hA hB2
  refine ⟨C.map e.toEmbedding, mem_image_of_mem _ hC, D.map e.toEmbedding, mem_image_of_mem _ hD,
    (Finset.disjoint_map _).2 hCD, ?_⟩
  rw [← Finset.map_union, hCDA]

theorem SpeciesTree.isBinary_relabel_iff (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).IsBinary ↔ σ.IsBinary := by
  refine ⟨fun h => ?_, msc_isBinary_relabel e⟩
  have := msc_isBinary_relabel e.symm h
  rwa [SpeciesTree.relabel_relabel_symm] at this

theorem SpeciesTree.rootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (G : Finset (Finset X)) :
    (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := by
  unfold SpeciesTree.rootedDist
  have := forestDist_relabel e e σ.clusters (len := σ.length) (len' := (σ.relabel e).length)
    (σ.relabel_length_map e) (s := id) (s' := id) (fun _ => rfl) univ G
  rwa [Finset.map_univ_equiv] at this

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  unfold SpeciesTree.unrootedDist
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [relabelFamilyEquiv_apply, unroot_relabelFamily, (relabelFamily_injective e).eq_iff,
    SpeciesTree.rootedDist_relabel]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  constructor
  · intro h
    funext T
    have := congrFun h (relabelFamily e T)
    rwa [SpeciesTree.unrootedDist_relabel, SpeciesTree.unrootedDist_relabel] at this
  · intro h
    funext T
    obtain ⟨T₀, rfl⟩ := (relabelFamilyEquiv e).surjective T
    rw [relabelFamilyEquiv_apply, SpeciesTree.unrootedDist_relabel,
      SpeciesTree.unrootedDist_relabel, h]

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  unfold SpeciesTree.SameRootedMetricTree
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAu => ?_,
    fun h B hB hB2 hBu => ?_⟩
  · have := h (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
      fun h' => hAu ((msc_map_eq_univ_iff e A).1 h')
    rwa [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map] at this
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map]
    exact h A hA (by rwa [Finset.card_map] at hB2) fun h' => hBu ((msc_map_eq_univ_iff e A).2 h')

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [SpeciesTree.relabel_clusters]
  unfold relabelFamily
  rw [filter_image, sum_image fun x _ y _ h => Finset.map_injective _ h]
  refine Finset.sum_congr (filter_congr fun C _ => ?_) fun C _ =>
    SpeciesTree.relabel_length_map σ e C
  simp only [ne_eq, msc_map_eq_univ_iff, Finset.map_inj, compl_map_equiv]

theorem SpeciesTree.sameUnrootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameUnrootedMetricTree (σ'.relabel e) ↔ σ.SameUnrootedMetricTree σ' := by
  unfold SpeciesTree.SameUnrootedMetricTree
  simp only [SpeciesTree.relabel_clusters, unroot_relabelFamily]
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAc2 => ?_,
    fun h B hB hB2 hBc2 => ?_⟩
  · have := h (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
      (by rwa [compl_map_equiv, Finset.card_map])
    rwa [SpeciesTree.unrootedLength_relabel, SpeciesTree.unrootedLength_relabel] at this
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [SpeciesTree.unrootedLength_relabel, SpeciesTree.unrootedLength_relabel]
    exact h A hA (by rwa [Finset.card_map] at hB2) (by rwa [compl_map_equiv, Finset.card_map] at hBc2)

end Phylogenetics
