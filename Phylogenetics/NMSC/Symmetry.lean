module

public import Phylogenetics.Coalescent.Relabel
public import Phylogenetics.NMSC.Marginal

/-!
# Symmetry of the network multispecies coalescent

The process with injected forests is natural with respect to permutations of the lineages
(`injDist_relabel`). When four lineages are injected, this decides the mass of the forests
containing a cherry of a quartet tree (`cherryMass`) in two cases, as `Phylogenetics.NiceKernel.score`
does in `Phylogenetics.NMSC.Level1.Symmetry`:

* once a cluster of two lineages is present, it stays, and it decides the split
  (`cherryMass_of_mem`);
* if the injected forests are fixed by the transpositions of all but one of the four lineages, then
  the three quartet trees are equally likely (`cherryMass_eq_third`).

## Main results

* `injDist_relabel`, `cherryMass_relabel`: naturality.
* `sum_cherryMass`: the three quartet trees have total mass one.
* `cherryMass_of_mem`, `cherryMass_eq_third`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- The injected forests relabelled by a permutation of the lineages. -/
def relabelInj (π : Equiv.Perm X) (inj : V → Finset (Finset X)) : V → Finset (Finset X) :=
  fun v => relabelFamily π (inj v)

/-- The forests of all arcs relabelled by a permutation of the lineages. -/
abbrev relabelAll (π : Equiv.Perm X) (t : E → Finset (Finset X)) : E → Finset (Finset X) :=
  fun f => relabelFamily π (t f)

omit [Fintype V] [Fintype X] in
theorem arriving_relabel (π : Equiv.Perm X) (inj : V → Finset (Finset X))
    (top : E → Finset (Finset X)) (v : V) :
    arriving N (relabelInj π inj) (relabelAll π top) v =
      relabelFamily π (arriving N inj top v) := by
  unfold arriving relabelInj
  rw [relabelFamily_union, relabelFamily_biUnion]

omit [Fintype V] in
/-- The allocation is natural: the roots are relabelled along. -/
theorem allocationFactor_relabel (π : Equiv.Perm X) (F : Finset (Finset X)) (v : V)
    (b : E → Finset (Finset X)) :
    allocationFactor N θ ρ (relabelFamily π F) v (relabelAll π b) =
      allocationFactor N θ ρ F v b := by
  let σ : {A // A ∈ roots F} ≃ {A // A ∈ roots (relabelFamily π F)} :=
    (Equiv.finsetCongr π).subtypeEquiv fun A => by
      rw [roots_relabelFamily, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  have hσ : ∀ r, (σ r).val = r.val.map π.toEmbedding := fun r => rfl
  unfold allocationFactor
  rw [← (Equiv.arrowCongr σ (Equiv.refl {e // N.graph.target e = v})).sum_comp]
  refine sum_congr rfl fun a _ => ?_
  have ha : ∀ r, Equiv.arrowCongr σ (Equiv.refl {e // N.graph.target e = v}) a (σ r) = a r := by
    intro r
    simp [Equiv.arrowCongr_apply]
  have hR : ∀ e : {e // N.graph.target e = v},
      (univ.filter fun r' =>
          Equiv.arrowCongr σ (Equiv.refl {e // N.graph.target e = v}) a r' = e).image Subtype.val =
        relabelFamily π ((univ.filter fun r => a r = e).image Subtype.val) := by
    intro e
    ext C
    constructor
    · intro hC
      obtain ⟨r', hr', rfl⟩ := mem_image.1 hC
      obtain ⟨r, rfl⟩ := σ.surjective r'
      have hr := (mem_filter.1 hr').2
      rw [ha] at hr
      rw [hσ]
      exact mem_image_of_mem _ (mem_image.2 ⟨r, mem_filter.2 ⟨mem_univ _, hr⟩, rfl⟩)
    · intro hC
      obtain ⟨_, hA, rfl⟩ := mem_image.1 hC
      obtain ⟨r, hr, rfl⟩ := mem_image.1 hA
      refine mem_image.2 ⟨σ r, mem_filter.2 ⟨mem_univ _, ?_⟩, hσ r⟩
      rw [ha]
      exact (mem_filter.1 hr).2
  have hc : (∀ e : {e // N.graph.target e = v}, relabelAll π b e.val =
        forestBelow (relabelFamily π F) ((univ.filter fun r' =>
          Equiv.arrowCongr σ (Equiv.refl {e // N.graph.target e = v}) a r' = e).image
            Subtype.val)) ↔
      ∀ e : {e // N.graph.target e = v}, b e.val =
        forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) := by
    refine forall_congr' fun e => ?_
    rw [hR, forestBelow_relabelFamily]
    exact (relabelFamily_injective π).eq_iff
  simp only [hc]
  have hw : allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val)
        (Equiv.arrowCongr σ (Equiv.refl {e // N.graph.target e = v}) a) =
      allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a :=
    allocationWeight_comp σ.symm a
  simp only [hw]

omit [Fintype V] in
theorem vertexWeight_relabel (π : Equiv.Perm X) (inj : V → Finset (Finset X)) (v : V)
    (bot top : E → Finset (Finset X)) :
    vertexWeight N θ ρ (relabelInj π inj) v (relabelAll π bot) (relabelAll π top) =
      vertexWeight N θ ρ inj v bot top := by
  unfold vertexWeight
  rw [arriving_relabel, allocationFactor_relabel]
  congr 1
  exact prod_congr rfl fun f _ => kingmanTransition_relabelFamily π _ _ _

/-- The forests of all arcs relabelled, as an equivalence. -/
def relabelAllEquiv (π : Equiv.Perm X) :
    (E → Finset (Finset X)) ≃ (E → Finset (Finset X)) :=
  Equiv.arrowCongr (Equiv.refl E) (relabelFamilyEquiv π)

omit [Fintype E] [Fintype X] in
theorem relabelAllEquiv_apply (π : Equiv.Perm X) (t : E → Finset (Finset X)) :
    relabelAllEquiv π t = relabelAll π t := rfl

/-- **Naturality of the process with injected forests** under permutations of the lineages. -/
theorem injDist_relabel (π : Equiv.Perm X) (inj : V → Finset (Finset X)) (G : Finset (Finset X)) :
    injDist N θ ρ (relabelInj π inj) (relabelFamily π G) = injDist N θ ρ inj G := by
  unfold injDist injWeight
  rw [← (relabelAllEquiv (E := E) π).sum_comp]
  refine sum_congr rfl fun bot _ => ?_
  rw [← (relabelAllEquiv (E := E) π).sum_comp]
  refine sum_congr rfl fun top _ => ?_
  simp only [relabelAllEquiv_apply, vertexWeight_relabel, arriving_relabel,
    kingmanAbsorption_relabelFamily]

/-! ### Quartet trees -/

/-- The quartet tree relabelled by a permutation of the taxa. -/
def relabelQuartet (π : Equiv.Perm X) (r : QuartetTree X) : QuartetTree X :=
  ⟨relabelFamily π r.val, by
    refine ⟨by rw [card_relabelFamily]; exact r.property.1, fun B hB => ?_, fun B hB C hC hBC => ?_⟩
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      rw [card_map]
      exact r.property.2.1 A hA
    · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      obtain ⟨D, hD, rfl⟩ := mem_image.1 hC
      exact (disjoint_map _).2 (r.property.2.2 A hA D hD fun h => hBC (h ▸ rfl))⟩

omit [Fintype X] in
theorem taxa_relabelQuartet [Fintype X] (π : Equiv.Perm X) (r : QuartetTree X) :
    (relabelQuartet π r).taxa = r.taxa.map π.toEmbedding := by
  ext x
  simp only [QuartetTree.taxa, relabelQuartet, relabelFamily, mem_sup, mem_image, id, mem_map]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact ⟨y, ⟨A, hA, hy⟩, rfl⟩
  · rintro ⟨y, ⟨A, hA, hy⟩, rfl⟩
    exact ⟨_, ⟨A, hA, rfl⟩, mem_map_of_mem _ hy⟩

omit [Fintype X] in
private theorem cherry_relabel [Fintype X] (π : Equiv.Perm X) (r : QuartetTree X)
    (H : Finset (Finset X)) :
    (∃ B ∈ (relabelQuartet π r).val, B ∈ relabelFamily π H) ↔ ∃ B ∈ r.val, B ∈ H := by
  constructor
  · rintro ⟨B, hB, hBH⟩
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact ⟨A, hA, map_mem_relabelFamily.1 hBH⟩
  · rintro ⟨A, hA, hAH⟩
    exact ⟨A.map π.toEmbedding, mem_image_of_mem _ hA, map_mem_relabelFamily.2 hAH⟩

/-- Naturality of the mass of a quartet tree. -/
theorem cherryMass_relabel (π : Equiv.Perm X) (inj : V → Finset (Finset X)) (r : QuartetTree X) :
    cherryMass N θ ρ (relabelInj π inj) (relabelQuartet π r) = cherryMass N θ ρ inj r := by
  unfold cherryMass
  rw [← (relabelFamilyEquiv π).sum_comp]
  refine sum_congr rfl fun H _ => ?_
  simp only [relabelFamilyEquiv_apply, cherry_relabel, injDist_relabel]

/-! ### Clusters of two lineages -/

omit [Fintype X] in
/-- A cluster of two lineages of a forest on the taxa of a quartet tree: if the forest contains a
cherry of the quartet tree, the cluster is a cherry. -/
theorem mem_val_of_cherry [Fintype X] {H : Finset (Finset X)} (hH : IsForest H) {C : Finset X}
    (hC : C ∈ H) (hC2 : #C = 2) {r : QuartetTree X} (hCr : C ⊆ r.taxa) {B : Finset X}
    (hB : B ∈ r.val) (hBH : B ∈ H) : C ∈ r.val := by
  have hB2 := r.card_of_mem hB
  rcases hH.2 C hC B hBH with h | h | h
  · rwa [eq_of_subset_of_card_le h (by omega)]
  · rwa [(eq_of_subset_of_card_le h (by omega)).symm]
  · have hsub : C ⊆ r.taxa \ B := fun x hx =>
      mem_sdiff.2 ⟨hCr hx, disjoint_left.1 h hx⟩
    have hcard : #(r.taxa \ B) = 2 := by
      rw [card_sdiff_of_subset (r.subset_taxa hB), r.card_taxa, hB2]
    rw [eq_of_subset_of_card_le hsub (by omega)]
    exact r.sdiff_mem hB

/-- A cluster of two lineages, injected, decides the mass of the quartet trees. -/
theorem cherryMass_of_mem (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {v : V} {C : Finset X} (hC : C ∈ inj v)
    (hC2 : #C = 2) {r : QuartetTree X} (hCr : C ⊆ r.taxa) :
    cherryMass N θ ρ inj r = if C ∈ r.val then 1 else 0 := by
  unfold cherryMass
  split_ifs with hm
  · rw [← sum_injDist (θ := θ) (ρ := ρ) hN hθ hρ hinj]
    refine sum_congr rfl fun H _ => ?_
    by_cases hd : injDist N θ ρ inj H = 0
    · simp [hd]
    · obtain ⟨-, hsub, -⟩ := injDist_support hN hinj hd
      rw [ite_eq_left ⟨C, hm, hsub v hC⟩]
  · refine sum_eq_zero fun H _ => ?_
    by_cases hd : injDist N θ ρ inj H = 0
    · simp [hd]
    · obtain ⟨hgood, hsub, -⟩ := injDist_support hN hinj hd
      refine ite_eq_right fun ⟨B, hB, hBH⟩ => ?_
      exact absurd (mem_val_of_cherry hgood.1 (hsub v hC) hC2 hCr hB hBH) hm

/-- The three quartet trees on the four injected lineages have total mass one. -/
theorem sum_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {Y : Finset X} (hY : #Y = 4)
    (hlin : ∀ x, (∃ u, x ∈ lineages (inj u)) ↔ x ∈ Y) :
    ∑ r ∈ treesOn Y, cherryMass N θ ρ inj r = 1 := by
  unfold cherryMass
  rw [sum_comm, ← sum_injDist (θ := θ) (ρ := ρ) hN hθ hρ hinj]
  refine sum_congr rfl fun H _ => ?_
  by_cases hd : injDist N θ ρ inj H = 0
  · simp [hd]
  obtain ⟨hgood, -, hl, hone⟩ := injDist_support hN hinj hd
  obtain ⟨x₀, hx₀⟩ : Y.Nonempty := card_pos.1 (by omega)
  obtain ⟨u₀, hu₀⟩ := (hlin x₀).2 hx₀
  obtain ⟨A₀, hA₀, -⟩ := mem_lineages.1 hu₀
  have hone' := hone ⟨u₀, A₀, hA₀⟩
  have hYH : lineages H = Y := by
    ext x
    rw [hl, hlin]
  have hYm : Y ∈ H := by
    have := lineages_mem_of_card_roots_eq_one hone'
    rwa [hYH] at this
  obtain ⟨C, hC, hCY, hC2⟩ := hgood.exists_two Y hYm (by omega)
  let r₀ := quartetOfCherry Y C hY hCY hC2
  have hr₀t : r₀.taxa = Y := quartetOfCherry_taxa Y C hY hCY hC2
  have hCr₀ : C ∈ r₀.val := by simp [r₀]
  rw [sum_eq_single r₀]
  · rw [ite_eq_left ⟨C, hCr₀, hC⟩]
  · intro r hr hne
    refine ite_eq_right fun ⟨B, hB, hBH⟩ => ?_
    have hrt : r.taxa = Y := mem_treesOn.1 hr
    have hCr : C ∈ r.val :=
      mem_val_of_cherry hgood.1 hC hC2 (by rw [hrt]; exact hCY) hB hBH
    exact hne (QuartetTree.eq_of_taxa_eq_of_mem (hrt.trans hr₀t.symm) hCr hCr₀)
  · exact fun h => absurd (mem_treesOn.2 hr₀t) h

omit [Fintype X] in
/-- Each taxon of a quartet tree lies in a cherry. -/
theorem exists_cherry_mem [Fintype X] (r : QuartetTree X) {a : X} (ha : a ∈ r.taxa) :
    ∃ B ∈ r.val, a ∈ B := by
  simpa [QuartetTree.taxa, mem_sup] using ha

/-- **The three quartet trees are equally likely** when the injected forests are fixed by the
transpositions of all but one of the four lineages. -/
theorem cherryMass_eq_third (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {Y : Finset X} (hY : #Y = 4)
    (hlin : ∀ x, (∃ u, x ∈ lineages (inj u)) ↔ x ∈ Y) {a : X} (ha : a ∈ Y)
    (hsym : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ a → y ≠ a → relabelInj (Equiv.swap x y) inj = inj)
    {r : QuartetTree X} (hr : r ∈ treesOn Y) : cherryMass N θ ρ inj r = 1 / 3 := by
  have heq : ∀ r₁ ∈ treesOn Y, ∀ r₂ ∈ treesOn Y,
      cherryMass N θ ρ inj r₁ = cherryMass N θ ρ inj r₂ := by
    intro r₁ h₁ r₂ h₂
    have ht₁ := mem_treesOn.1 h₁
    have ht₂ := mem_treesOn.1 h₂
    obtain ⟨B₁, hB₁, haB₁⟩ := exists_cherry_mem r₁ (ht₁ ▸ ha)
    obtain ⟨B₂, hB₂, haB₂⟩ := exists_cherry_mem r₂ (ht₂ ▸ ha)
    obtain ⟨x₁, hx₁⟩ : ∃ x₁, B₁ = {a, x₁} ∧ x₁ ≠ a := by
      obtain ⟨u, v, huv, hB⟩ := card_eq_two.1 (r₁.card_of_mem hB₁)
      rw [hB, mem_insert, mem_singleton] at haB₁
      rcases haB₁ with rfl | rfl
      · exact ⟨v, hB, huv.symm⟩
      · exact ⟨u, by rw [hB, pair_comm], huv⟩
    obtain ⟨x₂, hx₂⟩ : ∃ x₂, B₂ = {a, x₂} ∧ x₂ ≠ a := by
      obtain ⟨u, v, huv, hB⟩ := card_eq_two.1 (r₂.card_of_mem hB₂)
      rw [hB, mem_insert, mem_singleton] at haB₂
      rcases haB₂ with rfl | rfl
      · exact ⟨v, hB, huv.symm⟩
      · exact ⟨u, by rw [hB, pair_comm], huv⟩
    obtain ⟨hBe₁, hxa₁⟩ := hx₁
    obtain ⟨hBe₂, hxa₂⟩ := hx₂
    have hxY₁ : x₁ ∈ Y := ht₁ ▸ r₁.subset_taxa hB₁ (by simp [hBe₁])
    have hxY₂ : x₂ ∈ Y := ht₂ ▸ r₂.subset_taxa hB₂ (by simp [hBe₂])
    by_cases hx : x₁ = x₂
    · have : r₁ = r₂ := QuartetTree.eq_of_taxa_eq_of_mem (ht₁.trans ht₂.symm) hB₁
        (by rw [hBe₁, hx, ← hBe₂]; exact hB₂)
      rw [this]
    · have hsw : relabelQuartet (Equiv.swap x₁ x₂) r₁ = r₂ := by
        refine QuartetTree.eq_of_taxa_eq_of_mem ?_ (B := B₂) ?_ hB₂
        · rw [taxa_relabelQuartet, ht₁, ht₂]
          ext z
          simp only [mem_map_equiv, Equiv.symm_swap]
          by_cases hz1 : z = x₁
          · subst hz1
            simp [hxY₁, hxY₂]
          by_cases hz2 : z = x₂
          · subst hz2
            simp [hxY₁, hxY₂]
          rw [Equiv.swap_apply_of_ne_of_ne hz1 hz2]
        · have : B₂ = B₁.map (Equiv.swap x₁ x₂).toEmbedding := by
            rw [hBe₁, hBe₂, map_insert, map_singleton]
            simp [Equiv.swap_apply_of_ne_of_ne hxa₁.symm hxa₂.symm]
          rw [this]
          exact mem_image_of_mem _ hB₁
      have := cherryMass_relabel (N := N) (θ := θ) (ρ := ρ) (Equiv.swap x₁ x₂) inj r₁
      rw [hsw, hsym x₁ hxY₁ x₂ hxY₂ hxa₁ hxa₂] at this
      exact this.symm
  have hsum := sum_cherryMass (θ := θ) (ρ := ρ) hN hθ hρ hinj hY hlin
  rw [sum_congr rfl fun r' hr' => heq r' hr' r hr, sum_const, card_treesOn hY] at hsum
  simp only [nsmul_eq_mul] at hsum
  push_cast at hsum
  linarith

end NMSC

end Phylogenetics
