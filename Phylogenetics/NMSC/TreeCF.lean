module

public import Phylogenetics.NMSC.Exchangeability

/-!
# The split of a fork has the largest concordance factor

Let `s = P|Q` be a quartet tree, and let the arcs `e`, `f` leave one vertex `w`, with `e` dominating
`P`, nothing of `Q` below `e`, a taxon `c` of `Q` below `f`, and the taxa of `Q` below `f` dominated
by `f`. The network may be arbitrary elsewhere: reticulations below `e` or `f`, or above `w`, do not
matter, nor do the lengths of hybrid arcs, nor `ρ`. Then `F(s) > F(r)` for the alternatives `r` of `s`.

The argument conditions at `e`, by the Markov property. A cherry `P` at the top of `e` decides `s`.
Otherwise the two lineages of `P` are at `w`, and conditioning at `f` brings there those of `Q` below
`f`. A cherry `Q` at the top of `f` decides `s` again. Otherwise at least three singleton lineages are at
`w`, the fourth being anywhere, and the three quartet trees are equally likely (`cherryMass_eq_third`).
So no outcome favours an alternative, and the cherry `P` at the top of `e` has positive probability,
since `e` is a tree arc, of positive length: if the lineages of `P` reach the bottom of `e` apart, they
coalesce on `e` with probability `1 - exp (-ℓ e)` (`kingmanTransition_singletons_cherry`).

The two shapes of a rooted quartet are covered together: in the caterpillar `(((a,b),c),d)`, `d` is not
below `f`; in the balanced tree `((a,b),(c,d))`, it is below `f`, and only there can `Q` be a cherry.

## Main results

* `kingmanTransition_singletons_cherry`: two lineages coalesce over a time `t` with probability `1 - exp (-t)`.
* `cherryMass_hubInj_eq_third`: at least three singleton lineages at one vertex give equal masses.
* `nmscCF_lt_of_fork`: the concordance factor of the split of a fork is strictly the largest.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

/-! ### Two lineages on an arc -/

section Kingman

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **Two lineages coalesce over a time `t` with probability `1 - exp (-t)`.** -/
theorem kingmanTransition_singletons_cherry {P : Finset L} (hP : #P = 2) (t : ℝ) :
    kingmanTransition t (P.image fun x => ({x} : Finset L))
      (insert P (P.image fun x => ({x} : Finset L))) = 1 - Real.exp (-t) := by
  set F : Finset (Finset L) := P.image fun x => ({x} : Finset L) with hF
  have hgood : IsGoodForest F := isGoodForest_singletons P
  have hlin : lineages F = P := lineages_image_singleton P
  have hcard1 : ∀ A ∈ F, #A = 1 := by
    intro A hA
    obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    exact card_singleton x
  have hPF : P ∉ F := fun h => by
    have := hcard1 P h
    omega
  have hne : F ≠ insert P F := fun h => hPF (h ▸ mem_insert_self P F)
  have hroots : roots F = F := by
    refine filter_true_of_mem fun A hA B hB hAB => ?_
    obtain ⟨x, -, rfl⟩ := mem_image.1 hA
    obtain ⟨y, -, rfl⟩ := mem_image.1 hB
    rw [singleton_subset_singleton] at hAB
    rw [hAB]
  have hcardF : #(roots F) = 2 := by
    rw [hroots, hF, card_image_of_injective _ singleton_injective, hP]
  have hsupp : ∀ G, G ≠ F → G ≠ insert P F → kingmanTransition t F G = 0 := by
    intro G hGF hGi
    by_contra hG
    obtain ⟨hgG, hsub, hlG⟩ := kingmanTransition_support_good hgood hG
    rw [hlin] at hlG
    by_cases h2 : ∃ C ∈ G, #C = 2
    · obtain ⟨C, hC, hC2⟩ := h2
      have hCP : C = P := eq_of_subset_of_card_le
        (fun x hx => hlG ▸ mem_lineages.2 ⟨C, hC, hx⟩) (by rw [hP, hC2])
      refine hGi (Subset.antisymm (fun A hA => ?_) (insert_subset (hCP ▸ hC) hsub))
      have hAP : A ⊆ P := fun x hx => hlG ▸ mem_lineages.2 ⟨A, hA, hx⟩
      by_cases hAc : #A = 2
      · rw [eq_of_subset_of_card_le hAP (by rw [hP, hAc])]
        exact mem_insert_self _ _
      · have hApos := (hgG.1.1 A hA).card_pos
        have hle := card_le_card hAP
        obtain ⟨x, rfl⟩ := card_eq_one.1 (by omega : #A = 1)
        refine mem_insert_of_mem (mem_image.2 ⟨x, ?_, rfl⟩)
        exact hAP (mem_singleton_self x)
    · have := hgG.eq_singletons h2
      rw [hlG] at this
      exact hGF this
  have hsum := kingmanTransition_sum hgood.1 t
  rw [sum_eq_add F (insert P F) hne (fun G _ hG => hsupp G hG.1 hG.2)
    (fun h => absurd (mem_univ _) h) (fun h => absurd (mem_univ _) h),
    kingmanTransition_apply_self hgood.1, hcardF] at hsum
  norm_num at hsum
  linarith

end Kingman

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-! ### Arcs dominating a taxon -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc dominating a taxon is the only arc entering its target. -/
theorem eq_of_target_eq_of_dominates (hN : N.IsPhylogenetic) {e g : E} {x : X}
    (hd : N.Dominates e x) (ht : N.graph.target g = N.graph.target e) : g = e := by
  by_contra hne
  have h1 : N.AvoidingReach e N.root (N.graph.source g) := by
    by_contra hn
    have := target_reaches_of_not_avoidingReach (hN.root_reaches _) hn
    rw [← ht] at this
    exact not_reaches_target_source hN.acyclic g this
  have h3 : N.AvoidingReach e (N.graph.target g) (N.leaf x) :=
    avoidingReach_of_target_reaches hN.acyclic (ht ▸ .refl) (ht ▸ hd.isBelow hN)
  exact hd ((h1.tail ⟨g, hne, rfl, rfl⟩).trans h3)

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- An arc dominating a taxon is a tree arc. -/
theorem isTreeArc_of_dominates (hN : N.IsPhylogenetic) {e : E} {x : X} (hd : N.Dominates e x) :
    N.IsTreeArc e := by
  unfold RootedNetwork.IsTreeArc
  rw [indegree_eq_card, card_eq_one]
  refine ⟨e, ?_⟩
  ext g
  rw [mem_arcsInto, mem_singleton]
  exact ⟨fun h => eq_of_target_eq_of_dominates hN hd h, fun h => h ▸ rfl⟩

/-! ### Singleton lineages at one vertex -/

omit [Fintype E] in
/-- Lifting singleton lineages along an arc leaving the hub moves them to the hub. -/
theorem liftInj_hubInj (hN : N.IsPhylogenetic) {q T L : Finset X} {v : V} {f : E}
    (hs : N.graph.source f = v) (hL : ∀ x ∈ L, N.IsBelow f x)
    (hrest : ∀ x ∈ q, x ∉ T → x ∉ L → ¬ N.IsBelow f x) :
    liftInj N f (hubInj N q T v) (L.image fun x => ({x} : Finset X)) = hubInj N q (T ∪ L) v := by
  funext u
  by_cases hu : u ∈ belowSet N f
  · rw [liftInj_of_mem hN hu]
    symm
    refine eq_empty_of_forall_notMem fun A hA => ?_
    have huv : u ≠ v := fun h => source_notMem_belowSet hN f (by rw [hs, ← h]; exact hu)
    unfold hubInj at hA
    rw [ite_eq_right huv, union_empty] at hA
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
    obtain ⟨hzq, rfl⟩ := (mem_filter.1 hz).2
    obtain ⟨hzq', hzT⟩ := mem_sdiff.1 hzq
    exact hrest z hzq' (fun h => hzT (mem_union_left _ h)) (fun h => hzT (mem_union_right _ h))
      (mem_belowSet.1 hu)
  · have hT : taxaInj N (q \ T) u = taxaInj N (q \ (T ∪ L)) u := by
      ext D
      simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨z, ⟨hz, hzu⟩, rfl⟩
        refine ⟨z, ⟨mem_sdiff.2 ⟨(mem_sdiff.1 hz).1, fun h => ?_⟩, hzu⟩, rfl⟩
        rcases mem_union.1 h with h | h
        · exact (mem_sdiff.1 hz).2 h
        · exact hu (hzu ▸ mem_belowSet.2 (hL z h))
      · rintro ⟨z, ⟨hz, hzu⟩, rfl⟩
        exact ⟨z, ⟨mem_sdiff.2 ⟨(mem_sdiff.1 hz).1,
          fun h => (mem_sdiff.1 hz).2 (mem_union_left _ h)⟩, hzu⟩, rfl⟩
    unfold liftInj hubInj
    rw [hs, hT, ite_eq_right hu]
    by_cases huv : u = v
    · simp only [huv, ↓reduceIte, image_union, union_assoc]
    · simp [huv]

/-- **At least three singleton lineages at one vertex**, the fourth being anywhere, make the three
quartet trees equally likely. -/
theorem cherryMass_hubInj_eq_third (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q T : Finset X} (hq : #q = 4) (hT : T ⊆ q) (v : V) {a : X} (ha : a ∈ q)
    (haT : ∀ x ∈ q, x ≠ a → x ∈ T) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (hubInj N q T v) r = 1 / 3 := by
  refine cherryMass_eq_third hN hθ hρ (validInj_hubInj q T v) hq (fun x => ?_) ha
    (fun x hx y hy hxa hya => ?_) hr
  · constructor
    · rintro ⟨u, hu⟩
      rcases (mem_lineages_hubInj x).1 hu with ⟨h, -⟩ | ⟨-, h⟩
      · exact (mem_sdiff.1 h).1
      · exact hT h
    · intro hx
      by_cases hxT : x ∈ T
      · exact ⟨v, (mem_lineages_hubInj x).2 (Or.inr ⟨rfl, hxT⟩)⟩
      · exact ⟨N.leaf x, (mem_lineages_hubInj x).2 (Or.inl ⟨mem_sdiff.2 ⟨hx, hxT⟩, rfl⟩)⟩
  · funext u
    unfold relabelInj hubInj
    rw [relabelFamily_union]
    congr 1
    · refine relabelFamily_taxaInj fun z hz _ => ?_
      have hza : z = a := by
        by_contra hza
        exact (mem_sdiff.1 hz).2 (haT z (mem_sdiff.1 hz).1 hza)
      rw [hza]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya)
    · split_ifs
      · exact relabelFamily_swap_singletons (haT x hx hxa) (haT y hy hya)
      · exact relabelFamily_empty _

/-! ### No outcome favours an alternative -/

omit [Fintype V] in
theorem prod_vertexWeight_nonneg (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (inj : V → Finset (Finset X)) (D : Finset V)
    (bot top : E → Finset (Finset X)) : 0 ≤ ∏ v ∈ D, vertexWeight N θ ρ inj v bot top :=
  prod_nonneg fun _ _ => mul_nonneg (allocationFactor_nonneg hθ hρ _ _ _)
    (prod_nonneg fun e _ => kingmanTransition_nonneg (length_nonneg hθ e) _ _)

/-- A cherry of `s` among the injected forests decides the quartet trees on the taxa of `s`. -/
theorem cherryMass_of_mem_val (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {v : V} {s r : QuartetTree X}
    {C : Finset X} (hC : C ∈ inj v) (hCs : C ∈ s.val) (hr : r ∈ s.alternatives) :
    cherryMass N θ ρ inj r = 0 ∧ cherryMass N θ ρ inj s = 1 := by
  obtain ⟨hrt, hrs⟩ := QuartetTree.mem_alternatives.1 hr
  have hC2 := s.card_of_mem hCs
  have hCt := s.subset_taxa hCs
  refine ⟨?_, ?_⟩
  · rw [cherryMass_of_mem hN hθ hρ hinj hC hC2 (hrt ▸ hCt), ite_eq_right]
    exact fun hCr => hrs (QuartetTree.eq_of_taxa_eq_of_mem hrt hCr hCs)
  · rw [cherryMass_of_mem hN hθ hρ hinj hC hC2 hCt, ite_eq_left hCs]

/-- With the lineages of the cherry `P` at the hub, conditioning at the second arc `f` of the fork. -/
theorem cherryMass_hubInj_le (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {v : V} {f : E}
    (hs : N.graph.source f = v) {c : X} (hcq : c ∈ s.taxa) (hcP : c ∉ P) (hcf : N.IsBelow f c)
    (hdf : ∀ x ∈ s.taxa, x ∉ P → N.IsBelow f x → N.Dominates f x) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) :
    cherryMass N θ ρ (hubInj N s.taxa P v) r ≤ cherryMass N θ ρ (hubInj N s.taxa P v) s := by
  have hv := validInj_hubInj (N := N) s.taxa P v
  have hvB : ∀ u ∈ belowSet N f, u ≠ v := fun u hu h =>
    source_notMem_belowSet hN f (by rw [hs, ← h]; exact hu)
  have hdom : DominatedInj N f (hubInj N s.taxa P v) := by
    rintro u hu ⟨A, hA⟩
    obtain ⟨z, hz⟩ := (validInj_hubInj (N := N) s.taxa P v).good u |>.1.1 A hA
    rcases (mem_lineages_hubInj z).1 (mem_lineages.2 ⟨A, hA, hz⟩) with ⟨hzq, rfl⟩ | ⟨h, -⟩
    · exact hdf z (mem_sdiff.1 hzq).1 (mem_sdiff.1 hzq).2 (mem_belowSet.1 hu)
    · exact absurd h (hvB u hu)
  -- the lineages at the top of `f`
  have hbel : ∀ x, (∃ u ∈ belowSet N f, x ∈ lineages (hubInj N s.taxa P v u)) ↔
      x ∈ s.taxa ∧ x ∉ P ∧ N.IsBelow f x := by
    intro x
    constructor
    · rintro ⟨u, hu, hx⟩
      rcases (mem_lineages_hubInj x).1 hx with ⟨hzq, rfl⟩ | ⟨h, -⟩
      · exact ⟨(mem_sdiff.1 hzq).1, (mem_sdiff.1 hzq).2, mem_belowSet.1 hu⟩
      · exact absurd h (hvB u hu)
    · rintro ⟨hxq, hxP, hb⟩
      exact ⟨N.leaf x, mem_belowSet.2 hb,
        (mem_lineages_hubInj x).2 (Or.inl ⟨mem_sdiff.2 ⟨hxq, hxP⟩, rfl⟩)⟩
  have hpos := belowMass_pos (N := N) (X := X) f
  refine le_of_mul_le_mul_left ?_ hpos
  rw [belowMass_mul_cherryMass hN hθ hρ hv hdom r, belowMass_mul_cherryMass hN hθ hρ hv hdom s]
  refine sum_le_sum fun bot _ => sum_le_sum fun top _ => ?_
  by_cases hg : ∏ u ∈ belowSet N f, vertexWeight N θ ρ (hubInj N s.taxa P v) u bot top = 0
  · simp [hg]
  refine mul_le_mul_of_nonneg_left ?_ (prod_vertexWeight_nonneg hθ hρ _ _ _ _)
  have hgood := good_top_of_prod_ne_zero hN hv hg
  have hlin : ∀ x, x ∈ lineages (top f) ↔ x ∈ s.taxa ∧ x ∉ P ∧ N.IsBelow f x := fun x =>
    (lineages_top_of_prod_ne_zero hN hv hdom hg x).trans (hbel x)
  by_cases h2 : ∃ C ∈ top f, #C = 2
  · -- the other cherry at the top of `f` decides `s`
    obtain ⟨C, hC, hC2⟩ := h2
    have hQ := s.sdiff_mem hP
    have hCQ : C = s.taxa \ P := eq_of_subset_of_card_le
      (fun x hx => by
        obtain ⟨h1, h2, -⟩ := (hlin x).1 (mem_lineages.2 ⟨C, hC, hx⟩)
        exact mem_sdiff.2 ⟨h1, h2⟩)
      (by rw [s.card_of_mem hQ, hC2])
    have hl : ValidInj (liftInj N f (hubInj N s.taxa P v) (top f)) :=
      validInj_liftInj hv hgood fun x hx => (hbel x).2 ((hlin x).1 hx)
    have hmem : C ∈ liftInj N f (hubInj N s.taxa P v) (top f) (N.graph.source f) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hC)
    obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hθ hρ hl hmem (hCQ ▸ hQ) hr
    rw [h0, h1]
    exact zero_le_one
  · -- at least three singletons at the hub
    set L : Finset X := lineages (top f) with hLdef
    have hF : top f = L.image fun x => ({x} : Finset X) := hgood.eq_singletons h2
    have hlift := liftInj_hubInj (q := s.taxa) (T := P) hN hs
      (fun x hx => ((hlin x).1 hx).2.2) (fun x hxq hxP hxL hb => hxL ((hlin x).2 ⟨hxq, hxP, hb⟩))
    rw [hF, hlift]
    have hQ2 : #(s.taxa \ P) = 2 := s.card_of_mem (s.sdiff_mem hP)
    obtain ⟨a, ha, hac⟩ := exists_mem_ne (by omega : 1 < #(s.taxa \ P)) c
    have hTq : P ∪ L ⊆ s.taxa := union_subset (s.subset_taxa hP) fun x hx => ((hlin x).1 hx).1
    have haT : ∀ x ∈ s.taxa, x ≠ a → x ∈ P ∪ L := by
      intro x hx hxa
      by_cases hxP : x ∈ P
      · exact mem_union_left _ hxP
      · have hxc : x = c := by
          obtain ⟨u, w, huw, hQe⟩ := card_eq_two.1 hQ2
          have hx' : x ∈ s.taxa \ P := mem_sdiff.2 ⟨hx, hxP⟩
          have hc' : c ∈ s.taxa \ P := mem_sdiff.2 ⟨hcq, hcP⟩
          rw [hQe] at hx' hc' ha
          simp only [mem_insert, mem_singleton] at hx' hc' ha
          grind
        exact mem_union_right _ ((hlin x).2 ⟨hx, hxP, hxc ▸ hcf⟩)
    have haq : a ∈ s.taxa := (mem_sdiff.1 ha).1
    have hrq : r ∈ treesOn s.taxa := mem_treesOn.2 (QuartetTree.mem_alternatives.1 hr).1
    rw [cherryMass_hubInj_eq_third hN hθ hρ s.card_taxa hTq v haq haT hrq,
      cherryMass_hubInj_eq_third hN hθ hρ s.card_taxa hTq v haq haT (mem_treesOn.2 rfl)]

/-- The forest `F` of the lineages of the cherry `P` at the top of `e`: no outcome favours an
alternative. -/
theorem cherryMass_lift_le (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e f : E}
    (hs : N.graph.source f = N.graph.source e)
    (hbP : ∀ x ∈ P, N.IsBelow e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {c : X} (hcq : c ∈ s.taxa) (hcP : c ∉ P) (hcf : N.IsBelow f c)
    (hdf : ∀ x ∈ s.taxa, x ∉ P → N.IsBelow f x → N.Dominates f x)
    {F : Finset (Finset X)} (hgood : IsGoodForest F) (hlin : ∀ x, x ∈ lineages F ↔ x ∈ P)
    {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) F) r ≤
      cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) F) s := by
  by_cases h2 : ∃ C ∈ F, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCP : C = P := eq_of_subset_of_card_le
      (fun x hx => (hlin x).1 (mem_lineages.2 ⟨C, hC, hx⟩)) (by rw [s.card_of_mem hP, hC2])
    have hl : ValidInj (liftInj N e (taxaInj N s.taxa) F) :=
      validInj_liftInj (validInj_taxaInj _) hgood fun x hx => by
        have hxP := (hlin x).1 hx
        exact (exists_mem_below_taxaInj x).2 ⟨s.subset_taxa hP hxP, hbP x hxP⟩
    have hmem : C ∈ liftInj N e (taxaInj N s.taxa) F (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hC)
    obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hθ hρ hl hmem (hCP ▸ hP) hr
    rw [h0, h1]
    exact zero_le_one
  · have hF : F = P.image fun x => ({x} : Finset X) := by
      have := hgood.eq_singletons h2
      rwa [show lineages F = P from Finset.ext hlin] at this
    have hlift := liftInj_hubInj (q := s.taxa) (T := ∅) (L := P) (v := N.graph.source e) hN rfl hbP
      (fun x hxq _ hxP => hn x hxq hxP)
    rw [hubInj_empty, empty_union] at hlift
    rw [hF, hlift]
    exact cherryMass_hubInj_le hN hθ hρ s hP hs hcq hcP hcf hdf hr

/-! ### The cherry at the top of the arc has positive probability -/

/-- **A history in which the lineages of `P` have coalesced at the top of `e`**, of positive weight on
what is below `e`. Take any history of nonzero weight: if `P` is not a cluster at the top of `e`, the two
lineages traverse `e` without coalescing, and they can coalesce there since `e` has positive length. -/
theorem exists_history_cherry (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {Y P : Finset X} (hP2 : #P = 2) (hPY : P ⊆ Y) {e : E} (hd : ∀ x ∈ P, N.Dominates e x)
    (hn : ∀ x ∈ Y, x ∉ P → ¬ N.IsBelow e x) :
    ∃ bot top : E → Finset (Finset X),
      0 < ∏ u ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N Y) u bot top ∧ P ∈ top e := by
  have hv := validInj_taxaInj (N := N) Y
  have hxY : ∀ x ∈ Y, N.IsBelow e x → x ∈ P := fun x hx hb => by
    by_contra hxP
    exact hn x hx hxP hb
  have hdom : DominatedInj N e (taxaInj N Y) := dominatedInj_taxaInj fun x hx hb =>
    hd x (hxY x hx hb)
  -- a history of nonzero weight
  have hsum := sum_sum_below (θ := θ) (ρ := ρ) hN hθ hρ hv e
  have hne : ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      ∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N Y) v bot top ≠ 0 := by
    rw [hsum]
    exact (belowMass_pos e).ne'
  obtain ⟨bot, -, hbot⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨top, -, hg⟩ := exists_ne_zero_of_sum_ne_zero hbot
  have hnonneg : ∀ b t : E → Finset (Finset X),
      0 ≤ ∏ u ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N Y) u b t := fun b t =>
    prod_vertexWeight_nonneg hθ hρ _ _ _ _
  by_cases hPt : P ∈ top e
  · exact ⟨bot, top, lt_of_le_of_ne (hnonneg _ _) (Ne.symm hg), hPt⟩
  -- the forest at the top of `e` is the two singletons
  have hgood := good_top_of_prod_ne_zero hN hv hg
  have hlin : ∀ x, x ∈ lineages (top e) ↔ x ∈ P := fun x =>
    (lineages_top_of_prod_ne_zero hN hv hdom hg x).trans <|
      (exists_mem_below_taxaInj x).trans
        ⟨fun h => hxY x h.1 h.2, fun h => ⟨hPY h, (hd x h).isBelow hN⟩⟩
  have hno2 : ¬ ∃ C ∈ top e, #C = 2 := by
    rintro ⟨C, hC, hC2⟩
    apply hPt
    rwa [← eq_of_subset_of_card_le (fun x hx => (hlin x).1 (mem_lineages.2 ⟨C, hC, hx⟩))
      (by rw [hP2, hC2])]
  have hF : top e = P.image fun x => ({x} : Finset X) := by
    have := hgood.eq_singletons hno2
    rwa [show lineages (top e) = P from Finset.ext hlin] at this
  -- the factor of the target of `e`
  set v := N.graph.target e with hvdef
  have hvD : v ∈ belowSet N e := target_mem_belowSet e
  obtain ⟨x₀, hx₀⟩ : P.Nonempty := card_pos.1 (by omega)
  have htree : arcsInto N v = {e} := by
    ext g
    rw [mem_arcsInto, mem_singleton]
    exact ⟨fun h => eq_of_target_eq_of_dominates hN (hd x₀ hx₀) h, fun h => h ▸ rfl⟩
  rw [← mul_prod_erase _ _ hvD] at hg
  have hwv := left_ne_zero_of_mul hg
  have hrest := right_ne_zero_of_mul hg
  unfold vertexWeight at hwv
  rw [htree, prod_singleton] at hwv
  have halloc := left_ne_zero_of_mul hwv
  have hkin := right_ne_zero_of_mul hwv
  -- the forest at the bottom of `e` is the same
  have hFr := frontier_of_prod_ne_zero hN hv (downClosed_belowSet e)
    (show ∏ u ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N Y) u bot top ≠ 0 by
      rw [← mul_prod_erase _ _ hvD]
      exact hg)
  have hgb := hFr.good_bot e hvD
  obtain ⟨-, hsub, hlb⟩ := kingmanTransition_support_good hgb hkin
  have hbF : bot e = top e := by
    refine Subset.antisymm hsub fun A hA => ?_
    rw [hF] at hA
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
    have hxb : x ∈ lineages (bot e) := hlb ▸ (hlin x).2 hx
    obtain ⟨B, hB, hxB⟩ := mem_lineages.1 hxb
    exact hgb.singleton_mem hB hxB
  -- the history with the cherry at the top of `e`
  refine ⟨bot, Function.update top e (insert P (top e)), ?_, by simp⟩
  have hlen : 0 < θ.length e := hθ.1 e (isTreeArc_of_dominates hN (hd x₀ hx₀))
  have hsrc : ∀ g, N.graph.source g = v → g ≠ e := by
    rintro g hgv rfl
    exact source_ne_target hN g hgv
  have hu : ∀ u ∈ (belowSet N e).erase v,
      vertexWeight N θ ρ (taxaInj N Y) u bot (Function.update top e (insert P (top e))) =
        vertexWeight N θ ρ (taxaInj N Y) u bot top := by
    intro u hu
    have huv := ne_of_mem_erase hu
    have huB := mem_of_mem_erase hu
    refine vertexWeight_congr rfl (fun _ _ => rfl) (fun g hgu => ?_) (fun g hgu => ?_)
    · refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact huv hgu.symm
    · refine Function.update_of_ne ?_ _ _
      rintro rfl
      exact source_notMem_belowSet hN g (hgu ▸ huB)
  have hw₁ : vertexWeight N θ ρ (taxaInj N Y) v bot (Function.update top e (insert P (top e))) =
      allocationFactor N θ ρ (arriving N (taxaInj N Y) top v) v bot * (1 - Real.exp (-θ.length e)) := by
    unfold vertexWeight
    rw [htree, prod_singleton, Function.update_self, hbF, hF,
      kingmanTransition_singletons_cherry hP2,
      arriving_congr rfl fun g hgv => Function.update_of_ne (hsrc g hgv) _ _]
  rw [← mul_prod_erase _ _ hvD, hw₁, prod_congr rfl hu]
  have hpos1 : 0 < 1 - Real.exp (-θ.length e) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  have hpos2 : 0 < allocationFactor N θ ρ (arriving N (taxaInj N Y) top v) v bot :=
    lt_of_le_of_ne (allocationFactor_nonneg hθ hρ _ _ _) (Ne.symm halloc)
  have hpos3 : 0 < ∏ u ∈ (belowSet N e).erase v, vertexWeight N θ ρ (taxaInj N Y) u bot top :=
    lt_of_le_of_ne (prod_vertexWeight_nonneg hθ hρ _ _ _ _) (Ne.symm hrest)
  positivity

/-! ### The split of a fork -/

/-- **The split of a fork has the strictly largest concordance factor.** Let `e`, `f` be arcs with one
source, `e` dominating the cherry `P` of `s` with the other taxa of `s` not below it, a taxon `c` of
the other cherry below `f`, and all the taxa of the other cherry below `f` dominated by it. Then
`F(r) < F(s)` for the alternatives `r` of `s`, for any `0 ≤ ρ ≤ 1` and valid parameters. -/
theorem nmscCF_lt_of_fork (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e f : E}
    (hs : N.graph.source f = N.graph.source e)
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {c : X} (hcq : c ∈ s.taxa) (hcP : c ∉ P) (hcf : N.IsBelow f c)
    (hdf : ∀ x ∈ s.taxa, x ∉ P → N.IsBelow f x → N.Dominates f x)
    {r : QuartetTree X} (hr : r ∈ s.alternatives) : nmscCF N θ ρ r < nmscCF N θ ρ s := by
  rw [nmscCF_eq_cherryMass hN hθ hρ r, nmscCF_eq_cherryMass hN hθ hρ s,
    (QuartetTree.mem_alternatives.1 hr).1]
  have hv := validInj_taxaInj (N := N) s.taxa
  have hP2 := s.card_of_mem hP
  have hPq := s.subset_taxa hP
  have hxY : ∀ x ∈ s.taxa, N.IsBelow e x → x ∈ P := fun x hx hb => by
    by_contra hxP
    exact hn x hx hxP hb
  have hdom : DominatedInj N e (taxaInj N s.taxa) := dominatedInj_taxaInj fun x hx hb =>
    hd x (hxY x hx hb)
  have hbP : ∀ x ∈ P, N.IsBelow e x := fun x hx => (hd x hx).isBelow hN
  have hterm : ∀ bot top : E → Finset (Finset X),
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N s.taxa) v bot top) *
          cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top e)) r ≤
        (∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N s.taxa) v bot top) *
          cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top e)) s := by
    intro bot top
    by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N s.taxa) v bot top = 0
    · simp [hg]
    refine mul_le_mul_of_nonneg_left ?_ (prod_vertexWeight_nonneg hθ hρ _ _ _ _)
    refine cherryMass_lift_le hN hθ hρ s hP hs hbP hn hcq hcP hcf hdf
      (good_top_of_prod_ne_zero hN hv hg) (fun x => ?_) hr
    exact (lineages_top_of_prod_ne_zero hN hv hdom hg x).trans <|
      (exists_mem_below_taxaInj x).trans
        ⟨fun h => hxY x h.1 h.2, fun h => ⟨hPq h, hbP x h⟩⟩
  obtain ⟨bot₁, top₁, hw₁, hP₁⟩ := exists_history_cherry (θ := θ) (ρ := ρ) hN hθ hρ hP2 hPq hd hn
  have hstrict : (∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N s.taxa) v bot₁ top₁) *
        cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top₁ e)) r <
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ (taxaInj N s.taxa) v bot₁ top₁) *
        cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top₁ e)) s := by
    refine mul_lt_mul_of_pos_left ?_ hw₁
    have hg := hw₁.ne'
    have hl : ValidInj (liftInj N e (taxaInj N s.taxa) (top₁ e)) :=
      validInj_liftInj hv (good_top_of_prod_ne_zero hN hv hg) fun x hx =>
        (lineages_top_of_prod_ne_zero hN hv hdom hg x).1 hx
    have hmem : P ∈ liftInj N e (taxaInj N s.taxa) (top₁ e) (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hP₁)
    obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hθ hρ hl hmem hP hr
    rw [h0, h1]
    exact zero_lt_one
  have hpos := belowMass_pos (N := N) (X := X) e
  refine lt_of_mul_lt_mul_left ?_ hpos.le
  rw [belowMass_mul_cherryMass hN hθ hρ hv hdom r, belowMass_mul_cherryMass hN hθ hρ hv hdom s]
  refine sum_lt_sum (fun bot _ => sum_le_sum fun top _ => hterm bot top)
    ⟨bot₁, mem_univ _, sum_lt_sum (fun top _ => hterm bot₁ top) ⟨top₁, mem_univ _, hstrict⟩⟩

end NMSC

end Phylogenetics
