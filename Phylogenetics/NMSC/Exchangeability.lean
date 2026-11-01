module

public import Phylogenetics.NMSC.Factor

/-!
# Exchangeability and the forward facts of the network multispecies coalescent

The four-lineage analysis at a cut edge, from sampling consistency
(`Phylogenetics.NMSC.Marginal`), the Markov property at an arc
(`Phylogenetics.NMSC.Factor`) and the symmetry of the process
(`Phylogenetics.NMSC.Symmetry`).

* If the cut edge `e` has the taxon `a` below it and the three others not below it, a single lineage
  goes up to the source of `e`, and the process does not depend on which taxon it comes from.
* If the cut edge `e` has `b, c, d` below it and `a` not below it, the forest at the top of `e` does
  not depend on `a`. If it has a cherry, that decides the quartet tree; otherwise it has three
  singletons, and the three quartet trees are equally likely.

## Main results

* `exchangeability`: `CutExchangeable`, the exchangeability of Ané et al. (2024).
* `cut_alternatives`: on a cut-edge split of the induced network, the two alternatives have equal
  concordance factors.
* `trivial_uniform`: on a trivial 4-blob, all three concordance factors are `1/3`.

## References

* C. Ané, J. Fogg, E. S. Allman, H. Baños, J. A. Rhodes, *Anomalous networks under the multispecies
  coalescent: theory and prevalence*, J. Math. Biol. 88 (2024), 29.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-! ### Injected singletons and the arc -/

theorem cherryMass_congr {inj inj' : V → Finset (Finset X)}
    (h : ∀ G, injDist N θ ρ inj G = injDist N θ ρ inj' G) (r : QuartetTree X) :
    cherryMass N θ ρ inj r = cherryMass N θ ρ inj' r := by
  unfold cherryMass
  simp only [h]

omit [Fintype E] in
theorem dominatedInj_taxaInj {Y : Finset X} {e : E} (h : ∀ x ∈ Y, N.IsBelow e x → N.Dominates e x) :
    DominatedInj N e (taxaInj N Y) := by
  rintro u hu ⟨A, hA⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
  obtain ⟨hxY, rfl⟩ := (mem_filter.1 hx).2
  exact h x hxY (mem_belowSet.1 hu)

omit [Fintype E] in
theorem exists_mem_below_taxaInj {Y : Finset X} {e : E} (x : X) :
    (∃ u ∈ belowSet N e, x ∈ lineages (taxaInj N Y u)) ↔ x ∈ Y ∧ N.IsBelow e x := by
  constructor
  · rintro ⟨u, hu, hx⟩
    obtain ⟨hxY, rfl⟩ := mem_lineages_taxaInj.1 hx
    exact ⟨hxY, mem_belowSet.1 hu⟩
  · rintro ⟨hxY, hb⟩
    exact ⟨N.leaf x, mem_belowSet.2 hb, mem_lineages_taxaInj.2 ⟨hxY, rfl⟩⟩

omit [Fintype E] in
/-- The lineages after lifting the forest `F` of what is below `e`. -/
theorem lineages_lift_taxaInj {Y : Finset X} {e : E} {F : Finset (Finset X)}
    (hF : ∀ x, x ∈ lineages F ↔ x ∈ Y ∧ N.IsBelow e x) (x : X) :
    (∃ u, x ∈ lineages (liftInj N e (taxaInj N Y) F u)) ↔ x ∈ Y := by
  constructor
  · rintro ⟨u, hu⟩
    rcases (mem_lineages_liftInj x).1 hu with ⟨-, h⟩ | ⟨-, h⟩
    · exact (mem_lineages_taxaInj.1 h).1
    · exact ((hF x).1 h).1
  · intro hx
    by_cases hb : N.IsBelow e x
    · exact ⟨N.graph.source e, (mem_lineages_liftInj x).2 (Or.inr ⟨rfl, (hF x).2 ⟨hx, hb⟩⟩)⟩
    · exact ⟨N.leaf x, (mem_lineages_liftInj x).2
        (Or.inl ⟨fun h => hb (mem_belowSet.1 h), mem_lineages_taxaInj.2 ⟨hx, rfl⟩⟩)⟩

omit [Fintype X] in
theorem relabelFamily_eq_self {π : Equiv.Perm X} {F : Finset (Finset X)}
    (h : ∀ A ∈ F, A.map π.toEmbedding = A) : relabelFamily π F = F := by
  unfold relabelFamily
  conv_rhs => rw [← image_id (s := F)]
  exact image_congr fun A hA => h A hA

omit [Fintype E] [Fintype V] in
theorem relabelFamily_taxaInj {π : Equiv.Perm X} {Y : Finset X} {v : V}
    (h : ∀ z ∈ Y, N.leaf z = v → π z = z) : relabelFamily π (taxaInj N Y v) = taxaInj N Y v := by
  refine relabelFamily_eq_self fun A hA => ?_
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
  obtain ⟨hzY, hzv⟩ := (mem_filter.1 hz).2
  rw [map_singleton, Equiv.toEmbedding_apply, h z hzY hzv]

omit [Fintype E] in
/-- A permutation that fixes the lineages not below `e` and the forest `F` fixes what is injected
above `e`. -/
theorem relabelInj_lift_taxaInj {π : Equiv.Perm X} {Y : Finset X} {e : E}
    {F : Finset (Finset X)} (h : ∀ z ∈ Y, ¬ N.IsBelow e z → π z = z)
    (hF : relabelFamily π F = F) :
    relabelInj π (liftInj N e (taxaInj N Y) F) = liftInj N e (taxaInj N Y) F := by
  funext v
  unfold relabelInj liftInj
  rw [relabelFamily_union]
  congr 1
  · split_ifs with hv
    · exact relabelFamily_empty π
    · exact relabelFamily_taxaInj fun z hz hzv => h z hz fun hb => hv (hzv ▸ mem_belowSet.2 hb)
  · split_ifs
    · exact hF
    · exact relabelFamily_empty π

omit [Fintype X] in
/-- The transposition of two lineages of a forest of singletons fixes it. -/
theorem relabelFamily_swap_singletons {P : Finset X} {x y : X} (hx : x ∈ P) (hy : y ∈ P) :
    relabelFamily (Equiv.swap x y) (P.image fun z => ({z} : Finset X)) =
      P.image fun z => ({z} : Finset X) := by
  have hmem : ∀ z ∈ P, Equiv.swap x y z ∈ P := by
    intro z hz
    by_cases hzx : z = x
    · rw [hzx, Equiv.swap_apply_left]
      exact hy
    by_cases hzy : z = y
    · rw [hzy, Equiv.swap_apply_right]
      exact hx
    rwa [Equiv.swap_apply_of_ne_of_ne hzx hzy]
  ext D
  rw [mem_relabelFamily, mem_image, mem_image]
  constructor
  · rintro ⟨z, hz, hzD⟩
    refine ⟨Equiv.swap x y z, hmem z hz, ?_⟩
    ext w
    have h1 := Finset.ext_iff.1 hzD (Equiv.swap x y w)
    rw [mem_singleton, mem_map_equiv, Equiv.symm_symm, Equiv.swap_apply_self] at h1
    rw [mem_singleton, ← h1]
    exact ⟨fun h => by rw [h, Equiv.swap_apply_self], fun h => by rw [← h, Equiv.swap_apply_self]⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Equiv.swap x y z, hmem z hz, ?_⟩
    simp

/-! ### A cut edge with one taxon below it -/

/-- The first case of the four-lineage analysis: the taxon `a`, and also `a'`, are dominated by the
arc, and the three others are not below it. -/
private theorem exchange_case_one (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (s : QuartetTree X) {a a' : X} (ha : a ∈ s.taxa) (ha' : a' ∉ s.taxa)
    {e : E} (hda : N.Dominates e a) (hda' : N.Dominates e a')
    (hn : ∀ x ∈ s.taxa, x ≠ a → ¬ N.IsBelow e x) :
    cherryMass N θ ρ (taxaInj N s.taxa) s =
      cherryMass N θ ρ (taxaInj N (s.taxa.map (Equiv.swap a a').toEmbedding))
        (relabelQuartet (Equiv.swap a a') s) := by
  set π := Equiv.swap a a' with hπ
  set Y := s.taxa with hY
  set Y' := Y.map π.toEmbedding with hY'
  have hmem' : ∀ x, x ∈ Y' ↔ x = a' ∨ (x ∈ Y ∧ x ≠ a) := by
    intro x
    rw [hY', mem_map_equiv, hπ, Equiv.symm_swap]
    by_cases hxa : x = a
    · subst hxa
      have hne : x ≠ a' := fun h => ha' (h ▸ ha)
      simp [ha', hne]
    by_cases hxa' : x = a'
    · subst hxa'
      simp [ha]
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxa']
    simp [hxa, hxa']
  have hba := hda.isBelow hN
  have hba' := hda'.isBelow hN
  -- the lineages not below `e` are the same in both, and fixed
  have hnb' : ∀ x ∈ Y', x ≠ a' → ¬ N.IsBelow e x := by
    intro x hx hxa'
    obtain h | ⟨hxY, hxa⟩ := (hmem' x).1 hx
    · exact absurd h hxa'
    · exact hn x hxY hxa
  have hdom : DominatedInj N e (taxaInj N Y) := dominatedInj_taxaInj fun x hx hb => by
    by_cases hxa : x = a
    · exact hxa ▸ hda
    · exact absurd hb (hn x hx hxa)
  have hdom' : DominatedInj N e (taxaInj N Y') := dominatedInj_taxaInj fun x hx hb => by
    by_cases hxa : x = a'
    · exact hxa ▸ hda'
    · exact absurd hb (hnb' x hx hxa)
  have h₁ := injDist_eq_lift_singleton (θ := θ) (ρ := ρ) hN hθ hρ (validInj_taxaInj Y) hdom
    (y := a) ((exists_mem_below_taxaInj a).2 ⟨ha, hba⟩) (fun u hu x hx => by
      obtain ⟨hxY, hb⟩ := (exists_mem_below_taxaInj x).1 ⟨u, hu, hx⟩
      by_contra hxa
      exact hn x hxY hxa hb)
  have h₂ := injDist_eq_lift_singleton (θ := θ) (ρ := ρ) hN hθ hρ (validInj_taxaInj Y') hdom'
    (y := a') ((exists_mem_below_taxaInj a').2 ⟨(hmem' a').2 (Or.inl rfl), hba'⟩)
    (fun u hu x hx => by
      obtain ⟨hxY, hb⟩ := (exists_mem_below_taxaInj x).1 ⟨u, hu, hx⟩
      by_contra hxa
      exact hnb' x hxY hxa hb)
  have hrel : relabelInj π (liftInj N e (taxaInj N Y) {{a}}) =
      liftInj N e (taxaInj N Y') {{a'}} := by
    funext v
    unfold relabelInj liftInj
    rw [relabelFamily_union]
    congr 1
    · split_ifs with hv
      · exact relabelFamily_empty π
      · have hvb : ∀ z, N.leaf z = v → ¬ N.IsBelow e z := fun z hz hb =>
          hv (hz ▸ mem_belowSet.2 hb)
        rw [relabelFamily_taxaInj]
        · ext D
          simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨z, ⟨hzY, hzv⟩, rfl⟩
            refine ⟨z, ⟨(hmem' z).2 (Or.inr ⟨hzY, ?_⟩), hzv⟩, rfl⟩
            rintro rfl
            exact hvb _ hzv hba
          · rintro ⟨z, ⟨hzY, hzv⟩, rfl⟩
            obtain h | ⟨hzY', -⟩ := (hmem' z).1 hzY
            · subst h
              exact absurd hba' (hvb _ hzv)
            · exact ⟨z, ⟨hzY', hzv⟩, rfl⟩
        · intro z hz hzv
          have hza : z ≠ a := by
            rintro rfl
            exact hvb _ hzv hba
          have hza' : z ≠ a' := by
            rintro rfl
            exact ha' hz
          exact Equiv.swap_apply_of_ne_of_ne hza hza'
    · split_ifs
      · simp [relabelFamily, hπ]
      · exact relabelFamily_empty π
  rw [cherryMass_congr h₁, cherryMass_congr h₂, ← hrel, cherryMass_relabel]

/-! ### A cut edge with three taxa below it -/

omit [Fintype X] in
/-- The cherries of a quartet tree after replacing a taxon: a cluster avoiding the two taxa. -/
private theorem mem_relabelQuartet_swap_iff (s : QuartetTree X) {a a' : X} {C : Finset X}
    (hCa : a ∉ C) (hCa' : a' ∉ C) :
    C ∈ (relabelQuartet (Equiv.swap a a') s).val ↔ C ∈ s.val := by
  have hC : C.map (Equiv.swap a a').toEmbedding = C := by
    ext z
    rw [mem_map_equiv, Equiv.symm_swap]
    by_cases hza : z = a
    · subst hza
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => absurd h hCa', fun h => absurd h hCa⟩
    by_cases hza' : z = a'
    · subst hza'
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hCa, fun h => absurd h hCa'⟩
    rw [Equiv.swap_apply_of_ne_of_ne hza hza']
  conv_lhs => rw [← hC]
  exact map_mem_relabelFamily

/-- The second case of the four-lineage analysis: the three taxa other than `a` are dominated by the
arc, and `a`, `a'` are not below it. -/
private theorem exchange_case_two (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (s : QuartetTree X) {a a' : X} (ha : a ∈ s.taxa) (ha' : a' ∉ s.taxa)
    {e : E} (hna : ¬ N.IsBelow e a) (hna' : ¬ N.IsBelow e a')
    (hd : ∀ x ∈ s.taxa, x ≠ a → N.Dominates e x) :
    cherryMass N θ ρ (taxaInj N s.taxa) s =
      cherryMass N θ ρ (taxaInj N (s.taxa.map (Equiv.swap a a').toEmbedding))
        (relabelQuartet (Equiv.swap a a') s) := by
  set π := Equiv.swap a a' with hπ
  set Y := s.taxa with hY
  set Y' := Y.map π.toEmbedding with hY'
  have hmem' : ∀ x, x ∈ Y' ↔ x = a' ∨ (x ∈ Y ∧ x ≠ a) := by
    intro x
    rw [hY', mem_map_equiv, hπ, Equiv.symm_swap]
    by_cases hxa : x = a
    · subst hxa
      have hne : x ≠ a' := fun h => ha' (h ▸ ha)
      simp [ha', hne]
    by_cases hxa' : x = a'
    · subst hxa'
      simp [ha]
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxa']
    simp [hxa, hxa']
  have hbel : ∀ x, N.IsBelow e x → (x ∈ Y ↔ x ∈ Y') := by
    intro x hb
    have hxa : x ≠ a := fun h => hna (h ▸ hb)
    have hxa' : x ≠ a' := fun h => hna' (h ▸ hb)
    rw [hmem']
    simp [hxa, hxa']
  have hdY : ∀ x ∈ Y, N.IsBelow e x → N.Dominates e x := fun x hx hb =>
    hd x hx fun h => hna (h ▸ hb)
  have hdY' : ∀ x ∈ Y', N.IsBelow e x → N.Dominates e x := fun x hx hb =>
    hdY x ((hbel x hb).2 hx) hb
  have hdom := dominatedInj_taxaInj (N := N) hdY
  have hdom' := dominatedInj_taxaInj (N := N) hdY'
  have hB : ∀ u ∈ belowSet N e, taxaInj N Y u = taxaInj N Y' u := by
    intro u hu
    ext D
    simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨z, ⟨hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨(hbel z (mem_belowSet.1 hu)).1 hz, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨(hbel z (mem_belowSet.1 hu)).2 hz, rfl⟩, rfl⟩
  refine cherryMass_eq_of_lift hN hθ hρ (validInj_taxaInj Y) (validInj_taxaInj Y') hdom hdom' hB
    fun bot top hg => ?_
  have hgood := good_top_of_prod_ne_zero hN (validInj_taxaInj Y) hg
  have hlinF : ∀ x, x ∈ lineages (top e) ↔ x ∈ Y ∧ N.IsBelow e x := fun x =>
    (lineages_top_of_prod_ne_zero hN (validInj_taxaInj Y) hdom hg x).trans
      (exists_mem_below_taxaInj x)
  have hlinF' : ∀ x, x ∈ lineages (top e) ↔ x ∈ Y' ∧ N.IsBelow e x := fun x => by
    rw [hlinF]
    exact ⟨fun h => ⟨(hbel x h.2).1 h.1, h.2⟩, fun h => ⟨(hbel x h.2).2 h.1, h.2⟩⟩
  have hl₁ : ValidInj (liftInj N e (taxaInj N Y) (top e)) :=
    validInj_liftInj (validInj_taxaInj Y) hgood fun x hx =>
      (exists_mem_below_taxaInj x).2 ((hlinF x).1 hx)
  have hl₂ : ValidInj (liftInj N e (taxaInj N Y') (top e)) :=
    validInj_liftInj (validInj_taxaInj Y') hgood fun x hx =>
      (exists_mem_below_taxaInj x).2 ((hlinF' x).1 hx)
  have hmemlift : ∀ (Z : Finset X) {C : Finset X}, C ∈ top e →
      C ∈ liftInj N e (taxaInj N Z) (top e) (N.graph.source e) := fun Z C hC => by
    unfold liftInj
    exact mem_union_right _ (by simpa using hC)
  by_cases h2 : ∃ C ∈ top e, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCl : ∀ x ∈ C, x ∈ Y ∧ N.IsBelow e x := fun x hx =>
      (hlinF x).1 (mem_lineages.2 ⟨C, hC, hx⟩)
    have hCa : a ∉ C := fun h => hna (hCl a h).2
    have hCa' : a' ∉ C := fun h => hna' (hCl a' h).2
    have hCY : C ⊆ s.taxa := fun x hx => (hCl x hx).1
    have hCY' : C ⊆ (relabelQuartet π s).taxa := by
      rw [taxa_relabelQuartet]
      exact fun x hx => (hbel x (hCl x hx).2).1 (hCl x hx).1
    rw [cherryMass_of_mem hN hθ hρ hl₁ (hmemlift Y hC) hC2 hCY,
      cherryMass_of_mem hN hθ hρ hl₂ (hmemlift Y' hC) hC2 hCY']
    simp only [hπ, mem_relabelQuartet_swap_iff s hCa hCa']
  · have hF := hgood.eq_singletons h2
    have hYcard : #Y = 4 := s.card_taxa
    have hY'card : #Y' = 4 := by rw [hY', card_map]; exact hYcard
    have hthird₁ := cherryMass_eq_third (θ := θ) (ρ := ρ) hN hθ hρ hl₁ hYcard
      (lineages_lift_taxaInj hlinF) ha (fun x hx y hy hxa hya =>
        relabelInj_lift_taxaInj (fun z hz hzb => by
          have hza : z = a := by
            by_contra hza
            exact hzb ((hd z hz hza).isBelow hN)
          rw [hza]
          exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya))
          (by
            rw [hF]
            exact relabelFamily_swap_singletons
              ((hlinF x).2 ⟨hx, (hd x hx hxa).isBelow hN⟩)
              ((hlinF y).2 ⟨hy, (hd y hy hya).isBelow hN⟩)))
      (r := s) (mem_treesOn.2 rfl)
    have ha'Y' : a' ∈ Y' := (hmem' a').2 (Or.inl rfl)
    have hthird₂ := cherryMass_eq_third (θ := θ) (ρ := ρ) hN hθ hρ hl₂ hY'card
      (lineages_lift_taxaInj hlinF') ha'Y' (fun x hx y hy hxa hya =>
        relabelInj_lift_taxaInj (fun z hz hzb => by
          have hza : z = a' := by
            by_contra hza
            obtain h | ⟨hzY, hzn⟩ := (hmem' z).1 hz
            · exact hza h
            · exact hzb ((hd z hzY hzn).isBelow hN)
          rw [hza]
          exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya))
          (by
            obtain hxY := ((hmem' x).1 hx).resolve_left hxa
            obtain hyY := ((hmem' y).1 hy).resolve_left hya
            have hbx := (hd x hxY.1 hxY.2).isBelow hN
            have hby := (hd y hyY.1 hyY.2).isBelow hN
            rw [hF]
            exact relabelFamily_swap_singletons ((hlinF x).2 ⟨hxY.1, hbx⟩)
              ((hlinF y).2 ⟨hyY.1, hby⟩)))
      (r := relabelQuartet π s) (mem_treesOn.2 (taxa_relabelQuartet π s))
    rw [hthird₁, hthird₂]

/-! ### Exchangeability -/

omit [Fintype X] in
/-- The replacement of a taxon in a quartet tree is the relabelling by a transposition. -/
private theorem eq_relabelQuartet_swap {s s' : QuartetTree X} {a a' : X} (ha' : a' ∉ s.taxa)
    (hs' : s'.val = s.val.image (fun B => if a ∈ B then insert a' (B.erase a) else B)) :
    s' = relabelQuartet (Equiv.swap a a') s := by
  refine Subtype.ext ?_
  rw [hs']
  change _ = relabelFamily _ _
  unfold relabelFamily
  refine image_congr fun B hB => ?_
  have hB' : a' ∉ B := fun h => ha' (s.subset_taxa hB h)
  change (if a ∈ B then insert a' (B.erase a) else B) = _
  ext z
  rw [mem_map_equiv, Equiv.symm_swap]
  by_cases hza : z = a
  · subst hza
    rw [Equiv.swap_apply_left]
    split_ifs with h
    · have hne : z ≠ a' := fun h' => hB' (h' ▸ h)
      simp [hB', hne]
    · simp [h, hB']
  by_cases hza' : z = a'
  · subst hza'
    rw [Equiv.swap_apply_right]
    split_ifs with h
    · simp [h]
    · simp [h, hB']
  rw [Equiv.swap_apply_of_ne_of_ne hza hza']
  split_ifs with h
  · simp [hza, hza']
  · rfl

/-- **Exchangeability of the network multispecies coalescent** (Ané et al. 2024): concordance factors do not change when a taxon of a quartet
tree is replaced by one that a cut edge groups with it, away from the other three taxa. -/
theorem exchangeability (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) :
    CutExchangeable N (nmscCF N θ ρ) := by
  rintro s s' a a' ha ha' hs' ⟨A, hA, haA, ha'A, hdis⟩
  have hs'eq := eq_relabelQuartet_swap ha' hs'
  rw [nmscCF_eq_cherryMass hN hθ hρ s, nmscCF_eq_cherryMass hN hθ hρ s', hs'eq,
    taxa_relabelQuartet]
  have hnotA : ∀ x ∈ s.taxa, x ≠ a → x ∉ A := fun x hx hxa hxA =>
    disjoint_left.1 hdis hxA (mem_erase.2 ⟨hxa, hx⟩)
  obtain ⟨e, ⟨-, hd, hn⟩ | ⟨-, hd, hn⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).1
    ((hasCutSplit_iff_hasCutSplitOn_univ hN _).1 hA)
  · exact exchange_case_one hN hθ hρ s ha ha' (hd a ⟨Set.mem_univ _, haA⟩)
      (hd a' ⟨Set.mem_univ _, ha'A⟩)
      fun x hx hxa => hn x ⟨Set.mem_univ _, hnotA x hx hxa⟩
  · exact exchange_case_two hN hθ hρ s ha ha' (hn a ⟨Set.mem_univ _, haA⟩)
      (hn a' ⟨Set.mem_univ _, ha'A⟩)
      fun x hx hxa => hd x ⟨Set.mem_univ _, hnotA x hx hxa⟩

/-! ### The alternatives of a cut-edge split -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
private theorem eq_of_mem_of_card_two {α : Type*} [DecidableEq α] {S : Finset α} (hS : #S = 2)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hca : c ≠ a) : c = b := by
  obtain ⟨u, v, -, rfl⟩ := card_eq_two.1 hS
  simp only [mem_insert, mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first
    | rfl
    | exact absurd rfl hab
    | exact absurd rfl hca

/-- The analysis at a cut edge dominating the cherry `P`, the other cherry not being below it. -/
private theorem cut_alternatives_aux (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {r r' : QuartetTree X} (hr : r ∈ s.alternatives) (hr' : r' ∈ s.alternatives) :
    cherryMass N θ ρ (taxaInj N s.taxa) r = cherryMass N θ ρ (taxaInj N s.taxa) r' := by
  have hxP : ∀ x ∈ s.taxa, N.IsBelow e x → x ∈ P := fun x hx hb => by
    by_contra hxP
    exact hn x hx hxP hb
  have hdom : DominatedInj N e (taxaInj N s.taxa) := dominatedInj_taxaInj fun x hx hb =>
    hd x (hxP x hx hb)
  have hv := validInj_taxaInj (N := N) s.taxa
  refine cherryMass_eq_of_lift hN hθ hρ hv hv hdom hdom (fun _ _ => rfl) fun bot top hg => ?_
  have hgood := good_top_of_prod_ne_zero hN hv hg
  have hlinF : ∀ x, x ∈ lineages (top e) ↔ x ∈ s.taxa ∧ N.IsBelow e x := fun x =>
    (lineages_top_of_prod_ne_zero hN hv hdom hg x).trans (exists_mem_below_taxaInj x)
  have hlinP : ∀ x, x ∈ lineages (top e) ↔ x ∈ P := fun x => by
    rw [hlinF]
    exact ⟨fun h => hxP x h.1 h.2, fun h => ⟨s.subset_taxa hP h, (hd x h).isBelow hN⟩⟩
  have hl : ValidInj (liftInj N e (taxaInj N s.taxa) (top e)) :=
    validInj_liftInj hv hgood fun x hx => (exists_mem_below_taxaInj x).2 ((hlinF x).1 hx)
  have hrP : ∀ w ∈ s.alternatives, P ∉ w.val := fun w hw hPw => by
    obtain ⟨hwt, hwne⟩ := QuartetTree.mem_alternatives.1 hw
    exact hwne (QuartetTree.eq_of_taxa_eq_of_mem hwt hPw hP)
  by_cases h2 : ∃ C ∈ top e, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCP : C = P := eq_of_subset_of_card_le
      (fun x hx => (hlinP x).1 (mem_lineages.2 ⟨C, hC, hx⟩)) (by rw [s.card_of_mem hP, hC2])
    subst hCP
    have hmem : C ∈ liftInj N e (taxaInj N s.taxa) (top e) (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hC)
    have hval : ∀ w ∈ s.alternatives,
        cherryMass N θ ρ (liftInj N e (taxaInj N s.taxa) (top e)) w = 0 := fun w hw => by
      have hCw : C ⊆ w.taxa := by
        rw [(QuartetTree.mem_alternatives.1 hw).1]
        exact s.subset_taxa hP
      rw [cherryMass_of_mem hN hθ hρ hl hmem hC2 hCw, ite_eq_right (hrP w hw)]
    rw [hval r hr, hval r' hr']
  · by_cases hrr : r = r'
    · rw [hrr]
    have hF := hgood.eq_singletons h2
    obtain ⟨x, y, hxy, hPxy⟩ := card_eq_two.1 (s.card_of_mem hP)
    have hxP' : x ∈ P := by simp [hPxy]
    have hyP' : y ∈ P := by simp [hPxy]
    set π := Equiv.swap x y with hπ
    have hsym : relabelInj π (liftInj N e (taxaInj N s.taxa) (top e)) =
        liftInj N e (taxaInj N s.taxa) (top e) := by
      refine relabelInj_lift_taxaInj (fun z hz hzb => ?_) ?_
      · have hzP : z ∉ P := fun h => hzb ((hd z h).isBelow hN)
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hzP (h ▸ hxP')) (fun h => hzP (h ▸ hyP'))
      · rw [hF]
        exact relabelFamily_swap_singletons ((hlinP x).2 hxP') ((hlinP y).2 hyP')
    have hmapP : P.map π.symm.toEmbedding = P := by
      rw [hPxy, hπ, Equiv.symm_swap, map_insert, map_singleton]
      simp [pair_comm]
    obtain ⟨hrt, hrne⟩ := QuartetTree.mem_alternatives.1 hr
    have hπr : relabelQuartet π r = r' := by
      have hmem : relabelQuartet π r ∈ s.alternatives := by
        refine QuartetTree.mem_alternatives.2 ⟨?_, fun h => hrP r hr ?_⟩
        · rw [taxa_relabelQuartet, hrt]
          ext z
          rw [mem_map_equiv, hπ, Equiv.symm_swap]
          have hxY := s.subset_taxa hP hxP'
          have hyY := s.subset_taxa hP hyP'
          by_cases hzx : z = x
          · subst hzx
            simp [hxY, hyY]
          by_cases hzy : z = y
          · subst hzy
            simp [hxY, hyY]
          rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
        · have : P ∈ (relabelQuartet π r).val := h ▸ hP
          have h' := mem_relabelFamily.1 this
          rwa [hmapP] at h'
      have hne : relabelQuartet π r ≠ r := by
        intro h
        obtain ⟨D, hD, hxD⟩ := exists_cherry_mem r (hrt ▸ s.subset_taxa hP hxP')
        have hyD : y ∉ D := fun hyD => hrP r hr (by
          have hsub : P ⊆ D := by
            rw [hPxy]
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          rwa [eq_of_subset_of_card_le hsub (by rw [r.card_of_mem hD, s.card_of_mem hP])] )
        obtain ⟨p, hpD, hpx⟩ := exists_mem_ne (by rw [r.card_of_mem hD]; omega : 1 < #D) x
        have hpy : p ≠ y := fun hpy => hyD (hpy ▸ hpD)
        have hDm : D.map π.toEmbedding ∈ r.val := by
          have : D.map π.toEmbedding ∈ (relabelQuartet π r).val := mem_image_of_mem _ hD
          rwa [h] at this
        have hne' : D.map π.toEmbedding ≠ D := by
          intro hmapD
          have : y ∈ D.map π.toEmbedding := by
            refine mem_map.2 ⟨x, hxD, ?_⟩
            simp [hπ]
          exact hyD (hmapD ▸ this)
        have hdisj := r.property.2.2 _ hDm D hD hne'
        have hpm : p ∈ D.map π.toEmbedding := by
          refine mem_map.2 ⟨p, hpD, ?_⟩
          simpa [hπ] using Equiv.swap_apply_of_ne_of_ne hpx hpy
        exact disjoint_left.1 hdisj hpm hpD
      exact eq_of_mem_of_card_two s.card_alternatives hr hr' hmem hrr hne
    rw [← hπr]
    conv_rhs => rw [← hsym]
    exact (cherryMass_relabel π _ r).symm

/-- On a cut-edge split of the network induced on the taxa of `s`, the two alternatives of `s` have
equal concordance factors. -/
theorem cut_alternatives (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) (hs : InducedCutSplit N s) :
    ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, nmscCF N θ ρ r = nmscCF N θ ρ r' := by
  intro r hr r' hr'
  rw [nmscCF_eq_cherryMass hN hθ hρ r, nmscCF_eq_cherryMass hN hθ hρ r',
    (QuartetTree.mem_alternatives.1 hr).1, (QuartetTree.mem_alternatives.1 hr').1]
  obtain ⟨B, hB, hcut⟩ := hs
  have hc : ∀ x, x ∈ s.taxa ∧ x ∉ B ↔ x ∈ s.taxa \ B := fun x => by simp
  obtain ⟨e, ⟨-, hd, hn⟩ | ⟨-, hd, hn⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).1 hcut
  · refine cut_alternatives_aux hN hθ hρ s hB (e := e) (fun x hx => hd x ?_)
      (fun x hx hxB => hn x ⟨hx, hxB⟩) hr hr'
    exact ⟨s.subset_taxa hB hx, hx⟩
  · refine cut_alternatives_aux hN hθ hρ s (s.sdiff_mem hB) (e := e)
      (fun x hx => hd x ⟨(mem_sdiff.1 hx).1, (mem_sdiff.1 hx).2⟩)
      (fun x hx hxB => hn x ⟨hx, ?_⟩) hr hr'
    by_contra hxn
    exact hxB (mem_sdiff.2 ⟨hx, hxn⟩)

/-! ### Trivial 4-blobs -/

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc at the hub of a trivial 4-blob: either it leaves the hub, and separates its taxon from
the rest, or it enters the hub, with its taxon on the side of its source. -/
private theorem blob_arc (hN : N.IsPhylogenetic) {q : Finset X} {v : V} {x : X} {e : E}
    (he : e ∈ N.ancestralArcs (q : Set X)) {S : Set V}
    (hS : ∀ f ∈ N.ancestralArcs (q : Set X), N.graph.Crosses f S ↔ f = e)
    (hleaf : ∀ y ∈ q, N.leaf y ∈ S ↔ y = x) (hv : v ∉ S)
    (hev : N.graph.source e = v ∨ N.graph.target e = v) (hx : x ∈ q) :
    (N.graph.source e = v ∧ N.Dominates e x ∧ ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y) ∨
      (N.graph.target e = v ∧ ¬ N.IsBelow e x ∧ ∀ y ∈ q, y ≠ x → N.Dominates e y) := by
  rcases (hS e he).2 rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · right
    have hT : ∀ f ∈ N.ancestralArcs (q : Set X), f ≠ e → ¬ N.graph.Crosses f Sᶜ :=
      fun f hf hfe hc => hfe ((hS f hf).1 ((N.graph.crosses_compl f S).1 hc))
    obtain ⟨-, hdom, hnb⟩ := separates_of_crossing hN he hT ht (not_not.2 hs)
    refine ⟨?_, hnb x hx (not_not.2 ((hleaf x hx).2 rfl)), fun y hy hyx =>
      hdom y hy fun h => hyx ((hleaf y hy).1 h)⟩
    rcases hev with h | h
    · exact absurd (h ▸ hs) hv
    · exact h
  · left
    have hT : ∀ f ∈ N.ancestralArcs (q : Set X), f ≠ e → ¬ N.graph.Crosses f S := fun f hf hfe hc =>
      hfe ((hS f hf).1 hc)
    obtain ⟨-, hdom, hnb⟩ := separates_of_crossing hN he hT ht hs
    refine ⟨?_, hdom x hx ((hleaf x hx).2 rfl), fun y hy hyx =>
      hnb y hy fun h => hyx ((hleaf y hy).1 h)⟩
    rcases hev with h | h
    · exact h
    · exact absurd (h ▸ ht) hv

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc dominating a taxon is the only arc entering its target. -/
private theorem eq_of_dominates_of_target_eq (hN : N.IsPhylogenetic) {e₀ e' : E} {x : X}
    (hd : N.Dominates e₀ x) (ht : N.graph.target e' = N.graph.target e₀) : e' = e₀ := by
  by_contra hne
  have h1 : N.AvoidingReach e₀ N.root (N.graph.source e') := by
    by_contra hn
    have := target_reaches_of_not_avoidingReach (hN.root_reaches _) hn
    rw [← ht] at this
    exact not_reaches_target_source hN.acyclic e' this
  have h3 : N.AvoidingReach e₀ (N.graph.target e') (N.leaf x) :=
    avoidingReach_of_target_reaches hN.acyclic (ht ▸ .refl) (ht ▸ hd.isBelow hN)
  exact hd ((h1.tail ⟨e', hne, rfl, rfl⟩).trans h3)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- At the hub of a trivial 4-blob, at most one taxon is not on an arc leaving the hub. -/
private theorem blob_exists_asym (hN : N.IsPhylogenetic) {q : Finset X} (hq : #q = 4) {v : V}
    (hv : ∀ x ∈ q, ∃ e ∈ N.ancestralArcs (q : Set X), ∃ S : Set V,
      (∀ f ∈ N.ancestralArcs (q : Set X), N.graph.Crosses f S ↔ f = e) ∧
      (∀ y ∈ q, N.leaf y ∈ S ↔ y = x) ∧ v ∉ S ∧
      (N.graph.source e = v ∨ N.graph.target e = v)) :
    ∃ a ∈ q, ∀ x ∈ q, x ≠ a → ∃ e, N.graph.source e = v ∧ N.Dominates e x ∧
      ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y := by
  have hb : ∀ x ∈ q, ∃ e,
      (N.graph.source e = v ∧ N.Dominates e x ∧ ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y) ∨
      (N.graph.target e = v ∧ ¬ N.IsBelow e x ∧ ∀ y ∈ q, y ≠ x → N.Dominates e y) := by
    intro x hx
    obtain ⟨e, he, S, hS, hleaf, hvS, hev⟩ := hv x hx
    exact ⟨e, blob_arc hN he hS hleaf hvS hev hx⟩
  by_cases hall : ∀ x ∈ q, ∃ e, N.graph.source e = v ∧ N.Dominates e x ∧
      ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y
  · obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #q)
    exact ⟨a, ha, fun x hx _ => hall x hx⟩
  · push Not at hall
    obtain ⟨x₀, hx₀, hnot⟩ := hall
    obtain ⟨e₀, h₀⟩ := hb x₀ hx₀
    have h₀' : N.graph.target e₀ = v ∧ ¬ N.IsBelow e₀ x₀ ∧
        ∀ y ∈ q, y ≠ x₀ → N.Dominates e₀ y := by
      rcases h₀ with ⟨h1, h2, h3⟩ | h
      · obtain ⟨y, hy, hyx, hyb⟩ := hnot e₀ h1 h2
        exact absurd hyb (h3 y hy hyx)
      · exact h
    obtain ⟨ht₀, -, hdom₀⟩ := h₀'
    refine ⟨x₀, hx₀, fun x hx hxne => ?_⟩
    obtain ⟨e, h⟩ := hb x hx
    rcases h with h | ⟨ht, hnb, -⟩
    · exact ⟨e, h⟩
    · have hd₀ := hdom₀ x hx hxne
      have : e = e₀ := eq_of_dominates_of_target_eq hN hd₀ (ht.trans ht₀.symm)
      exact absurd (hd₀.isBelow hN) (this ▸ hnb)

variable (N) in
/-- The singleton lineages of `q`, those of `T` moved up to the vertex `v`. -/
def hubInj (q T : Finset X) (v : V) : V → Finset (Finset X) := fun u =>
  taxaInj N (q \ T) u ∪ (if u = v then T.image fun x => ({x} : Finset X) else ∅)

omit [Fintype V] [Fintype E] in
theorem mem_lineages_hubInj {q T : Finset X} {v u : V} (x : X) :
    x ∈ lineages (hubInj N q T v u) ↔ (x ∈ q \ T ∧ N.leaf x = u) ∨ (u = v ∧ x ∈ T) := by
  unfold hubInj
  rw [lineages_union, mem_union, mem_lineages_taxaInj]
  refine or_congr Iff.rfl ?_
  by_cases hu : u = v
  · simp [hu]
  · simp [hu]

omit [Fintype V] [Fintype E] in
theorem validInj_hubInj (q T : Finset X) (v : V) : ValidInj (hubInj N q T v) := by
  refine ⟨fun u => ?_, fun u u' huu' => disjoint_left.2 fun x hx hx' => ?_⟩
  · unfold hubInj
    refine IsGoodForest.union (isGoodForest_singletons _) ?_ (disjoint_left.2 fun x hx hx' => ?_)
    · split_ifs
      · exact isGoodForest_singletons _
      · exact isGoodForest_empty
    · have hxq := (mem_lineages_taxaInj.1 hx).1
      split_ifs at hx' with hu
      · rw [lineages_image_singleton] at hx'
        exact (mem_sdiff.1 hxq).2 hx'
      · simp at hx'
  · rcases (mem_lineages_hubInj x).1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases (mem_lineages_hubInj x).1 hx' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact huu' (h2.symm.trans h4)
    · exact (mem_sdiff.1 h1).2 h4
    · exact (mem_sdiff.1 h3).2 h2
    · exact huu' (h1.trans h3.symm)

omit [Fintype V] [Fintype E] in
theorem hubInj_empty (q : Finset X) (v : V) : hubInj N q ∅ v = taxaInj N q := by
  funext u
  unfold hubInj
  simp

/-- A lineage alone below an arc leaving the hub moves up to the hub. -/
theorem injDist_hubInj_insert (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q T : Finset X} {v : V} {x : X} (hxq : x ∈ q) (hxT : x ∉ T) {e : E}
    (hs : N.graph.source e = v) (hd : N.Dominates e x)
    (hn : ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y) (G : Finset (Finset X)) :
    injDist N θ ρ (hubInj N q T v) G = injDist N θ ρ (hubInj N q (insert x T) v) G := by
  have hb := hd.isBelow hN
  have hvB : ∀ u ∈ belowSet N e, u ≠ v := fun u hu h =>
    source_notMem_belowSet hN e (hs ▸ h ▸ hu)
  have hbel : ∀ u ∈ belowSet N e, ∀ z ∈ lineages (hubInj N q T v u), z = x := by
    intro u hu z hz
    rcases (mem_lineages_hubInj z).1 hz with ⟨hzq, rfl⟩ | ⟨h, -⟩
    · by_contra hzx
      exact hn z (mem_sdiff.1 hzq).1 hzx (mem_belowSet.1 hu)
    · exact absurd h (hvB u hu)
  have hdom : DominatedInj N e (hubInj N q T v) := by
    rintro u hu ⟨A, hA⟩
    obtain ⟨z, hz⟩ := (validInj_hubInj (N := N) q T v).good u |>.1.1 A hA
    have hzl : z ∈ lineages (hubInj N q T v u) := mem_lineages.2 ⟨A, hA, hz⟩
    have hzx := hbel u hu z hzl
    subst hzx
    rcases (mem_lineages_hubInj z).1 hzl with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hd
    · exact absurd h (hvB u hu)
  have hmem : x ∈ q \ T := mem_sdiff.2 ⟨hxq, hxT⟩
  have h := injDist_eq_lift_singleton (θ := θ) (ρ := ρ) hN hθ hρ (validInj_hubInj q T v) hdom
    (y := x) ⟨N.leaf x, mem_belowSet.2 hb, (mem_lineages_hubInj x).2 (Or.inl ⟨hmem, rfl⟩)⟩ hbel G
  rw [h]
  suffices hlift : liftInj N e (hubInj N q T v) {{x}} = hubInj N q (insert x T) v by rw [hlift]
  funext u
  by_cases hu : u ∈ belowSet N e
  · rw [liftInj_of_mem hN hu]
    symm
    refine eq_empty_of_forall_notMem fun A hA => ?_
    unfold hubInj at hA
    rcases mem_union.1 hA with hA | hA
    · obtain ⟨z, hz, rfl⟩ := mem_image.1 hA
      obtain ⟨hzq, rfl⟩ := (mem_filter.1 hz).2
      obtain ⟨hzq', hzT⟩ := mem_sdiff.1 hzq
      have hzx : z ≠ x := fun h => hzT (h ▸ mem_insert_self _ _)
      exact hn z hzq' hzx (mem_belowSet.1 hu)
    · rw [ite_eq_right (hvB u hu)] at hA
      exact notMem_empty _ hA
  · have hxu : N.leaf x ≠ u := fun h => hu (h ▸ mem_belowSet.2 hb)
    have hT : taxaInj N (q \ T) u = taxaInj N (q \ insert x T) u := by
      ext D
      simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨z, ⟨hz, hzu⟩, rfl⟩
        have hzx : z ≠ x := fun h => hxu (h ▸ hzu)
        refine ⟨z, ⟨mem_sdiff.2 ⟨(mem_sdiff.1 hz).1, ?_⟩, hzu⟩, rfl⟩
        simp [hzx, (mem_sdiff.1 hz).2]
      · rintro ⟨z, ⟨hz, hzu⟩, rfl⟩
        refine ⟨z, ⟨mem_sdiff.2 ⟨(mem_sdiff.1 hz).1, fun h => (mem_sdiff.1 hz).2 ?_⟩, hzu⟩, rfl⟩
        exact mem_insert_of_mem h
    unfold liftInj hubInj
    rw [hs, hT]
    simp only [hu, ↓reduceIte]
    by_cases huv : u = v
    · simp only [huv, ↓reduceIte, image_insert, union_assoc]
      congr 1
      rw [union_comm]
      rfl
    · simp [huv]

/-- All the lineages of `P` move up to the hub. -/
theorem injDist_hubInj (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {v : V} (P : Finset X) (hP : P ⊆ q)
    (h : ∀ x ∈ P, ∃ e, N.graph.source e = v ∧ N.Dominates e x ∧
      ∀ y ∈ q, y ≠ x → ¬ N.IsBelow e y) (G : Finset (Finset X)) :
    injDist N θ ρ (taxaInj N q) G = injDist N θ ρ (hubInj N q P v) G := by
  induction P using Finset.induction_on with
  | empty => rw [hubInj_empty]
  | insert x P hx ih =>
    obtain ⟨e, hs, hd, hn⟩ := h x (mem_insert_self _ _)
    rw [ih (fun z hz => hP (mem_insert_of_mem hz)) (fun z hz => h z (mem_insert_of_mem hz))]
    exact injDist_hubInj_insert hN hθ hρ (hP (mem_insert_self _ _)) hx hs hd hn G

/-- On a trivial 4-blob, all three concordance factors are `1/3`. -/
theorem trivial_uniform (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (q : Finset X) (hq : q.card = 4) (ht : HasTrivialFourBlob N q) :
    ∀ r ∈ treesOn q, nmscCF N θ ρ r = 1 / 3 := by
  intro r hr
  have hrt := mem_treesOn.1 hr
  obtain ⟨v, hv⟩ := ht
  obtain ⟨a, ha, hasym⟩ := blob_exists_asym hN hq hv
  set P := q.erase a with hP
  rw [nmscCF_eq_cherryMass hN hθ hρ r, hrt,
    cherryMass_congr (injDist_hubInj hN hθ hρ P (erase_subset _ _)
      fun x hx => hasym x (mem_of_mem_erase hx) (ne_of_mem_erase hx))]
  refine cherryMass_eq_third hN hθ hρ (validInj_hubInj q P v) hq (fun x => ?_) ha
    (fun x hx y hy hxa hya => ?_) hr
  · constructor
    · rintro ⟨u, hu⟩
      rcases (mem_lineages_hubInj x).1 hu with ⟨h, -⟩ | ⟨-, h⟩
      · exact (mem_sdiff.1 h).1
      · exact mem_of_mem_erase h
    · intro hx
      by_cases hxa : x = a
      · refine ⟨N.leaf x, (mem_lineages_hubInj x).2 (Or.inl ⟨mem_sdiff.2 ⟨hx, ?_⟩, rfl⟩)⟩
        rw [hxa]
        exact notMem_erase a q
      · exact ⟨v, (mem_lineages_hubInj x).2 (Or.inr ⟨rfl, mem_erase.2 ⟨hxa, hx⟩⟩)⟩
  · funext u
    unfold relabelInj hubInj
    rw [relabelFamily_union]
    congr 1
    · refine relabelFamily_taxaInj fun z hz _ => ?_
      have hza : z = a := by
        by_contra hza
        exact (mem_sdiff.1 hz).2 (mem_erase.2 ⟨hza, (mem_sdiff.1 hz).1⟩)
      rw [hza]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya)
    · split_ifs
      · exact relabelFamily_swap_singletons (mem_erase.2 ⟨hxa, hx⟩) (mem_erase.2 ⟨hya, hy⟩)
      · exact relabelFamily_empty _

end NMSC

end Phylogenetics
