module

public import Phylogenetics.NMSC.Cycle
public import Phylogenetics.NMSC.Displays
/-!
# Gene trees drawn from the NMSC

Facts about i.i.d. gene trees drawn from the NMSC on a network, for estimating quartet and
component CFs from a sample of gene trees: the chosen taxa lie in their components, the quartet CF
of taxa of four distinct components is their component CF, the probability that a gene tree
displays a quartet is its quartet CF, and the gene trees are identically distributed.
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open Finset

/-- The chosen taxon `x i` lies in the component labelled `i`: the components are pairwise
disjoint, and `x i` lies in the component at position `ord.symm i` (`hx`) and in the one at
position `ord.symm (comp (x i))` (`hcomp`). -/
theorem comp_rep_eq {X : Type u} [DecidableEq X] {N : Net X} (hN : N.WellFormed)
    (Ω : N.Cycle) {d : ℕ} (ord : Equiv.Perm (Fin d)) (comp : X → Fin d)
    (hcomp : ∀ t, t ∈ Ω.component (ord.symm (comp t))) (x : Fin d → X)
    (hx : ∀ i : Fin d, x (ord i) ∈ Ω.component i) (i : Fin d) : comp (x i) = i := by
  by_contra hne
  have h1 : x i ∈ Ω.component (ord.symm i) := by
    simpa using hx (ord.symm i)
  have hne' : ((ord.symm (comp (x i)) : Fin d) : ℕ) ≠ (ord.symm i : ℕ) :=
    fun h => hne (ord.symm.injective (Fin.ext h))
  exact Finset.disjoint_left.1 (Ω.component_disjoint hN.2 hne') (hcomp (x i)) h1

/-- For taxa `a, b, c, e` of four distinct components, the quartet CF is the component CF of their
components: by `Phylogenetics.nmsc_quartetCF`, both are the CF `cycleCF M` of the induced metric
quarnet, for the choice `x` and for the choice `y` that picks `a, b, c, e` in their components. -/
theorem quartetCF_eq_componentCF_of_comp {X : Type u} [DecidableEq X] {N : Net X}
    (hN : N.WellFormed) (Ω : N.Cycle) {d : ℕ} (hΩ : Ω.size = d) (ord : Equiv.Perm (Fin d))
    (comp : X → Fin d) (hcomp : ∀ t, t ∈ Ω.component (ord.symm (comp t))) (x : Fin d → X)
    (hx : ∀ i : Fin d, x (ord i) ∈ Ω.component i) {a b c e : X} (hab : comp a ≠ comp b)
    (hac : comp a ≠ comp c) (hae : comp a ≠ comp e) (hbc : comp b ≠ comp c)
    (hbe : comp b ≠ comp e) (hce : comp c ≠ comp e) :
    N.quartetCF a b c e = N.componentCF x (comp a) (comp b) (comp c) (comp e) := by
  obtain ⟨M, hγ, hw⟩ := Ω.exists_metricCycle hN
  subst hΩ
  -- the choice `y` picks `a, b, c, e` in their components and agrees with `x` elsewhere
  set y : Fin Ω.size → X := fun i =>
    if i = comp a then a else if i = comp b then b else if i = comp c then c
      else if i = comp e then e else x i with hy_def
  have hy : ∀ i : Fin Ω.size, y (ord i) ∈ Ω.component i := by
    intro i
    have key : ∀ t, ord i = comp t → t ∈ Ω.component i := by
      intro t h
      have := hcomp t
      rwa [← h, Equiv.symm_apply_apply] at this
    simp only [hy_def]
    split_ifs with h1 h2 h3 h4
    · exact key a h1
    · exact key b h2
    · exact key c h3
    · exact key e h4
    · exact hx i
  have hya : y (comp a) = a := by simp [hy_def]
  have hyb : y (comp b) = b := by simp [hy_def, hab.symm]
  have hyc : y (comp c) = c := by simp [hy_def, hac.symm, hbc.symm]
  have hye : y (comp e) = e := by simp [hy_def, hae.symm, hbe.symm, hce.symm]
  have h1 := nmsc_quartetCF N hN Ω rfl M hγ hw ord x hx (comp a) (comp b) (comp c) (comp e)
    hab hac hae hbc hbe hce
  have h2 := nmsc_quartetCF N hN Ω rfl M hγ hw ord y hy (comp a) (comp b) (comp c) (comp e)
    hab hac hae hbc hbe hce
  rw [h1, ← h2]
  simp only [Net.componentCF, hya, hyb, hyc, hye]

/-- The probability that the gene tree `G0`, distributed as the gene tree of the NMSC on `N` in
which lineage `t` of `L` is sampled from the taxon `s t`, displays `ij|kl`, for distinct lineages,
is the quartet CF of `s i, s j, s k, s l` (`Phylogenetics.quartetCF_eq_displays_sample`). -/
theorem measureReal_geneTreeDisplays_sample {X : Type u} [DecidableEq X] {L : Type*} [Fintype L]
    [DecidableEq L] {N : Net X} (hN : N.leaves.Nodup) (s : L → X) {S : Type*} [MeasurableSpace S]
    [MeasurableSpace (Finset (Finset L))] [MeasurableSingletonClass (Finset (Finset L))]
    (P : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure P]
    (G0 : S → Finset (Finset L)) (hG0 : Measurable G0)
    (hlaw : ∀ g, P.real (G0 ⁻¹' {g}) = N.geneTreeDist s g) {i j k l : L} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    P.real {ω | geneTreeDisplays (G0 ω) i j k l = true} = N.quartetCF (s i) (s j) (s k) (s l) := by
  have hset : {ω | geneTreeDisplays (G0 ω) i j k l = true} =
      G0 ⁻¹' ↑(univ.filter fun g => geneTreeDisplays g i j k l = true) := by
    ext ω
    simp
  rw [hset, ← MeasureTheory.sum_measureReal_preimage_singleton _
      (fun g _ => hG0 (measurableSet_singleton g)),
    quartetCF_eq_displays_sample N hN s hij hik hil hjk hjl hkl, Finset.sum_filter]
  exact Finset.sum_congr rfl fun g _ => by rw [hlaw]

/-- The probability that the gene tree `G0`, distributed as the gene tree of the NMSC on `N`,
displays `ab|ce` is the quartet CF (`Phylogenetics.quartetCF_eq_displays`; the case `s = id` of
`Phylogenetics.measureReal_geneTreeDisplays_sample`). -/
theorem measureReal_geneTreeDisplays {X : Type u} [Fintype X] [DecidableEq X] {N : Net X}
    (hN : N.leaves.Nodup) {S : Type*} [MeasurableSpace S]
    [MeasurableSpace (Finset (Finset X))] [MeasurableSingletonClass (Finset (Finset X))]
    (P : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure P]
    (G0 : S → Finset (Finset X)) (hG0 : Measurable G0)
    (hlaw : ∀ g, P.real (G0 ⁻¹' {g}) = N.geneTreeDist id g) {a b c e : X} (hab : a ≠ b)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    P.real {s | geneTreeDisplays (G0 s) a b c e = true} = N.quartetCF a b c e :=
  measureReal_geneTreeDisplays_sample hN id P G0 hG0 hlaw hab hac hae hbc hbe hce

/-- For taxa `a, b, c, e` of four distinct components, the probability that the gene tree `G0`,
distributed as the gene tree of the NMSC on `N`, displays `ab|ce` is the component CF of their
components (`measureReal_geneTreeDisplays`, `quartetCF_eq_componentCF_of_comp`). -/
theorem measureReal_geneTreeDisplays_eq_componentCF {X : Type u} [Fintype X] [DecidableEq X]
    {N : Net X} (hN : N.WellFormed) (Ω : N.Cycle) {d : ℕ} (hΩ : Ω.size = d)
    (ord : Equiv.Perm (Fin d)) (comp : X → Fin d)
    (hcomp : ∀ t, t ∈ Ω.component (ord.symm (comp t))) (x : Fin d → X)
    (hx : ∀ i : Fin d, x (ord i) ∈ Ω.component i) {S : Type*} [MeasurableSpace S]
    [MeasurableSpace (Finset (Finset X))] [MeasurableSingletonClass (Finset (Finset X))]
    (P : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure P]
    (G0 : S → Finset (Finset X)) (hG0 : Measurable G0)
    (hlaw : ∀ g, P.real (G0 ⁻¹' {g}) = N.geneTreeDist id g) {a b c e : X}
    (hab : comp a ≠ comp b) (hac : comp a ≠ comp c) (hae : comp a ≠ comp e)
    (hbc : comp b ≠ comp c) (hbe : comp b ≠ comp e) (hce : comp c ≠ comp e) :
    P.real {s | geneTreeDisplays (G0 s) a b c e = true} =
      N.componentCF x (comp a) (comp b) (comp c) (comp e) := by
  rw [measureReal_geneTreeDisplays hN.2 P G0 hG0 hlaw (ne_of_apply_ne comp hab)
    (ne_of_apply_ne comp hac) (ne_of_apply_ne comp hae) (ne_of_apply_ne comp hbc)
    (ne_of_apply_ne comp hbe) (ne_of_apply_ne comp hce)]
  exact quartetCF_eq_componentCF_of_comp hN Ω hΩ ord comp hcomp x hx hab hac hae hbc hbe hce

/-- The gene trees `G n` all have the law of `G 0`: their laws are measures on a countable space
with measurable singletons that agree on the singletons (`hlaw`). -/
theorem identDistrib_of_law {X : Type u} [Fintype X] [DecidableEq X] {S : Type*}
    [MeasurableSpace S] [MeasurableSpace (Finset (Finset X))]
    [MeasurableSingletonClass (Finset (Finset X))] (P : MeasureTheory.Measure S)
    [MeasureTheory.IsProbabilityMeasure P] (G : ℕ → S → Finset (Finset X))
    (hG : ∀ n, Measurable (G n)) (μ : Finset (Finset X) → ℝ)
    (hlaw : ∀ n g, P.real (G n ⁻¹' {g}) = μ g) (n : ℕ) :
    ProbabilityTheory.IdentDistrib (G n) (G 0) P P where
  aemeasurable_fst := (hG n).aemeasurable
  aemeasurable_snd := (hG 0).aemeasurable
  map_eq := MeasureTheory.Measure.ext_of_measureReal_singleton fun g => by
    rw [MeasureTheory.map_measureReal_apply (hG n) (measurableSet_singleton g),
      MeasureTheory.map_measureReal_apply (hG 0) (measurableSet_singleton g), hlaw, hlaw]

end Phylogenetics
