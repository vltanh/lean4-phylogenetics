module

public import Phylogenetics.Coalescent.Trace
public import Phylogenetics.NMSC.History
public import Phylogenetics.Tree.Splits

/-!
# Sampling consistency of the network multispecies coalescent

The forest formed by a subset `Z` of the lineages is distributed as the process of that subset
(`sum_injDist_trace`). It combines three consistencies, vertex by vertex along a linear extension:
Kingman's coalescent lumps (`Phylogenetics.Coalescent.Trace`), the urn at a reticulation
is consistent (`sum_allocationWeight_mul_comp`), and `forestBelow` commutes with restriction
(`traceForest_forestBelow`).

Consequently the concordance factor of a quartet tree `s` can be read from the process of the
lineages of the four taxa of `s` (`nmscCF_eq_cherryMass`).

## Main results

* `vertexKernel`, `card_sq_mul_sum_insert`: summing out the arcs entering the topmost vertex,
  against a test function.
* `vertexKernel_trace`: consistency at one vertex.
* `sum_injDist_trace`, `geneTreeDistOn`, `geneTreeDist_trace`: consistency.
* `cherryMass`, `displays_unroot_iff`, `nmscCF_eq_cherryMass`: concordance factors.

All of these use the inheritance probabilities only through their sums, so each has a version with
the suffix `_weak` for `RootedNetwork.IsNormalized`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- The restrictions of the forests of all arcs. -/
abbrev traceAll (Z : Finset X) (t : E → Finset (Finset X)) : E → Finset (Finset X) :=
  fun f => traceForest Z (t f)

variable (N θ ρ) in
/-- One step of the chain at the vertex `v`, from the forest `F` arriving there, against a test
function `ψ` of the forests at the top of its arcs. -/
def vertexKernel (v : V) (F : Finset (Finset X)) (ψ : (E → Finset (Finset X)) → ℝ) : ℝ :=
  ∑ b : E → Finset (Finset X), allocationFactor N θ ρ F v b *
    ∑ t : E → Finset (Finset X),
      (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) * ψ t

omit [Fintype V] [Fintype X] in
theorem arriving_trace (Z : Finset X) (inj : V → Finset (Finset X))
    (top : E → Finset (Finset X)) (v : V) :
    traceForest Z (arriving N inj top v) =
      arriving N (fun u => traceForest Z (inj u)) (traceAll Z top) v := by
  unfold arriving
  rw [traceForest_union, traceForest_biUnion]

/-! ### Summing out the arcs entering a vertex -/

omit [Fintype V] in
/-- **The chain at the topmost vertex of `insert v D`**, tested against a function `φ` of the
forests at the tops. -/
theorem card_sq_mul_sum_insert {inj : V → Finset (Finset X)} {D : Finset V}
    (hD : DownClosed N D) {v : V} (hvD : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) (φ : (E → Finset (Finset X)) → ℝ) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          vertexKernel N θ ρ v (arriving N inj top v)
            (fun t => φ (overwrite (arcsInto N v) top t)) := by
  set S := arcsInto N v with hS
  set M : ℝ := (Fintype.card (E → Finset (Finset X)) : ℝ) with hM
  let L : (E → Finset (Finset X)) → (E → Finset (Finset X)) → ℝ := fun bot top =>
    ∑ t : E → Finset (Finset X),
      (∏ f ∈ S, kingmanTransition (θ.length f) (bot f) (t f)) * φ (overwrite S top t)
  -- summing out the tops of the arcs entering `v`
  have htop : ∀ bot : E → Finset (Finset X),
      M * ∑ top : E → Finset (Finset X),
          (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top =
        ∑ top : E → Finset (Finset X), (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          (allocationFactor N θ ρ (arriving N inj top v) v bot * L bot top) := by
    intro bot
    have := card_mul_sum_mul S
      (fun top : E → Finset (Finset X) => (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
        allocationFactor N θ ρ (arriving N inj top v) v bot)
      (fun top => (∏ f ∈ S, kingmanTransition (θ.length f) (bot f) (top f)) * φ top)
      (fun top y => by
        simp only [hS, prod_vertexWeight_overwrite_top hD hvD, arriving_overwrite hvD hch])
    rw [hM, sum_congr rfl fun top _ => ?_]
    · rw [this]
      refine sum_congr rfl fun top _ => ?_
      rw [mul_assoc]
      congr 2
      refine sum_congr rfl fun t _ => ?_
      congr 1
      exact prod_congr rfl fun f hf => by rw [overwrite_of_mem hf]
    · rw [prod_insert hvD]
      unfold vertexWeight
      ring
  -- summing out the bottoms of the arcs entering `v`
  have hbot : ∀ top : E → Finset (Finset X),
      M * ∑ bot : E → Finset (Finset X), (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          (allocationFactor N θ ρ (arriving N inj top v) v bot * L bot top) =
        ∑ bot : E → Finset (Finset X), (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          vertexKernel N θ ρ v (arriving N inj top v) (fun t => φ (overwrite S top t)) := by
    intro top
    rw [hM, card_mul_sum_mul S _ _ fun bot y => prod_vertexWeight_overwrite_bot hvD top bot y]
    refine sum_congr rfl fun bot _ => ?_
    congr 1
    refine sum_congr rfl fun b _ => ?_
    have h1 : allocationFactor N θ ρ (arriving N inj top v) v (overwrite S bot b) =
        allocationFactor N θ ρ (arriving N inj top v) v b :=
      allocationFactor_congr fun e he => overwrite_of_mem (mem_arcsInto.2 he) _ _
    have h2 : L (overwrite S bot b) top =
        ∑ t : E → Finset (Finset X),
          (∏ f ∈ S, kingmanTransition (θ.length f) (b f) (t f)) * φ (overwrite S top t) := by
      refine sum_congr rfl fun t _ => ?_
      congr 1
      exact prod_congr rfl fun f hf => by rw [overwrite_of_mem hf]
    rw [h1, h2]
  calc M * (M * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top)
      = M * ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
            (allocationFactor N θ ρ (arriving N inj top v) v bot * L bot top) := by
        rw [mul_sum]
        congr 1
        exact sum_congr rfl fun bot _ => htop bot
    _ = M * ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X),
          (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
            (allocationFactor N θ ρ (arriving N inj top v) v bot * L bot top) := by
        rw [sum_comm]
    _ = ∑ top : E → Finset (Finset X), ∑ bot : E → Finset (Finset X),
          (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
            vertexKernel N θ ρ v (arriving N inj top v) (fun t => φ (overwrite S top t)) := by
        rw [mul_sum]
        exact sum_congr rfl fun top _ => hbot top
    _ = _ := sum_comm

/-! ### Consistency at one vertex -/

omit [Fintype V] in
/-- Kingman's coalescent lumps along several arcs. -/
theorem sum_prod_kingman_trace (S : Finset E) (ℓ : E → ℝ) (Z : Finset X)
    {b : E → Finset (Finset X)} (hb : ∀ f ∈ S, IsForest (b f))
    (ψ : (E → Finset (Finset X)) → ℝ) (hψ : ∀ t t', (∀ f ∈ S, t f = t' f) → ψ t = ψ t') :
    ∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) * ψ (traceAll Z t) =
      ∑ t : E → Finset (Finset X),
        (∏ f ∈ S, kingmanTransition (ℓ f) (traceForest Z (b f)) (t f)) * ψ t := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) ^ #Sᶜ with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hB.ne'
  refine mul_right_cancel₀ hc0 ?_
  have hψsum : ∀ u : E → Finset (Finset X),
      ψ u * c = ∑ y : E → Finset (Finset X), if ∀ f ∈ S, y f = u f then ψ y else 0 :=
    fun u => (sum_ite_forall_mul S u ψ hψ).symm
  have hinner : ∀ y : E → Finset (Finset X),
      ∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) *
          (if ∀ f ∈ S, y f = traceForest Z (t f) then 1 else 0) =
        (∏ f ∈ S, kingmanTransition (ℓ f) (traceForest Z (b f)) (y f)) * c := by
    intro y
    have h := sum_prod_mem S
      (fun f τ => if traceForest Z τ = y f then kingmanTransition (ℓ f) (b f) τ else 0)
    rw [prod_congr rfl fun f hf => kingmanTransition_trace (hb f hf) Z (ℓ f) (y f)] at h
    rw [← h]
    refine sum_congr rfl fun t _ => ?_
    rw [prod_ite_zero]
    by_cases ht : ∀ f ∈ S, traceForest Z (t f) = y f
    · have ht' : ∀ f ∈ S, y f = traceForest Z (t f) := fun f hf => (ht f hf).symm
      rw [ite_eq_left ht, ite_eq_left ht', mul_one]
    · have ht' : ¬ ∀ f ∈ S, y f = traceForest Z (t f) := fun h' => ht fun f hf => (h' f hf).symm
      rw [ite_eq_right ht, ite_eq_right ht', mul_zero]
  calc (∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) *
          ψ (traceAll Z t)) * c
      = ∑ t : E → Finset (Finset X), (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) *
          ∑ y : E → Finset (Finset X), if ∀ f ∈ S, y f = traceForest Z (t f) then ψ y else 0 := by
        rw [sum_mul]
        refine sum_congr rfl fun t _ => ?_
        rw [mul_assoc, hψsum]
    _ = ∑ y : E → Finset (Finset X), ψ y * ∑ t : E → Finset (Finset X),
          (∏ f ∈ S, kingmanTransition (ℓ f) (b f) (t f)) *
            (if ∀ f ∈ S, y f = traceForest Z (t f) then 1 else 0) := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun t _ => ?_
        split_ifs <;> ring
    _ = _ := by
        simp only [hinner]
        rw [sum_mul]
        refine sum_congr rfl fun y _ => ?_
        ring

omit [Fintype V] in
/-- The urn is consistent at a vertex: restricting the lineages `Z` after the allocation of the
roots of `F` is the allocation of the roots of the restriction. -/
theorem sum_allocationFactor_trace_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    (hρ : 0 ≤ ρ) {v : V} (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F)
    (Z : Finset X) (Λ : (E → Finset (Finset X)) → ℝ)
    (hΛ : ∀ b b', (∀ f ∈ arcsInto N v, b f = b' f) → Λ b = Λ b') :
    ∑ b : E → Finset (Finset X), allocationFactor N θ ρ F v b * Λ (traceAll Z b) =
      ∑ b : E → Finset (Finset X), allocationFactor N θ ρ (traceForest Z F) v b * Λ b := by
  have hΛ' : ∀ b b' : E → Finset (Finset X), (∀ f ∈ arcsInto N v, b f = b' f) →
      Λ (traceAll Z b) = Λ (traceAll Z b') := fun b b' h =>
    hΛ _ _ fun f hf => by simp only [traceAll, h f hf]
  rw [sum_allocationFactor_mul F v (fun b => Λ (traceAll Z b)) hΛ',
    sum_allocationFactor_mul (traceForest Z F) v Λ hΛ]
  set rF := traceForest Z F with hrF
  -- each root of the restriction is the trace of a root of `F`
  have hex : ∀ r' : {A // A ∈ roots rF}, ∃ r : {A // A ∈ roots F},
      (r.val ∩ Z).Nonempty ∧ r.val ∩ Z = r'.val := by
    intro r'
    obtain ⟨A, hA, hm, hAZ⟩ := (mem_roots_traceForest hF).1 r'.property
    exact ⟨⟨A, hA⟩, hm, hAZ⟩
  choose j hjm hjZ using hex
  have hjinj : Function.Injective j := fun r' s' h =>
    Subtype.ext (by rw [← hjZ r', ← hjZ s', h])
  have hγ := sum_inheritance_weak hN hθ hv
  rw [← sum_allocationWeight_mul_comp hρ hγ j hjinj
    (fun a' => Λ (assignedForest N rF v a') *
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ)]
  refine sum_congr rfl fun a _ => ?_
  congr 2
  refine hΛ _ _ fun f hf => ?_
  have hf' := mem_arcsInto.1 hf
  simp only [traceAll, assignedForest, hf', ↓reduceDIte]
  refine traceForest_forestBelow hF Z (fun A hA => ?_) fun C => ?_
  · obtain ⟨r, -, rfl⟩ := mem_image.1 hA
    exact r.property
  · simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨r', hr', rfl⟩
      exact ⟨(j r').val, ⟨j r', hr', rfl⟩, hjm r', hjZ r'⟩
    · rintro ⟨A, ⟨r, hr, rfl⟩, hm, rfl⟩
      have hroot : r.val ∩ Z ∈ roots rF := (mem_roots_traceForest hF).2 ⟨r.val, r.property, hm, rfl⟩
      refine ⟨⟨_, hroot⟩, ?_, rfl⟩
      have hjr : j ⟨_, hroot⟩ = r := Subtype.ext (hF.inter_inj_of_mem_roots (j ⟨_, hroot⟩).property
        r.property (hjm _) (hjZ ⟨_, hroot⟩))
      simp only [Function.comp, hjr, hr]

omit [Fintype V] in
/-- The urn is consistent at a vertex: restricting the lineages `Z` after the allocation of the
roots of `F` is the allocation of the roots of the restriction. -/
theorem sum_allocationFactor_trace (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {v : V} (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F)
    (Z : Finset X) (Λ : (E → Finset (Finset X)) → ℝ)
    (hΛ : ∀ b b', (∀ f ∈ arcsInto N v, b f = b' f) → Λ b = Λ b') :
    ∑ b : E → Finset (Finset X), allocationFactor N θ ρ F v b * Λ (traceAll Z b) =
      ∑ b : E → Finset (Finset X), allocationFactor N θ ρ (traceForest Z F) v b * Λ b :=
  sum_allocationFactor_trace_weak hN hθ.isNormalized hρ.1 hv hF Z Λ hΛ

omit [Fintype V] in
/-- Consistency of one step of the chain. -/
theorem vertexKernel_trace_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {v : V} (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F) (Z : Finset X)
    (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    vertexKernel N θ ρ v F (fun t => ψ (traceAll Z t)) =
      vertexKernel N θ ρ v (traceForest Z F) ψ := by
  unfold vertexKernel
  let Λ : (E → Finset (Finset X)) → ℝ := fun b => ∑ t : E → Finset (Finset X),
    (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) * ψ t
  have hΛ : ∀ b b' : E → Finset (Finset X), (∀ f ∈ arcsInto N v, b f = b' f) → Λ b = Λ b' := by
    intro b b' h
    refine sum_congr rfl fun t _ => ?_
    congr 1
    exact prod_congr rfl fun f hf => by rw [h f hf]
  change _ = ∑ b : E → Finset (Finset X), allocationFactor N θ ρ (traceForest Z F) v b * Λ b
  rw [← sum_allocationFactor_trace_weak hN hθ hρ hv hF Z Λ hΛ]
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : allocationFactor N θ ρ F v b = 0
  · simp [hb]
  · obtain ⟨a, ha⟩ := exists_assignment hb
    congr 1
    refine sum_prod_kingman_trace _ _ Z (fun f hf => ?_) ψ hψ
    rw [ha ⟨f, mem_arcsInto.1 hf⟩]
    exact hF.subset fun _ h => (mem_forestBelow.1 h).1

omit [Fintype V] in
/-- Consistency of one step of the chain. -/
theorem vertexKernel_trace (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {v : V} (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F) (Z : Finset X)
    (ψ : (E → Finset (Finset X)) → ℝ)
    (hψ : ∀ t t', (∀ f ∈ arcsInto N v, t f = t' f) → ψ t = ψ t') :
    vertexKernel N θ ρ v F (fun t => ψ (traceAll Z t)) =
      vertexKernel N θ ρ v (traceForest Z F) ψ :=
  vertexKernel_trace_weak hN hθ.isNormalized hρ.1 hv hF Z ψ hψ

/-! ### Consistency of the process -/

/-- The law of the forests at the top of the arcs entering a set `D` closed under children, for a
subset `Z` of the lineages. -/
theorem sum_sum_trace_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (Z : Finset X) {D : Finset V}
    (hD : DownClosed N D) (hroot : N.root ∉ D) (φ : (E → Finset (Finset X)) → ℝ)
    (hφ : ∀ t t', (∀ f, N.graph.target f ∈ D → t f = t' f) → φ t = φ t') :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ (traceAll Z top) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ (fun w => traceForest Z (inj w)) u bot top) * φ top := by
  set ri : V → Finset (Finset X) := fun w => traceForest Z (inj w) with hri
  induction D using Finset.strongInduction generalizing φ with
  | H D ih =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · have : ∀ top : E → Finset (Finset X), φ (traceAll Z top) = φ top :=
        fun top => hφ _ _ fun f hf => absurd hf (notMem_empty _)
      simp [this]
    · obtain ⟨v, hv, hD', hch⟩ := exists_top_vertex hN hD hne
      have hvr : v ≠ N.root := fun h => hroot (h ▸ hv)
      have hvD' : v ∉ D.erase v := notMem_erase v D
      set D₀ := D.erase v with hD₀
      have hins : insert v D₀ = D := insert_erase hv
      have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      let φ' : (E → Finset (Finset X)) → ℝ := fun top' =>
        vertexKernel N θ ρ v (arriving N ri top' v) (fun t => φ (overwrite (arcsInto N v) top' t))
      have hφ' : ∀ t t', (∀ f, N.graph.target f ∈ D₀ → t f = t' f) → φ' t = φ' t' := by
        intro t t' h
        have harr : arriving N ri t v = arriving N ri t' v :=
          arriving_congr rfl fun f hf => h f (hch f hf)
        simp only [φ', harr]
        unfold vertexKernel
        refine sum_congr rfl fun b _ => ?_
        congr 1
        refine sum_congr rfl fun y _ => ?_
        congr 1
        refine hφ _ _ fun f hf => ?_
        by_cases hfS : f ∈ arcsInto N v
        · rw [overwrite_of_mem hfS, overwrite_of_mem hfS]
        · rw [overwrite_of_notMem hfS, overwrite_of_notMem hfS]
          exact h f (mem_erase.2 ⟨fun h' => hfS (mem_arcsInto.2 h'), hf⟩)
      have hih := ih D₀ (erase_ssubset hv) hD' (fun h => hroot (mem_of_mem_erase h)) φ' hφ'
      have hleft := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD' hvD' hch
        (fun t => φ (traceAll Z t))
      have hright := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := ri) hD' hvD' hch φ
      rw [hins] at hleft hright
      refine mul_left_cancel₀ hM (mul_left_cancel₀ hM ?_)
      rw [hleft, hright, ← hih]
      refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
      by_cases hg : ∏ u ∈ D₀, vertexWeight N θ ρ inj u bot top = 0
      · simp [hg]
      · congr 1
        have hF := frontier_of_prod_ne_zero hN hinj hD' hg
        have hgood := (hF.good_arriving hinj hvD' hch).1
        have hψ : ∀ t t' : E → Finset (Finset X), (∀ f ∈ arcsInto N v, t f = t' f) →
            φ (overwrite (arcsInto N v) (traceAll Z top) t) =
              φ (overwrite (arcsInto N v) (traceAll Z top) t') := by
          intro t t' h
          refine congrArg φ (funext fun f => ?_)
          by_cases hfS : f ∈ arcsInto N v
          · rw [overwrite_of_mem hfS, overwrite_of_mem hfS, h f hfS]
          · rw [overwrite_of_notMem hfS, overwrite_of_notMem hfS]
        have hk := vertexKernel_trace_weak (N := N) (θ := θ) (ρ := ρ) hN hθ hρ hvr hgood Z _ hψ
        have hmap : ∀ t : E → Finset (Finset X), traceAll Z (overwrite (arcsInto N v) top t) =
            overwrite (arcsInto N v) (traceAll Z top) (traceAll Z t) := by
          intro t
          funext f
          by_cases hfS : f ∈ arcsInto N v
          · simp only [traceAll, overwrite_of_mem hfS]
          · simp only [traceAll, overwrite_of_notMem hfS]
        simp only [hmap, φ']
        rw [hk, arriving_trace]

/-- The law of the forests at the top of the arcs entering a set `D` closed under children, for a
subset `Z` of the lineages. -/
theorem sum_sum_trace (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (Z : Finset X) {D : Finset V}
    (hD : DownClosed N D) (hroot : N.root ∉ D) (φ : (E → Finset (Finset X)) → ℝ)
    (hφ : ∀ t t', (∀ f, N.graph.target f ∈ D → t f = t' f) → φ t = φ t') :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ (traceAll Z top) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ (fun w => traceForest Z (inj w)) u bot top) * φ top :=
  sum_sum_trace_weak hN hθ.isNormalized hρ.1 hinj Z hD hroot φ hφ

/-- **Sampling consistency.** The forest formed by the lineages `Z` in the process with injected
forests `inj` is distributed as the process with the restrictions of `inj`. -/
theorem sum_injDist_trace_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (Z : Finset X) (H : Finset (Finset X)) :
    ∑ G, (if traceForest Z G = H then injDist N θ ρ inj G else 0) =
      injDist N θ ρ (fun w => traceForest Z (inj w)) H := by
  set ri : V → Finset (Finset X) := fun w => traceForest Z (inj w) with hri
  have hD := downClosed_erase_root (N := N) hN
  have hall : ∀ f, N.graph.target f ∈ univ.erase N.root := fun f =>
    mem_erase.2 ⟨target_ne_root hN f, mem_univ _⟩
  have h := sum_sum_trace_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj Z hD (notMem_erase _ _)
    (fun top => kingmanAbsorption (arriving N ri top N.root) H)
    (fun t t' h => by
      have : t = t' := funext fun f => h f (hall f)
      rw [this])
  unfold injDist injWeight
  rw [← h]
  have hleft : ∀ G, (if traceForest Z G = H then
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top) *
            kingmanAbsorption (arriving N inj top N.root) G else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top) *
          if traceForest Z G = H then kingmanAbsorption (arriving N inj top N.root) G else 0 := by
    intro G
    split_ifs <;> simp
  simp only [hleft]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [← mul_sum]
  by_cases hw : ∏ v ∈ univ.erase N.root, vertexWeight N θ ρ inj v bot top = 0
  · simp [hw]
  · congr 1
    rw [kingmanAbsorption_trace (good_arriving_root hN hinj hw).1.1 Z H, arriving_trace]

/-- **Sampling consistency.** The forest formed by the lineages `Z` in the process with injected
forests `inj` is distributed as the process with the restrictions of `inj`. -/
theorem sum_injDist_trace (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (Z : Finset X) (H : Finset (Finset X)) :
    ∑ G, (if traceForest Z G = H then injDist N θ ρ inj G else 0) =
      injDist N θ ρ (fun w => traceForest Z (inj w)) H :=
  sum_injDist_trace_weak hN hθ.isNormalized hρ.1 hinj Z H

omit [Fintype V] [Fintype E] in
theorem traceForest_taxaInj (Y Z : Finset X) (v : V) :
    traceForest Z (taxaInj N Y v) = taxaInj N (Y ∩ Z) v := by
  ext D
  simp only [mem_traceForest, taxaInj, mem_image, mem_filter, mem_univ, true_and, mem_inter]
  constructor
  · rintro ⟨_, ⟨x, ⟨hxY, hxv⟩, rfl⟩, hm, rfl⟩
    obtain ⟨y, hy⟩ := hm
    obtain ⟨hyx, hyZ⟩ := mem_inter.1 hy
    obtain rfl := mem_singleton.1 hyx
    refine ⟨y, ⟨⟨hxY, hyZ⟩, hxv⟩, ?_⟩
    ext w
    simp only [mem_singleton, mem_inter]
    constructor
    · rintro rfl
      exact ⟨rfl, hyZ⟩
    · exact fun h => h.1
  · rintro ⟨x, ⟨⟨hxY, hxZ⟩, hxv⟩, rfl⟩
    refine ⟨{x}, ⟨x, ⟨hxY, hxv⟩, rfl⟩, ⟨x, by simp [hxZ]⟩, ?_⟩
    ext w
    simp only [mem_singleton, mem_inter]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, hxZ⟩

variable (N θ ρ) in
/-- The distribution of the forest of the lineages of the taxa `Y` under the network multispecies
coalescent. -/
abbrev geneTreeDistOn (Y : Finset X) (H : Finset (Finset X)) : ℝ :=
  injDist N θ ρ (taxaInj N Y) H

/-- All the taxa give the gene tree distribution. -/
theorem geneTreeDistOn_univ (hN : N.IsPhylogenetic) (G : Finset (Finset X)) :
    geneTreeDistOn N θ ρ univ G = geneTreeDist N θ ρ G :=
  (geneTreeDist_eq_injDist hN G).symm

/-- **Sampling consistency for gene trees**: the restriction of a gene tree to the taxa `Y` has the
distribution of the forest of the lineages of `Y`. -/
theorem geneTreeDist_trace_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (Y : Finset X) (H : Finset (Finset X)) :
    ∑ G, (if traceForest Y G = H then geneTreeDist N θ ρ G else 0) =
      geneTreeDistOn N θ ρ Y H := by
  simp only [geneTreeDist_eq_injDist hN]
  rw [sum_injDist_trace_weak hN hθ hρ (validInj_taxaInj univ) Y H]
  simp only [traceForest_taxaInj, univ_inter]

/-- **Sampling consistency for gene trees**: the restriction of a gene tree to the taxa `Y` has the
distribution of the forest of the lineages of `Y`. -/
theorem geneTreeDist_trace (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (Y : Finset X) (H : Finset (Finset X)) :
    ∑ G, (if traceForest Y G = H then geneTreeDist N θ ρ G else 0) =
      geneTreeDistOn N θ ρ Y H :=
  geneTreeDist_trace_weak hN hθ.isNormalized hρ.1 Y H

/-! ### Concordance factors -/

variable (N θ ρ) in
/-- The mass of the forests containing a cherry of `r`. -/
def cherryMass (inj : V → Finset (Finset X)) (r : QuartetTree X) : ℝ :=
  ∑ H, if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ inj H else 0

omit [Fintype V] [Fintype E] [Fintype X] in
private theorem cherry_nonempty (s : QuartetTree X) {B : Finset X}
    (hB : B ∈ s.val) : B.Nonempty :=
  card_pos.1 (by rw [s.card_of_mem hB]; omega)

/-- A rooted tree displays the quartet tree `s` when the restriction of its clusters to the taxa of
`s` contains a cherry of `s`. -/
theorem displays_unroot_iff (s : QuartetTree X) (G : Finset (Finset X)) :
    Displays (unroot G) s ↔ ∃ B ∈ s.val, B ∈ traceForest s.taxa G := by
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_unroot.1 hA with ⟨hAG, -⟩ | ⟨hAG, -⟩
    · exact ⟨_, hAs, inter_mem_traceForest hAG (cherry_nonempty s hAs)⟩
    · have hc : Aᶜ ∩ s.taxa = s.taxa \ (A ∩ s.taxa) := by
        ext x
        simp only [mem_inter, mem_compl, mem_sdiff]
        tauto
      have hm := s.sdiff_mem hAs
      rw [← hc] at hm
      exact ⟨_, hm, inter_mem_traceForest hAG (cherry_nonempty s hm)⟩
  · rintro ⟨B, hB, hBt⟩
    obtain ⟨A, hA, -, rfl⟩ := mem_traceForest.1 hBt
    refine ⟨A, mem_unroot.2 (Or.inl ⟨hA, ?_⟩), hB⟩
    rintro rfl
    have h1 := s.card_of_mem hB
    rw [univ_inter, s.card_taxa] at h1
    omega

/-- **The concordance factor of a quartet tree** is read from the lineages of its four taxa. -/
theorem nmscCF_eq_cherryMass_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (s : QuartetTree X) : nmscCF N θ ρ s = cherryMass N θ ρ (taxaInj N s.taxa) s := by
  unfold nmscCF cherryMass
  have h : ∀ G : Finset (Finset X), (if Displays (unroot G) s then geneTreeDist N θ ρ G else 0) =
      ∑ H, if traceForest s.taxa G = H then
        (if ∃ B ∈ s.val, B ∈ H then geneTreeDist N θ ρ G else 0) else 0 := by
    intro G
    rw [sum_ite_eq]
    simp only [mem_univ, ↓reduceIte, displays_unroot_iff]
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun H _ => ?_
  have hd : injDist N θ ρ (taxaInj N s.taxa) H =
      ∑ G, (if traceForest s.taxa G = H then geneTreeDist N θ ρ G else 0) :=
    (geneTreeDist_trace_weak hN hθ hρ s.taxa H).symm
  rw [hd]
  split_ifs with hc
  · rfl
  · simp

/-- **The concordance factor of a quartet tree** is read from the lineages of its four taxa. -/
theorem nmscCF_eq_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) : nmscCF N θ ρ s = cherryMass N θ ρ (taxaInj N s.taxa) s :=
  nmscCF_eq_cherryMass_weak hN hθ.isNormalized hρ.1 s

end NMSC

end Phylogenetics
