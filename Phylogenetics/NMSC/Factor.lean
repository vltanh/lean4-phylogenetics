module

public import Phylogenetics.NMSC.Symmetry
public import Phylogenetics.Network.Cuts

/-!
# The Markov property at an arc

Let `e` be an arc such that every vertex below it where a forest is injected has all its root paths
through `e`. Then the history splits at `e`: the part below `e` gives a law of the forest at the top
of `e`, and it only involves the forests injected below `e`; the part above `e` is the same process
with that forest injected at the source of `e` (`liftInj`), nothing being left below `e`.

## Main results

* `belowMass_mul_injDist`, `belowMass_mul_cherryMass`: the Markov property at the arc `e`.
* `good_top_of_prod_ne_zero`, `lineages_top_of_prod_ne_zero`: the forest at the top of `e`.
* `injDist_eq_lift_singleton`: a single lineage below `e` moves up to the source of `e`.
* `cherryMass_eq_of_lift`: two processes with the same forests below `e` are compared above `e`.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

variable (N) in
/-- The vertices below the arc `e`. -/
def belowSet (e : E) : Finset V := univ.filter fun v => N.graph.Reaches (N.graph.target e) v

variable (N) in
/-- The arcs entering a vertex below the arc `e`, including `e`. -/
def arcsBelow (e : E) : Finset E := univ.filter fun f => N.graph.target f ∈ belowSet N e

variable (N) in
/-- The injected forests after moving what is below `e` to the source of `e`, as the forest `F`. -/
def liftInj (e : E) (inj : V → Finset (Finset X)) (F : Finset (Finset X)) :
    V → Finset (Finset X) := fun v =>
  (if v ∈ belowSet N e then ∅ else inj v) ∪ (if v = N.graph.source e then F else ∅)

variable (N θ ρ) in
/-- The factors of the vertices not below `e`, with the root. -/
def restWeight (inj : V → Finset (Finset X)) (e : E) (G : Finset (Finset X))
    (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ (univ.erase N.root) \ belowSet N e, vertexWeight N θ ρ inj v bot top) *
    kingmanAbsorption (arriving N inj top N.root) G

/-- The forests `F` at `e` and empty at the other arcs. -/
def tauForest (e : E) (F : Finset (Finset X)) : E → Finset (Finset X) :=
  fun f => if f = e then F else ∅

variable (N θ ρ) in
/-- The part of the process above the arc `e`, given the forest `F` at its top. -/
def aboveMass (inj : V → Finset (Finset X)) (e : E) (G F : Finset (Finset X)) : ℝ :=
  ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
    restWeight N θ ρ inj e G b (overwrite (arcsBelow N e) t (tauForest e F))

/-! ### The vertices below an arc -/

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem mem_belowSet {e : E} {v : V} :
    v ∈ belowSet N e ↔ N.graph.Reaches (N.graph.target e) v := by
  simp [belowSet]

omit [Fintype X] [DecidableEq X] in
theorem mem_arcsBelow {e f : E} : f ∈ arcsBelow N e ↔ N.graph.target f ∈ belowSet N e := by
  simp [arcsBelow]

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem downClosed_belowSet (e : E) : DownClosed N (belowSet N e) := fun f hf =>
  mem_belowSet.2 ((mem_belowSet.1 hf).tail ⟨f, rfl, rfl⟩)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem target_mem_belowSet (e : E) : N.graph.target e ∈ belowSet N e :=
  mem_belowSet.2 .refl

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem source_notMem_belowSet (hN : N.IsPhylogenetic) (e : E) :
    N.graph.source e ∉ belowSet N e := fun h =>
  not_reaches_target_source hN.acyclic e (mem_belowSet.1 h)

omit [Fintype X] [DecidableEq X] in
theorem root_notMem_belowSet (hN : N.IsPhylogenetic) (e : E) : N.root ∉ belowSet N e := by
  intro h
  rcases Relation.ReflTransGen.cases_tail (mem_belowSet.1 h) with h' | ⟨_, -, f, -, hf⟩
  · exact target_ne_root hN e h'.symm
  · exact target_ne_root hN f hf

omit [Fintype X] [DecidableEq X] in
theorem belowSet_subset_erase (hN : N.IsPhylogenetic) (e : E) :
    belowSet N e ⊆ univ.erase N.root := fun _ hv =>
  mem_erase.2 ⟨fun h => root_notMem_belowSet hN e (h ▸ hv), mem_univ _⟩

omit [Fintype E] [Fintype X] in
theorem liftInj_of_mem {e : E} {inj : V → Finset (Finset X)} {F : Finset (Finset X)} {v : V}
    (hN : N.IsPhylogenetic) (hv : v ∈ belowSet N e) : liftInj N e inj F v = ∅ := by
  have hne : v ≠ N.graph.source e := fun h => source_notMem_belowSet hN e (h ▸ hv)
  simp [liftInj, hv, hne]

omit [Fintype E] [Fintype X] in
theorem mem_lineages_liftInj {e : E} {inj : V → Finset (Finset X)} {F : Finset (Finset X)} {v : V}
    (x : X) : x ∈ lineages (liftInj N e inj F v) ↔
      (v ∉ belowSet N e ∧ x ∈ lineages (inj v)) ∨ (v = N.graph.source e ∧ x ∈ lineages F) := by
  unfold liftInj
  rw [lineages_union, mem_union]
  refine or_congr ?_ ?_
  · by_cases hv : v ∈ belowSet N e <;> simp [hv]
  · by_cases hv : v = N.graph.source e <;> simp [hv]

/-! ### What the part below an arc gives -/

/-- Every vertex below `e` where a forest is injected has all its root paths through `e`. -/
def DominatedInj (N : RootedNetwork V E X) (e : E) (inj : V → Finset (Finset X)) : Prop :=
  ∀ u ∈ belowSet N e, (inj u).Nonempty → ¬ N.AvoidingReach e N.root u

omit [Fintype E] [Fintype X] in
/-- The arcs other than `e` leaving what is below `e` carry no lineages. -/
theorem frontier_top_eq_empty (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {e : E}
    (hdom : DominatedInj N e inj) {bot top : E → Finset (Finset X)}
    (hF : Frontier N inj (belowSet N e) bot top) {f : E} (hft : N.graph.target f ∈ belowSet N e)
    (hfs : N.graph.source f ∉ belowSet N e) (hfe : f ≠ e) : top f = ∅ := by
  by_contra hne
  obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨x, hx⟩ := (hF.good_top f hft).1.1 A hA
  obtain ⟨u, hu, hxu⟩ := hF.below f hft x (mem_lineages.2 ⟨A, hA, hx⟩)
  obtain ⟨B, hB, -⟩ := mem_lineages.1 hxu
  have huB : u ∈ belowSet N e := mem_belowSet.2 ((mem_belowSet.1 hft).trans hu)
  refine hdom u huB ⟨B, hB⟩ ?_
  have h1 : N.AvoidingReach e N.root (N.graph.source f) := by
    by_contra hn
    exact hfs (mem_belowSet.2 (target_reaches_of_not_avoidingReach (hN.root_reaches _) hn))
  exact (h1.tail ⟨f, hfe, rfl, rfl⟩).trans
    (avoidingReach_of_target_reaches hN.acyclic (mem_belowSet.1 hft) hu)

theorem good_top_of_prod_ne_zero (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {e : E} {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top ≠ 0) : IsGoodForest (top e) :=
  (frontier_of_prod_ne_zero hN hinj (downClosed_belowSet e) h).good_top e (target_mem_belowSet e)

/-- The lineages at the top of `e` are those injected below `e`. -/
theorem lineages_top_of_prod_ne_zero (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj) {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top ≠ 0) (x : X) :
    x ∈ lineages (top e) ↔ ∃ u ∈ belowSet N e, x ∈ lineages (inj u) := by
  have hF := frontier_of_prod_ne_zero hN hinj (downClosed_belowSet e) h
  constructor
  · intro hx
    exact (hF.mem x).1 ⟨e, target_mem_belowSet e, source_notMem_belowSet hN e, hx⟩
  · intro hx
    obtain ⟨f, hft, hfs, hxf⟩ := (hF.mem x).2 hx
    by_cases hfe : f = e
    · exact hfe ▸ hxf
    · rw [frontier_top_eq_empty hN hdom hF hft hfs hfe] at hxf
      simp at hxf

omit [Fintype E] [Fintype X] in
/-- Lifting what is below `e` to the forest at the top of `e` keeps the injected forests valid. -/
theorem validInj_liftInj {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {e : E} {F : Finset (Finset X)} (hF : IsGoodForest F)
    (hlin : ∀ x ∈ lineages F, ∃ u ∈ belowSet N e, x ∈ lineages (inj u)) :
    ValidInj (liftInj N e inj F) := by
  have hsep : ∀ x, x ∈ lineages F → ∀ v, v ∉ belowSet N e → x ∉ lineages (inj v) := by
    intro x hx v hv hxv
    obtain ⟨u, hu, hxu⟩ := hlin x hx
    have huv : u ≠ v := fun h => hv (h ▸ hu)
    exact disjoint_left.1 (hinj.disj u v huv) hxu hxv
  refine ⟨fun v => ?_, fun u v huv => disjoint_left.2 fun x hxu hxv => ?_⟩
  · unfold liftInj
    refine IsGoodForest.union ?_ ?_ (disjoint_left.2 fun x hx hx' => ?_)
    · split_ifs
      · exact isGoodForest_empty
      · exact hinj.good v
    · split_ifs
      · exact hF
      · exact isGoodForest_empty
    · by_cases hv : v ∈ belowSet N e
      · simp [hv] at hx
      · by_cases hvs : v = N.graph.source e
        · simp only [hv, ↓reduceIte] at hx
          simp only [hvs, ↓reduceIte] at hx'
          exact hsep x hx' v hv hx
        · simp [hvs] at hx'
  · rcases (mem_lineages_liftInj x).1 hxu with ⟨hu, hxu'⟩ | ⟨rfl, hxu'⟩ <;>
      rcases (mem_lineages_liftInj x).1 hxv with ⟨hv, hxv'⟩ | ⟨rfl, hxv'⟩
    · exact disjoint_left.1 (hinj.disj u v huv) hxu' hxv'
    · exact hsep x hxv' u hu hxu'
    · exact hsep x hxu' v hv hxv'
    · exact huv rfl

/-! ### Splitting the weight -/

theorem injWeight_eq_mul (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (e : E)
    (bot top : E → Finset (Finset X)) :
    injWeight N θ ρ inj bot top =
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
        ∏ v ∈ (univ.erase N.root) \ belowSet N e, vertexWeight N θ ρ inj v bot top := by
  unfold injWeight
  rw [← prod_sdiff (belowSet_subset_erase hN e), mul_comm]

theorem injDist_eq_sum (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (e : E)
    (G : Finset (Finset X)) :
    injDist N θ ρ inj G = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
        restWeight N θ ρ inj e G bot top := by
  unfold injDist restWeight
  simp only [injWeight_eq_mul hN inj e, mul_assoc]

omit [Fintype X] [DecidableEq X] in
private theorem notMem_compl_arcsBelow {e f : E} (hf : N.graph.target f ∈ belowSet N e) :
    f ∉ (arcsBelow N e)ᶜ := fun h => mem_compl.1 h (mem_arcsBelow.2 hf)

theorem prod_below_overwrite_bot (inj : V → Finset (Finset X)) (e : E)
    (top bot y : E → Finset (Finset X)) :
    ∏ u ∈ belowSet N e, vertexWeight N θ ρ inj u (overwrite (arcsBelow N e)ᶜ bot y) top =
      ∏ u ∈ belowSet N e, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsBelow (hf ▸ hu)) _ _)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem prod_below_overwrite_top (inj : V → Finset (Finset X)) (e : E)
    (bot top y : E → Finset (Finset X)) :
    ∏ u ∈ belowSet N e, vertexWeight N θ ρ inj u bot (overwrite (arcsBelow N e)ᶜ top y) =
      ∏ u ∈ belowSet N e, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl (fun _ _ => rfl)
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsBelow (hf ▸ hu)) _ _)
    (fun f hf => overwrite_of_notMem
      (notMem_compl_arcsBelow (downClosed_belowSet e f (hf ▸ hu))) _ _)

/-- The part above `e` only sees the arcs not entering what is below `e`, and the tops of the arcs
leaving what is below `e`. -/
theorem restWeight_congr (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {e : E}
    {G : Finset (Finset X)} {bot bot' top top' : E → Finset (Finset X)}
    (h1 : ∀ f, f ∉ arcsBelow N e → bot f = bot' f) (h2 : ∀ f, f ∉ arcsBelow N e → top f = top' f)
    (h3 : ∀ f, f ∈ arcsBelow N e → N.graph.source f ∉ belowSet N e → top f = top' f) :
    restWeight N θ ρ inj e G bot top = restWeight N θ ρ inj e G bot' top' := by
  have hch : ∀ v, v ∉ belowSet N e → ∀ f, N.graph.source f = v → top f = top' f := by
    intro v hv f hf
    by_cases hfS : f ∈ arcsBelow N e
    · exact h3 f hfS (hf ▸ hv)
    · exact h2 f hfS
  have hin : ∀ v, v ∉ belowSet N e → ∀ f, N.graph.target f = v → f ∉ arcsBelow N e :=
    fun v hv f hf hfS => hv (hf ▸ mem_arcsBelow.1 hfS)
  unfold restWeight
  rw [arriving_congr rfl (hch _ (root_notMem_belowSet hN e))]
  refine congrArg (· * _) (prod_congr rfl fun v hv => ?_)
  have hv' := (mem_sdiff.1 hv).2
  exact vertexWeight_congr rfl (fun f hf => h1 f (hin v hv' f hf))
    (fun f hf => h2 f (hin v hv' f hf)) (hch v hv')

/-! ### The Markov property -/

/-- The history splits at `e`, up to the number of values of the arcs. -/
theorem card_sq_mul_injDist (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ inj G) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          aboveMass N θ ρ inj e G (top e) := by
  have htop : ∀ bot : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ top : E → Finset (Finset X),
          (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
            restWeight N θ ρ inj e G bot top =
        ∑ top : E → Finset (Finset X), (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          ∑ t : E → Finset (Finset X),
            restWeight N θ ρ inj e G bot (overwrite (arcsBelow N e)ᶜ top t) := fun bot =>
    card_mul_sum_mul (arcsBelow N e)ᶜ _ _ fun top y => prod_below_overwrite_top inj e bot top y
  have hbot : ∀ top : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ bot : E → Finset (Finset X),
          (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
            ∑ t : E → Finset (Finset X),
              restWeight N θ ρ inj e G bot (overwrite (arcsBelow N e)ᶜ top t) =
        ∑ bot : E → Finset (Finset X), (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
            restWeight N θ ρ inj e G (overwrite (arcsBelow N e)ᶜ bot b)
              (overwrite (arcsBelow N e)ᶜ top t) := fun top =>
    card_mul_sum_mul (arcsBelow N e)ᶜ (fun bot => ∏ v ∈ belowSet N e,
        vertexWeight N θ ρ inj v bot top)
      (fun bot => ∑ t : E → Finset (Finset X),
        restWeight N θ ρ inj e G bot (overwrite (arcsBelow N e)ᶜ top t))
      fun bot y => prod_below_overwrite_bot inj e top bot y
  have hpt : ∀ bot top : E → Finset (Finset X),
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
        (∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
          restWeight N θ ρ inj e G (overwrite (arcsBelow N e)ᶜ bot b)
            (overwrite (arcsBelow N e)ᶜ top t)) =
      (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
        aboveMass N θ ρ inj e G (top e) := by
    intro bot top
    by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top = 0
    · rw [hg, zero_mul, zero_mul]
    have hF := frontier_of_prod_ne_zero hN hinj (downClosed_belowSet e) hg
    refine congrArg (_ * ·) ?_
    unfold aboveMass
    refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => restWeight_congr hN ?_ ?_ ?_
    · exact fun f hf => overwrite_of_mem (mem_compl.2 hf) _ _
    · intro f hf
      rw [overwrite_of_mem (mem_compl.2 hf), overwrite_of_notMem hf]
    · intro f hf hfs
      rw [overwrite_of_notMem (notMem_compl_arcsBelow (mem_arcsBelow.1 hf)), overwrite_of_mem hf]
      unfold tauForest
      by_cases hfe : f = e
      · rw [ite_eq_left hfe, hfe]
      · rw [ite_eq_right hfe]
        exact frontier_top_eq_empty hN hdom hF (mem_arcsBelow.1 hf) hfs hfe
  rw [injDist_eq_sum hN inj e G, mul_sum]
  simp only [htop]
  rw [sum_comm, mul_sum]
  simp only [hbot, hpt]
  rw [sum_comm]

omit [Fintype X] in
/-- The forest arriving above `e` is the same when the forest at the top of `e` is injected at its
source. -/
theorem arriving_liftInj (inj : V → Finset (Finset X)) (e : E)
    (F : Finset (Finset X)) (t : E → Finset (Finset X)) {v : V} (hv : v ∉ belowSet N e) :
    arriving N (liftInj N e inj F) (overwrite (arcsBelow N e) t (tauForest e ∅)) v =
      arriving N inj (overwrite (arcsBelow N e) t (tauForest e F)) v := by
  have heS : e ∈ arcsBelow N e := mem_arcsBelow.2 (target_mem_belowSet e)
  have hτ : ∀ f, tauForest e (∅ : Finset (Finset X)) f = ∅ := fun f => by
    unfold tauForest
    split_ifs <;> rfl
  ext C
  simp only [arriving, liftInj, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, hv,
    ↓reduceIte]
  constructor
  · rintro ((h | h) | ⟨f, hf, hC⟩)
    · exact Or.inl h
    · by_cases hve : v = N.graph.source e
      · rw [ite_eq_left hve] at h
        refine Or.inr ⟨e, hve.symm, ?_⟩
        rw [overwrite_of_mem heS]
        simpa [tauForest] using h
      · rw [ite_eq_right hve] at h
        exact absurd h (notMem_empty _)
    · by_cases hfS : f ∈ arcsBelow N e
      · rw [overwrite_of_mem hfS, hτ] at hC
        exact absurd hC (notMem_empty _)
      · rw [overwrite_of_notMem hfS] at hC
        exact Or.inr ⟨f, hf, by rwa [overwrite_of_notMem hfS]⟩
  · rintro (h | ⟨f, hf, hC⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hfS : f ∈ arcsBelow N e
      · rw [overwrite_of_mem hfS] at hC
        unfold tauForest at hC
        split_ifs at hC with hfe
        · refine Or.inl (Or.inr ?_)
          have hve : v = N.graph.source e := by rw [← hf, hfe]
          rwa [ite_eq_left hve]
        · exact absurd hC (notMem_empty _)
      · rw [overwrite_of_notMem hfS] at hC
        exact Or.inr ⟨f, hf, by rwa [overwrite_of_notMem hfS]⟩

/-- The part above `e`, given the forest `F` at its top, is the process with `F` injected at the
source of `e`. -/
theorem aboveMass_liftInj (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (e : E)
    (G F : Finset (Finset X)) :
    aboveMass N θ ρ (liftInj N e inj F) e G ∅ = aboveMass N θ ρ inj e G F := by
  unfold aboveMass restWeight
  refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => ?_
  rw [arriving_liftInj inj e F t (root_notMem_belowSet hN e)]
  refine congrArg (· * _) (prod_congr rfl fun v hv => ?_)
  have hv' := (mem_sdiff.1 hv).2
  unfold vertexWeight
  rw [arriving_liftInj inj e F t hv']
  refine congrArg (_ * ·) (prod_congr rfl fun f hf => ?_)
  have hfS : f ∉ arcsBelow N e := fun h => hv' (mem_arcsInto.1 hf ▸ mem_arcsBelow.1 h)
  rw [overwrite_of_notMem hfS, overwrite_of_notMem hfS]

variable (N X) in
/-- The total mass of the part below `e`, independent of the injected forests. -/
def belowMass (e : E) : ℝ :=
  ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 /
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsBelow N e)) ^ 2

theorem sum_sum_below (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (e : E) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top = belowMass X N e := by
  have h := sum_sum_prod_vertexWeight (θ := θ) (ρ := ρ) hN hθ hρ hinj (downClosed_belowSet e)
    (root_notMem_belowSet hN e)
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  unfold belowMass
  rw [eq_div_iff (pow_ne_zero 2 (pow_ne_zero _ hB.ne')), mul_comm]
  exact h

omit [DecidableEq X] in
omit [DecidableEq X] in
theorem belowMass_pos (e : E) : 0 < belowMass X N e := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  unfold belowMass
  positivity

/-- Above an arc with nothing below it: the forest at the top of `e` is empty. -/
theorem top_eq_empty_of_liftInj (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {e : E}
    {F : Finset (Finset X)} (hl : ValidInj (liftInj N e inj F))
    {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ belowSet N e, vertexWeight N θ ρ (liftInj N e inj F) v bot top ≠ 0) :
    top e = ∅ := by
  have hF := frontier_of_prod_ne_zero hN hl (downClosed_belowSet e) h
  by_contra hne
  obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨x, hx⟩ := (hF.good_top e (target_mem_belowSet e)).1.1 A hA
  obtain ⟨u, hu, hxu⟩ := hF.below e (target_mem_belowSet e) x (mem_lineages.2 ⟨A, hA, hx⟩)
  rw [liftInj_of_mem hN (mem_belowSet.2 hu)] at hxu
  simp at hxu

/-- The process with the forest `F` at `e` injected at the source of `e`, up to the number of values
of the arcs, is the part above `e`. -/
theorem card_sq_mul_injDist_liftInj (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} {e : E} {F : Finset (Finset X)}
    (hl : ValidInj (liftInj N e inj F)) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ (liftInj N e inj F) G) =
      belowMass X N e * aboveMass N θ ρ inj e G F := by
  have hdom : DominatedInj N e (liftInj N e inj F) := fun u hu hne => by
    rw [liftInj_of_mem hN hu] at hne
    simp at hne
  rw [card_sq_mul_injDist hN hl hdom G, ← aboveMass_liftInj hN inj e G F,
    ← sum_sum_below (θ := θ) (ρ := ρ) hN hθ hρ hl e, sum_mul]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ (liftInj N e inj F) v bot top = 0
  · simp [hg]
  · rw [top_eq_empty_of_liftInj hN hl hg]

/-- **The Markov property at an arc.** The process is the mixture, over the part of the history
below `e`, of the process with the forest at the top of `e` injected at its source. -/
theorem belowMass_mul_injDist (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E} (hdom : DominatedInj N e inj)
    (G : Finset (Finset X)) :
    belowMass X N e * injDist N θ ρ inj G =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          injDist N θ ρ (liftInj N e inj (top e)) G := by
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine mul_left_cancel₀ hM (mul_left_cancel₀ hM ?_)
  have h1 := card_sq_mul_injDist (θ := θ) (ρ := ρ) hN hinj hdom G
  calc (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        (belowMass X N e * injDist N θ ρ inj G))
      = belowMass X N e * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
          ((Fintype.card (E → Finset (Finset X)) : ℝ) * injDist N θ ρ inj G)) := by ring
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
            (belowMass X N e * aboveMass N θ ρ inj e G (top e)) := by
        rw [h1, mul_sum]
        refine sum_congr rfl fun bot _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun top _ => ?_
        ring
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
            ((Fintype.card (E → Finset (Finset X)) : ℝ) *
              ((Fintype.card (E → Finset (Finset X)) : ℝ) *
                injDist N θ ρ (liftInj N e inj (top e)) G)) := by
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top = 0
        · simp [hg]
        · congr 1
          refine (card_sq_mul_injDist_liftInj hN hθ hρ ?_ G).symm
          exact validInj_liftInj hinj (good_top_of_prod_ne_zero hN hinj hg)
            fun x hx => (lineages_top_of_prod_ne_zero hN hinj hdom hg x).1 hx
    _ = _ := by
        simp only [mul_sum]
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        ring

/-- The Markov property at an arc, for the mass of a quartet tree. -/
theorem belowMass_mul_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E}
    (hdom : DominatedInj N e inj) (r : QuartetTree X) :
    belowMass X N e * cherryMass N θ ρ inj r =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          cherryMass N θ ρ (liftInj N e inj (top e)) r := by
  unfold cherryMass
  simp only [mul_sum]
  have h : ∀ H : Finset (Finset X), belowMass X N e *
      (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ inj H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top) *
          (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ (liftInj N e inj (top e)) H else 0) := by
    intro H
    split_ifs
    · exact belowMass_mul_injDist hN hθ hρ hinj hdom H
    · simp
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]

/-- A single lineage below `e` moves up to the source of `e`. -/
theorem injDist_eq_lift_singleton (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {e : E}
    (hdom : DominatedInj N e inj) {y : X} (hy : ∃ u ∈ belowSet N e, y ∈ lineages (inj u))
    (hall : ∀ u ∈ belowSet N e, ∀ x ∈ lineages (inj u), x = y) (G : Finset (Finset X)) :
    injDist N θ ρ inj G = injDist N θ ρ (liftInj N e inj {{y}}) G := by
  have hpos := belowMass_pos (N := N) (X := X) e
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [belowMass_mul_injDist hN hθ hρ hinj hdom G,
    ← sum_sum_below (θ := θ) (ρ := ρ) hN hθ hρ hinj e, sum_mul]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top = 0
  · simp [hg]
  have hgood := good_top_of_prod_ne_zero hN hinj hg
  have hlin := lineages_top_of_prod_ne_zero hN hinj hdom hg
  obtain ⟨A₀, hA₀, hyA₀⟩ := mem_lineages.1 ((hlin y).2 hy)
  have hsing := hgood.singleton_mem hA₀ hyA₀
  suffices htop : top e = {{y}} by rw [htop]
  ext A
  rw [mem_singleton]
  constructor
  · intro hA
    obtain ⟨x, hx⟩ := hgood.1.1 A hA
    have hxy : x = y := by
      obtain ⟨u, hu, hxu⟩ := (hlin x).1 (mem_lineages.2 ⟨A, hA, hx⟩)
      exact hall u hu x hxu
    subst hxy
    refine Subset.antisymm (fun z hz => ?_) (singleton_subset_iff.2 hx)
    obtain ⟨u, hu, hzu⟩ := (hlin z).1 (mem_lineages.2 ⟨A, hA, hz⟩)
    exact mem_singleton.2 (hall u hu z hzu)
  · rintro rfl
    exact hsing

/-- Two processes with the same forests below `e`, compared above `e`. -/
theorem cherryMass_eq_of_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj inj' : V → Finset (Finset X)} (hinj : ValidInj inj) (hinj' : ValidInj inj') {e : E}
    (hdom : DominatedInj N e inj) (hdom' : DominatedInj N e inj')
    (hB : ∀ u ∈ belowSet N e, inj u = inj' u) {r r' : QuartetTree X}
    (h : ∀ bot top : E → Finset (Finset X),
      ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top ≠ 0 →
        cherryMass N θ ρ (liftInj N e inj (top e)) r =
          cherryMass N θ ρ (liftInj N e inj' (top e)) r') :
    cherryMass N θ ρ inj r = cherryMass N θ ρ inj' r' := by
  have hpos := belowMass_pos (N := N) (X := X) e
  refine mul_left_cancel₀ hpos.ne' ?_
  rw [belowMass_mul_cherryMass hN hθ hρ hinj hdom, belowMass_mul_cherryMass hN hθ hρ hinj' hdom']
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  have hw : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top =
      ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj' v bot top :=
    prod_congr rfl fun u hu => vertexWeight_congr (hB u hu) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  rw [← hw]
  by_cases hg : ∏ v ∈ belowSet N e, vertexWeight N θ ρ inj v bot top = 0
  · simp [hg]
  · rw [h bot top hg]

end NMSC

end Phylogenetics
