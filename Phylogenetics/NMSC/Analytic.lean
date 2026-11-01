module

public import Phylogenetics.ForMathlib.Analysis.MatrixExponential
public import Phylogenetics.NMSC.Defs
public import Mathlib.Analysis.Analytic.Constructions

/-!
# The concordance factors are analytic in the numerical parameters

The numerical parameters of a network, in the coordinates of Allman et al. (2023): all
edge lengths, and at each reticulation the inheritance probabilities of all parents but a chosen one.
A concordance factor `nmscCF` is a finite sum of products of

* inheritance weights `allocationWeight`, polynomial in the inheritance probabilities,
* transition probabilities `kingmanTransition`, entries of `exp (t • Q)`, entire in the length `t`,
* the constants `kingmanAbsorption`, which depend on no parameter,

and the inheritance probabilities are affine in the coordinates. So it is an entire function of the
coordinates. This holds for every network and every inheritance correlation `ρ`: no hypothesis is needed
for the formula to make sense, and `ρ` enters only as a constant. The polynomial form of `allocationWeight`
holds as written, without `allocationWeight_rho_zero`: its denominator does not depend on `γ`.

## Main results

* `coordMetric`: the parameters at given coordinates, with `coordMetric_length`,
  `coordMetric_inheritance_of_isTreeArc`, `coordMetric_inheritance_of_ne`,
  `coordMetric_inheritance_parent`, `sum_coordMetric_inheritance`.
* `eq_coordMetric`: valid parameters with given coordinates are `coordMetric` at those coordinates.
* `analyticOnNhd_nmscCF`: the concordance factor along any analytic family of parameters is analytic.
* `analyticOnNhd_nmscCF_coordMetric`: the concordance factor is entire in the coordinates.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
-/

@[expose] public noncomputable section

open Finset Phylogenetics.RootedNetwork
open scoped Classical

namespace Phylogenetics

variable {V E X : Type*} [Fintype E]

/-! ### The coordinates -/

/-- The numerical parameters with the edge lengths `ℓ` and the free inheritance probabilities `g`: at a
reticulation, the chosen parent `d` of the vertex takes what the other parents leave. Tree arcs have
inheritance one. -/
def coordMetric (N : RootedNetwork V E X) (d : V → E) (ℓ g : E → ℝ) : MetricData E where
  length := ℓ
  inheritance e :=
    if N.IsHybridArc e then
      if e = d (N.graph.target e) then
        1 - ∑ f ∈ Finset.univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), g f
      else g e
    else 1

variable {N : RootedNetwork V E X} {d : V → E} {ℓ g : E → ℝ} {e : E}

/-- The lengths of `coordMetric` are the coordinates. -/
@[simp] theorem coordMetric_length : (coordMetric N d ℓ g).length = ℓ := rfl

omit [Fintype E] in
/-- A tree arc is not a hybrid arc. -/
theorem not_isHybridArc_of_isTreeArc (he : N.IsTreeArc e) : ¬ N.IsHybridArc e := by
  unfold IsTreeArc at he
  unfold IsHybridArc
  omega

/-- The inheritance of `coordMetric` on an arc that is not a hybrid arc. -/
theorem coordMetric_inheritance_of_not_isHybridArc (he : ¬ N.IsHybridArc e) :
    (coordMetric N d ℓ g).inheritance e = 1 :=
  ite_eq_right he

/-- The inheritance of `coordMetric` on a tree arc. -/
theorem coordMetric_inheritance_of_isTreeArc (he : N.IsTreeArc e) :
    (coordMetric N d ℓ g).inheritance e = 1 :=
  coordMetric_inheritance_of_not_isHybridArc (not_isHybridArc_of_isTreeArc he)

/-- The inheritance of `coordMetric` on a hybrid arc that is not the chosen parent: the coordinate. -/
theorem coordMetric_inheritance_of_ne (he : N.IsHybridArc e) (hd : e ≠ d (N.graph.target e)) :
    (coordMetric N d ℓ g).inheritance e = g e := by
  simp only [coordMetric, ite_eq_left he, ite_eq_right hd]

/-- The inheritance of `coordMetric` on a hybrid arc that is the chosen parent: what the others leave. -/
theorem coordMetric_inheritance_of_eq (he : N.IsHybridArc e) (hd : e = d (N.graph.target e)) :
    (coordMetric N d ℓ g).inheritance e =
      1 - ∑ f ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), g f := by
  simp only [coordMetric, ite_eq_left he, ite_eq_left hd]

/-- The inheritance of `coordMetric` on the chosen parent of a reticulation. -/
theorem coordMetric_inheritance_parent (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v)
    {v : V} (hv : 2 ≤ N.graph.indegree v) :
    (coordMetric N d ℓ g).inheritance (d v) =
      1 - ∑ f ∈ univ.filter (fun f => N.graph.target f = v ∧ f ≠ d v), g f := by
  have ht := hd v hv
  have he : N.IsHybridArc (d v) := by rw [IsHybridArc, ht]; exact hv
  rw [coordMetric_inheritance_of_eq he (by rw [ht]), ht]

/-- A sum over the arcs with the target of `e`, split at `e`. -/
private theorem sum_target_eq_add (γ : E → ℝ) (e : E) :
    (∑ f, if N.graph.target f = N.graph.target e then γ f else 0) =
      γ e + ∑ f ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e), γ f := by
  rw [← Finset.sum_filter, ← Finset.add_sum_erase _ _
    (Finset.mem_filter.2 ⟨Finset.mem_univ e, rfl⟩ :
      e ∈ univ.filter (fun f => N.graph.target f = N.graph.target e))]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The inheritance of `coordMetric` sums to one at each reticulation. -/
theorem sum_coordMetric_inheritance (hd : ∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v)
    {v : V} (hv : 2 ≤ N.graph.indegree v) :
    (∑ e, if N.graph.target e = v then (coordMetric N d ℓ g).inheritance e else 0) = 1 := by
  have ht := hd v hv
  have hsum := sum_target_eq_add (N := N) (coordMetric N d ℓ g).inheritance (d v)
  rw [ht] at hsum
  rw [hsum, coordMetric_inheritance_parent hd hv]
  have hne : ∀ f ∈ univ.filter (fun f => N.graph.target f = v ∧ f ≠ d v),
      (coordMetric N d ℓ g).inheritance f = g f := by
    intro f hf
    obtain ⟨hfv, hfd⟩ := (Finset.mem_filter.1 hf).2
    subst hfv
    exact coordMetric_inheritance_of_ne hv hfd
  rw [Finset.sum_congr rfl hne]
  ring

/-- **The bridge to the coordinates of `RootedNetwork.IsGenericNull`.** Valid parameters whose
lengths and free inheritance probabilities are the coordinates `ℓ`, `g` are `coordMetric` at `ℓ`, `g`. That
`d` chooses a parent at each reticulation is not needed: where it does not, all parents are free. -/
theorem eq_coordMetric {θ : MetricData E} (hθ : N.IsMetric θ) (hℓ : θ.length = ℓ)
    (hg : ∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = g e) :
    θ = coordMetric N d ℓ g := by
  obtain ⟨-, -, htree, -, hsum⟩ := hθ
  suffices hinh : θ.inheritance = (coordMetric N d ℓ g).inheritance from
    congrArg₂ MetricData.mk hℓ hinh
  funext e
  by_cases he : N.IsHybridArc e
  · by_cases hde : e = d (N.graph.target e)
    · rw [coordMetric_inheritance_of_eq he hde]
      have hs := hsum _ he
      rw [sum_target_eq_add θ.inheritance e] at hs
      have hne : ∀ f ∈ univ.filter (fun f => N.graph.target f = N.graph.target e ∧ f ≠ e),
          θ.inheritance f = g f := by
        intro f hf
        obtain ⟨hfv, hfe⟩ := (Finset.mem_filter.1 hf).2
        refine hg f (by rwa [IsHybridArc, hfv]) ?_
        rw [hfv, ← hde]
        exact hfe
      rw [Finset.sum_congr rfl hne] at hs
      linarith
    · rw [coordMetric_inheritance_of_ne he hde, hg e he hde]
  · rw [coordMetric_inheritance_of_not_isHybridArc he]
    refine htree e ?_
    have hpos : 0 < N.graph.indegree (N.graph.target e) :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨e, rfl⟩
    unfold IsHybridArc at he
    unfold IsTreeArc
    omega

/-! ### Analyticity -/

section Analytic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

/-- A function that is analytic when a side condition holds and zero otherwise is analytic. -/
private theorem analyticOnNhd_ite {f : W → ℝ} (c : Prop) [Decidable c]
    (hf : c → AnalyticOnNhd ℝ f s) : AnalyticOnNhd ℝ (fun x => if c then f x else 0) s := by
  by_cases h : c
  · simpa only [ite_eq_left h] using hf h
  · simpa only [ite_eq_right h] using analyticOnNhd_const

/-- `allocationWeight` is analytic along an analytic family of inheritance probabilities: it is a polynomial
in them, at any `ρ`. -/
theorem analyticOnNhd_allocationWeight {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P] (ρ : ℝ)
    {γ : W → P → ℝ} (hγ : ∀ e, AnalyticOnNhd ℝ (fun x => γ x e) s) (a : R → P) :
    AnalyticOnNhd ℝ (fun x => allocationWeight ρ (γ x) a) s := by
  unfold allocationWeight
  refine AnalyticOnNhd.div_const (AnalyticOnNhd.mul analyticOnNhd_const ?_)
  refine Finset.analyticOnNhd_fun_prod _ fun e _ => (hγ e).mul ?_
  refine Finset.analyticOnNhd_fun_prod _ fun j _ => AnalyticOnNhd.add ?_ analyticOnNhd_const
  exact AnalyticOnNhd.mul analyticOnNhd_const (hγ e)

/-- A coordinate of the first factor is analytic. -/
private theorem analyticOnNhd_coord_fst (e : E) :
    AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => x.1 e) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : E => ℝ) e).comp
    (ContinuousLinearMap.fst ℝ (E → ℝ) (E → ℝ))).analyticOnNhd _

/-- A coordinate of the second factor is analytic. -/
private theorem analyticOnNhd_coord_snd (e : E) :
    AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => x.2 e) Set.univ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : E => ℝ) e).comp
    (ContinuousLinearMap.snd ℝ (E → ℝ) (E → ℝ))).analyticOnNhd _

variable (N) in
/-- The inheritance of `coordMetric` is affine in the coordinates. -/
theorem analyticOnNhd_coordMetric_inheritance (d : V → E) (e : E) :
    AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => (coordMetric N d x.1 x.2).inheritance e)
      Set.univ := by
  by_cases he : N.IsHybridArc e
  · by_cases hde : e = d (N.graph.target e)
    · simp only [coordMetric_inheritance_of_eq he hde]
      exact analyticOnNhd_const.sub
        (Finset.analyticOnNhd_fun_sum _ fun f _ => analyticOnNhd_coord_snd f)
    · simp only [coordMetric_inheritance_of_ne he hde]
      exact analyticOnNhd_coord_snd e
  · simp only [coordMetric_inheritance_of_not_isHybridArc he]
    exact analyticOnNhd_const

variable [Fintype V] [Fintype X] [DecidableEq X] (N)

omit [Fintype V] in
/-- `allocationFactor` is analytic along an analytic family of parameters. -/
theorem analyticOnNhd_allocationFactor {θ : W → MetricData E} (ρ : ℝ)
    (hγ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).inheritance e) s)
    (F : Finset (Finset X)) (v : V) (bot : E → Finset (Finset X)) :
    AnalyticOnNhd ℝ (fun x => allocationFactor N (θ x) ρ F v bot) s := by
  unfold allocationFactor
  refine Finset.analyticOnNhd_fun_sum _ fun a _ => analyticOnNhd_ite _ fun _ => ?_
  exact analyticOnNhd_allocationWeight (γ := fun x e => (θ x).inheritance e.val) ρ
    (fun e => hγ e.val) a

/-- `kingmanTransition` is analytic along an analytic family of lengths. -/
theorem analyticOnNhd_kingmanTransition {L : Type*} [Fintype L] [DecidableEq L] {t : W → ℝ}
    (ht : AnalyticOnNhd ℝ t s) (F G : Finset (Finset L)) :
    AnalyticOnNhd ℝ (fun x => kingmanTransition (t x) F G) s := fun x hx =>
  AnalyticAt.comp (g := fun u : ℝ => kingmanTransition u F G) (f := t)
    (Matrix.analyticOnNhd_exp_smul _ F G _ (Set.mem_univ _)) (ht x hx)

/-- `historyWeight` is analytic along an analytic family of parameters. -/
theorem analyticOnNhd_historyWeight {θ : W → MetricData E} (ρ : ℝ)
    (hℓ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).length e) s)
    (hγ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).inheritance e) s)
    (bot top : E → Finset (Finset X)) :
    AnalyticOnNhd ℝ (fun x => historyWeight N (θ x) ρ bot top) s := by
  unfold historyWeight
  exact (Finset.analyticOnNhd_fun_prod _ fun v _ =>
    analyticOnNhd_allocationFactor N ρ hγ _ v bot).mul
      (Finset.analyticOnNhd_fun_prod _ fun e _ => analyticOnNhd_kingmanTransition (hℓ e) _ _)

/-- `geneTreeDist` is analytic along an analytic family of parameters. -/
theorem analyticOnNhd_geneTreeDist {θ : W → MetricData E} (ρ : ℝ)
    (hℓ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).length e) s)
    (hγ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).inheritance e) s) (G : Finset (Finset X)) :
    AnalyticOnNhd ℝ (fun x => geneTreeDist N (θ x) ρ G) s := by
  unfold geneTreeDist
  refine Finset.analyticOnNhd_fun_sum _ fun bot _ => Finset.analyticOnNhd_fun_sum _ fun top _ => ?_
  exact (analyticOnNhd_historyWeight N ρ hℓ hγ bot top).mul analyticOnNhd_const

/-- A concordance factor is analytic along an analytic family of parameters. -/
theorem analyticOnNhd_nmscCF {θ : W → MetricData E} (ρ : ℝ)
    (hℓ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).length e) s)
    (hγ : ∀ e, AnalyticOnNhd ℝ (fun x => (θ x).inheritance e) s) (r : QuartetTree X) :
    AnalyticOnNhd ℝ (fun x => nmscCF N (θ x) ρ r) s := by
  unfold nmscCF
  exact Finset.analyticOnNhd_fun_sum _ fun G _ =>
    analyticOnNhd_ite _ fun _ => analyticOnNhd_geneTreeDist N ρ hℓ hγ G

/-- **The concordance factors are entire in the coordinates**, for every network, every choice `d` of the
left-out coordinates and every inheritance correlation `ρ`; `ρ = 0` is the independent inheritance of Allman et al. (2023). -/
theorem analyticOnNhd_nmscCF_coordMetric (d : V → E) (ρ : ℝ) (r : QuartetTree X) :
    AnalyticOnNhd ℝ (fun x : (E → ℝ) × (E → ℝ) => nmscCF N (coordMetric N d x.1 x.2) ρ r)
      Set.univ :=
  analyticOnNhd_nmscCF N (θ := fun x : (E → ℝ) × (E → ℝ) => coordMetric N d x.1 x.2) ρ
    analyticOnNhd_coord_fst (analyticOnNhd_coordMetric_inheritance N d) r

end Analytic

end Phylogenetics
