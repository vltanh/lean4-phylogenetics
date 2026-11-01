module

public import Phylogenetics.NMSC.Exchangeability
public import Phylogenetics.NMSC.InducedRestrict
public import Phylogenetics.Tree.Splice

/-!
# What lies above a stable ancestor

All the lineages of a set `Q` of taxa pass through a stable ancestor `l` of `Q`. So the process is the
mixture, over the part of the history strictly below `l`, of the process with the forest arriving at
`l` injected at `l` (`sum_sum_mul_injDist_atInj`), the Markov property at a vertex. For four taxa, the
forest arriving at `l` decides the quartet tree if it has a cluster of two lineages, and otherwise it
is the forest of the four singletons, whose three quartet trees are equally likely by exchangeability
(`cherryMass_atInj`). Hence nothing above `l` changes a concordance factor
(`nmscCF_belowNetwork`).

## Main results

* `sum_sum_mul_injDist_atInj`: the Markov property at a stable ancestor.
* `cherryMass_atInj`: the mass of a quartet tree, given the forest arriving at a stable ancestor.
* `nmscCF_belowNetwork`: the concordance factors of a quartet on the part below a stable ancestor.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

/-- The forest `F` injected at the vertex `l`, and nothing elsewhere. -/
def atInj (l : V) (F : Finset (Finset X)) : V → Finset (Finset X) :=
  fun v => if v = l then F else ∅

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem atInj_self (l : V) (F : Finset (Finset X)) : atInj l F l = F := ite_eq_left rfl

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem atInj_of_ne {l v : V} (h : v ≠ l) (F : Finset (Finset X)) : atInj l F v = ∅ :=
  ite_eq_right h

omit [Fintype V] [Fintype E] [Fintype X] in
theorem validInj_atInj [Fintype X] (l : V) {F : Finset (Finset X)} (hF : IsGoodForest F) :
    ValidInj (atInj l F) := by
  refine ⟨fun v => ?_, fun u v huv => ?_⟩
  · by_cases hv : v = l
    · rwa [hv, atInj_self]
    · rw [atInj_of_ne hv]
      exact isGoodForest_empty
  · by_cases hu : u = l
    · have hv : v ≠ l := fun h => huv (hu.trans h.symm)
      rw [atInj_of_ne hv]
      simp
    · rw [atInj_of_ne hu]
      simp

variable (N) in
/-- The arcs entering a vertex strictly below `l`. -/
def arcsStrictBelow (l : V) : Finset E := univ.filter fun e => N.graph.target e ∈ strictBelow N l

omit [Fintype X] [DecidableEq X] in
theorem mem_arcsStrictBelow {l : V} {e : E} :
    e ∈ arcsStrictBelow N l ↔ N.graph.target e ∈ strictBelow N l := by
  simp [arcsStrictBelow]

omit [Fintype X] [DecidableEq X] in
theorem strictBelow_subset_erase (hN : N.IsPhylogenetic) (l : V) :
    strictBelow N l ⊆ univ.erase N.root := fun _ hv =>
  mem_erase.2 ⟨fun h => root_notMem_strictBelow hN l (h ▸ hv), mem_univ _⟩

variable (N θ ρ) in
/-- The factors of the vertices not strictly below `l`, with the root. -/
def aboveWeight (inj : V → Finset (Finset X)) (l : V) (G : Finset (Finset X))
    (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ (univ.erase N.root) \ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
    kingmanAbsorption (arriving N inj top N.root) G

theorem injDist_eq_sum_strictBelow (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (l : V)
    (G : Finset (Finset X)) :
    injDist N θ ρ inj G = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
        aboveWeight N θ ρ inj l G bot top := by
  unfold injDist aboveWeight injWeight
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  rw [← prod_sdiff (strictBelow_subset_erase hN l)]
  ring

omit [Fintype X] [DecidableEq X] in
theorem notMem_compl_arcsStrictBelow {l : V} {f : E} (hf : N.graph.target f ∈ strictBelow N l) :
    f ∉ (arcsStrictBelow N l)ᶜ := fun h => mem_compl.1 h (mem_arcsStrictBelow.2 hf)

theorem prod_strictBelow_overwrite_bot (inj : V → Finset (Finset X)) (l : V)
    (top bot y : E → Finset (Finset X)) :
    ∏ u ∈ strictBelow N l, vertexWeight N θ ρ inj u (overwrite (arcsStrictBelow N l)ᶜ bot y) top =
      ∏ u ∈ strictBelow N l, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsStrictBelow (hf ▸ hu)) _ _)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem prod_strictBelow_overwrite_top (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X)) (l : V)
    (bot top y : E → Finset (Finset X)) :
    ∏ u ∈ strictBelow N l, vertexWeight N θ ρ inj u bot (overwrite (arcsStrictBelow N l)ᶜ top y) =
      ∏ u ∈ strictBelow N l, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl (fun _ _ => rfl)
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsStrictBelow (hf ▸ hu)) _ _)
    (fun f hf => overwrite_of_notMem
      (notMem_compl_arcsStrictBelow (downClosed_strictBelow hN l f (hf ▸ hu))) _ _)

/-- The history splits at `l`, up to the number of values of the arcs. -/
theorem card_sq_mul_injDist_strictBelow (hN : N.IsPhylogenetic) (inj : V → Finset (Finset X))
    (l : V) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ inj G) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
            aboveWeight N θ ρ inj l G (overwrite (arcsStrictBelow N l)ᶜ bot b)
              (overwrite (arcsStrictBelow N l)ᶜ top t) := by
  have htop : ∀ bot : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ top : E → Finset (Finset X),
          (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
            aboveWeight N θ ρ inj l G bot top =
        ∑ top : E → Finset (Finset X), (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          ∑ t : E → Finset (Finset X),
            aboveWeight N θ ρ inj l G bot (overwrite (arcsStrictBelow N l)ᶜ top t) := fun bot =>
    card_mul_sum_mul (arcsStrictBelow N l)ᶜ _ _ fun top y =>
      prod_strictBelow_overwrite_top hN inj l bot top y
  have hbot : ∀ top : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ bot : E → Finset (Finset X),
          (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
            ∑ t : E → Finset (Finset X),
              aboveWeight N θ ρ inj l G bot (overwrite (arcsStrictBelow N l)ᶜ top t) =
        ∑ bot : E → Finset (Finset X), (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
            aboveWeight N θ ρ inj l G (overwrite (arcsStrictBelow N l)ᶜ bot b)
              (overwrite (arcsStrictBelow N l)ᶜ top t) := fun top =>
    card_mul_sum_mul (arcsStrictBelow N l)ᶜ (fun bot => ∏ v ∈ strictBelow N l,
        vertexWeight N θ ρ inj v bot top)
      (fun bot => ∑ t : E → Finset (Finset X),
        aboveWeight N θ ρ inj l G bot (overwrite (arcsStrictBelow N l)ᶜ top t))
      fun bot y => prod_strictBelow_overwrite_bot inj l top bot y
  rw [injDist_eq_sum_strictBelow hN inj l G, mul_sum]
  simp only [htop]
  rw [sum_comm, mul_sum]
  simp only [hbot]
  rw [sum_comm]

/-- The part above `l` only sees the arcs not entering what is strictly below `l`, and the forests
arriving at the vertices not strictly below `l`. -/
theorem aboveWeight_congr (hN : N.IsPhylogenetic) {inj inj' : V → Finset (Finset X)} {l : V}
    {G : Finset (Finset X)} {bot bot' top top' : E → Finset (Finset X)}
    (harr : ∀ v, v ∉ strictBelow N l → arriving N inj top v = arriving N inj' top' v)
    (hb : ∀ f, f ∉ arcsStrictBelow N l → bot f = bot' f)
    (ht : ∀ f, f ∉ arcsStrictBelow N l → top f = top' f) :
    aboveWeight N θ ρ inj l G bot top = aboveWeight N θ ρ inj' l G bot' top' := by
  have hin : ∀ v, v ∉ strictBelow N l → ∀ f, N.graph.target f = v → f ∉ arcsStrictBelow N l :=
    fun v hv f hf hfS => hv (hf ▸ mem_arcsStrictBelow.1 hfS)
  unfold aboveWeight
  rw [harr _ (root_notMem_strictBelow hN l)]
  refine congrArg (· * _) (prod_congr rfl fun v hv => ?_)
  have hv' := (mem_sdiff.1 hv).2
  unfold vertexWeight
  rw [harr v hv', allocationFactor_congr fun f hf => hb f (hin v hv' f hf)]
  refine congrArg (_ * ·) (prod_congr rfl fun f hf => ?_)
  have hf' := hin v hv' f (mem_arcsInto.1 hf)
  rw [hb f hf', ht f hf']

variable (N θ ρ) in
/-- The part of the process above `l`, given the forest `F` arriving at `l`. -/
def aboveAt (l : V) (G F : Finset (Finset X)) : ℝ :=
  ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
    aboveWeight N θ ρ (atInj l F) l G b (overwrite (arcsStrictBelow N l) t fun _ => ∅)

omit [Fintype X] in
/-- The forests arriving above `l` are those of the process with the forest arriving at `l` injected
at `l`, when the arcs entering the part strictly below `l` from elsewhere are empty. -/
theorem arriving_overwrite_eq (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)}
    {l : V} (hsupp : ∀ v, v ∉ strictBelow N l → inj v = ∅) {top : E → Finset (Finset X)}
    (hdom : ∀ f, N.graph.target f ∈ strictBelow N l → N.graph.source f ∉ strictBelow N l →
      N.graph.source f ≠ l → top f = ∅) (t : E → Finset (Finset X)) {v : V}
    (hv : v ∉ strictBelow N l) :
    arriving N inj (overwrite (arcsStrictBelow N l)ᶜ top t) v =
      arriving N (atInj l (arriving N inj top l))
        (overwrite (arcsStrictBelow N l) t fun _ => ∅) v := by
  have hoverA : ∀ f, f ∈ arcsStrictBelow N l → overwrite (arcsStrictBelow N l)ᶜ top t f = top f :=
    fun f hf => overwrite_of_notMem (fun h => mem_compl.1 h hf) _ _
  have hoverN : ∀ f, f ∉ arcsStrictBelow N l → overwrite (arcsStrictBelow N l)ᶜ top t f = t f :=
    fun f hf => overwrite_of_mem (mem_compl.2 hf) _ _
  have h2A : ∀ f, f ∈ arcsStrictBelow N l →
      overwrite (arcsStrictBelow N l) t (fun _ => (∅ : Finset (Finset X))) f = ∅ :=
    fun f hf => overwrite_of_mem hf _ _
  have h2N : ∀ f, f ∉ arcsStrictBelow N l →
      overwrite (arcsStrictBelow N l) t (fun _ => (∅ : Finset (Finset X))) f = t f :=
    fun f hf => overwrite_of_notMem hf _ _
  ext C
  rw [mem_arriving, mem_arriving, hsupp v hv]
  simp only [notMem_empty, false_or]
  by_cases hvl : v = l
  · subst hvl
    rw [atInj_self, mem_arriving, hsupp v hv]
    simp only [notMem_empty, false_or]
    constructor
    · rintro ⟨f, hf, hC⟩
      have hfA : f ∈ arcsStrictBelow N v :=
        mem_arcsStrictBelow.2 (target_mem_strictBelow hN (hf ▸ .refl))
      rw [hoverA f hfA] at hC
      exact Or.inl ⟨f, hf, hC⟩
    · rintro (⟨f, hf, hC⟩ | ⟨f, hf, hC⟩)
      · have hfA : f ∈ arcsStrictBelow N v :=
          mem_arcsStrictBelow.2 (target_mem_strictBelow hN (hf ▸ .refl))
        exact ⟨f, hf, by rwa [hoverA f hfA]⟩
      · have hfA : f ∈ arcsStrictBelow N v :=
          mem_arcsStrictBelow.2 (target_mem_strictBelow hN (hf ▸ .refl))
        rw [h2A f hfA] at hC
        exact absurd hC (notMem_empty _)
  · rw [atInj_of_ne hvl]
    simp only [notMem_empty, false_or]
    refine exists_congr fun f => and_congr_right fun hf => ?_
    by_cases hfA : f ∈ arcsStrictBelow N l
    · rw [hoverA f hfA, h2A f hfA, hdom f (mem_arcsStrictBelow.1 hfA) (hf ▸ hv) (hf ▸ hvl)]
    · rw [hoverN f hfA, h2N f hfA]

/-- The part above `l`, given the forest arriving at `l`. -/
theorem aboveWeight_overwrite_eq (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {l : V}
    (hsupp : ∀ v, v ∉ strictBelow N l → inj v = ∅) {top : E → Finset (Finset X)}
    (hdom : ∀ f, N.graph.target f ∈ strictBelow N l → N.graph.source f ∉ strictBelow N l →
      N.graph.source f ≠ l → top f = ∅) (G : Finset (Finset X)) (bot b t : E → Finset (Finset X)) :
    aboveWeight N θ ρ inj l G (overwrite (arcsStrictBelow N l)ᶜ bot b)
        (overwrite (arcsStrictBelow N l)ᶜ top t) =
      aboveWeight N θ ρ (atInj l (arriving N inj top l)) l G b
        (overwrite (arcsStrictBelow N l) t fun _ => ∅) :=
  aboveWeight_congr hN (fun _ hv => arriving_overwrite_eq hN hsupp hdom t hv)
    (fun f hf => overwrite_of_mem (mem_compl.2 hf) _ _)
    (fun f hf => by
      rw [overwrite_of_mem (mem_compl.2 hf), overwrite_of_notMem hf])

/-- With everything injected at `l`, the part strictly below `l` carries no lineages. -/
theorem top_eq_empty_of_atInj (hN : N.IsPhylogenetic) {l : V} {F : Finset (Finset X)}
    (hF : IsGoodForest F) {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ (atInj l F) v bot top ≠ 0) {f : E}
    (hf : N.graph.target f ∈ strictBelow N l) : top f = ∅ := by
  have hFr := frontier_of_prod_ne_zero hN (validInj_atInj l hF) (downClosed_strictBelow hN l) h
  refine eq_empty_of_forall_notMem fun A hA => ?_
  obtain ⟨x, hx⟩ := (hFr.good_top f hf).1.1 A hA
  obtain ⟨u, hu, hxu⟩ := hFr.below f hf x (mem_lineages.2 ⟨A, hA, hx⟩)
  by_cases hul : u = l
  · subst hul
    obtain ⟨hr, hne⟩ := mem_strictBelow.1 hf
    exact hne (eq_of_reaches_of_reaches hN.acyclic hu hr)
  · rw [atInj_of_ne hul] at hxu
    simp at hxu

variable (N X) in
/-- The total mass of the part strictly below `l`. -/
def strictMass (l : V) : ℝ :=
  ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 /
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsStrictBelow N l)) ^ 2

omit [DecidableEq X] in
theorem strictMass_pos (l : V) : 0 < strictMass X N l := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  unfold strictMass
  positivity

theorem sum_sum_strictBelow_mass (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (l : V) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      ∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top = strictMass X N l := by
  have h := sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj
    (downClosed_strictBelow hN l) (root_notMem_strictBelow hN l)
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  unfold strictMass
  rw [eq_div_iff (pow_ne_zero 2 (pow_ne_zero _ hB.ne')), mul_comm]
  exact h

/-- The process with a forest `F` injected at `l`, up to the number of values of the arcs, is the
part above `l`. -/
theorem card_sq_mul_injDist_atInj (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (l : V) {F : Finset (Finset X)} (hF : IsGoodForest F) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ (atInj l F) G) =
      strictMass X N l * aboveAt N θ ρ l G F := by
  rw [card_sq_mul_injDist_strictBelow hN (atInj l F) l G,
    ← sum_sum_strictBelow_mass hN hθ hρ (validInj_atInj l hF) l, sum_mul]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ (atInj l F) v bot top = 0
  · simp [hg]
  refine congrArg (_ * ·) ?_
  unfold aboveAt
  refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => aboveWeight_congr hN ?_ ?_ ?_
  · intro v _
    refine arriving_congr rfl fun f _ => ?_
    by_cases hfA : f ∈ arcsStrictBelow N l
    · rw [overwrite_of_notMem (fun h => mem_compl.1 h hfA), overwrite_of_mem hfA]
      exact top_eq_empty_of_atInj hN hF hg (mem_arcsStrictBelow.1 hfA)
    · rw [overwrite_of_mem (mem_compl.2 hfA), overwrite_of_notMem hfA]
  · exact fun f hf => overwrite_of_mem (mem_compl.2 hf) _ _
  · intro f hf
    rw [overwrite_of_mem (mem_compl.2 hf), overwrite_of_notMem hf]

/-- **The Markov property at a vertex.** If the injected forests all lie strictly below `l`, and the
lineages leave what is strictly below `l` only through `l`, then the process is the mixture, over the
part of the history strictly below `l`, of the process with the forest arriving at `l` injected at
`l`. -/
theorem sum_sum_mul_injDist_atInj (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {l : V}
    (hsupp : ∀ v, v ∉ strictBelow N l → inj v = ∅)
    (hdom : ∀ bot top : E → Finset (Finset X),
      ∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top ≠ 0 →
        ∀ f, N.graph.target f ∈ strictBelow N l → N.graph.source f ∉ strictBelow N l →
          N.graph.source f ≠ l → top f = ∅) (G : Finset (Finset X)) :
    strictMass X N l * injDist N θ ρ inj G =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          injDist N θ ρ (atInj l (arriving N inj top l)) G := by
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine mul_left_cancel₀ hM (mul_left_cancel₀ hM ?_)
  calc (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        (strictMass X N l * injDist N θ ρ inj G))
      = strictMass X N l * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
          ((Fintype.card (E → Finset (Finset X)) : ℝ) * injDist N θ ρ inj G)) := by ring
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
            ((Fintype.card (E → Finset (Finset X)) : ℝ) *
              ((Fintype.card (E → Finset (Finset X)) : ℝ) *
                injDist N θ ρ (atInj l (arriving N inj top l)) G)) := by
        rw [card_sq_mul_injDist_strictBelow hN inj l G, mul_sum]
        refine sum_congr rfl fun bot _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun top _ => ?_
        by_cases hg : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top = 0
        · simp [hg]
        have hFr := frontier_of_prod_ne_zero hN hinj (downClosed_strictBelow hN l) hg
        have hgood : IsGoodForest (arriving N inj top l) :=
          hFr.good_arriving hinj (fun h => (mem_strictBelow.1 h).2 rfl)
            fun e he => target_mem_strictBelow hN (he ▸ .refl)
        rw [card_sq_mul_injDist_atInj hN hθ hρ l hgood]
        have hab : ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
            aboveWeight N θ ρ inj l G (overwrite (arcsStrictBelow N l)ᶜ bot b)
              (overwrite (arcsStrictBelow N l)ᶜ top t) =
            aboveAt N θ ρ l G (arriving N inj top l) :=
          sum_congr rfl fun b _ => sum_congr rfl fun t _ =>
            aboveWeight_overwrite_eq hN hsupp (hdom bot top hg) G bot b t
        rw [hab]
        ring
    _ = _ := by
        simp only [mul_sum]
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        ring

/-- The Markov property at a vertex, for the mass of a quartet tree. -/
theorem sum_sum_mul_cherryMass_atInj (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {l : V}
    (hsupp : ∀ v, v ∉ strictBelow N l → inj v = ∅)
    (hdom : ∀ bot top : E → Finset (Finset X),
      ∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top ≠ 0 →
        ∀ f, N.graph.target f ∈ strictBelow N l → N.graph.source f ∉ strictBelow N l →
          N.graph.source f ≠ l → top f = ∅) (r : QuartetTree X) :
    strictMass X N l * cherryMass N θ ρ inj r =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          cherryMass N θ ρ (atInj l (arriving N inj top l)) r := by
  unfold cherryMass
  simp only [mul_sum]
  have h : ∀ H : Finset (Finset X), strictMass X N l *
      (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ inj H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ strictBelow N l, vertexWeight N θ ρ inj v bot top) *
          (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ (atInj l (arriving N inj top l)) H else 0) := by
    intro H
    split_ifs
    · exact sum_sum_mul_injDist_atInj hN hθ hρ hinj hsupp hdom H
    · simp
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]

/-! ### Four taxa -/

section Quartet

/-- The mass of the quartet tree `s` given the forest `F` on its four taxa arriving at a vertex: it
is decided if `F` has a cluster of two lineages; otherwise the three quartet trees are equally
likely. -/
def quartetValue (s : QuartetTree X) (F : Finset (Finset X)) : ℝ :=
  if ∃ C ∈ F, #C = 2 then (if ∃ C ∈ F, C ∈ s.val then 1 else 0) else 1 / 3

/-- **The forest arriving at a vertex decides the mass of a quartet tree** on its four lineages, in
the process with that forest injected there. -/
theorem cherryMass_atInj (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (l : V)
    {s : QuartetTree X} {F : Finset (Finset X)} (hF : IsGoodForest F) (hlin : lineages F = s.taxa) :
    cherryMass N θ ρ (atInj l F) s = quartetValue s F := by
  have hinj := validInj_atInj l hF
  unfold quartetValue
  by_cases h : ∃ C ∈ F, #C = 2
  · rw [ite_eq_left h]
    have hval : ∀ C ∈ F, #C = 2 → cherryMass N θ ρ (atInj l F) s = if C ∈ s.val then 1 else 0 := by
      intro C hC hC2
      refine cherryMass_of_mem hN hθ hρ hinj (v := l) (by rwa [atInj_self]) hC2 ?_
      rw [← hlin]
      exact subset_lineages hC
    by_cases h2 : ∃ C ∈ F, C ∈ s.val
    · obtain ⟨C, hC, hCs⟩ := h2
      rw [hval C hC (s.card_of_mem hCs), ite_eq_left hCs, ite_eq_left ⟨C, hC, hCs⟩]
    · obtain ⟨C, hC, hC2⟩ := h
      rw [hval C hC hC2, ite_eq_right fun h' => h2 ⟨C, hC, h'⟩, ite_eq_right h2]
  · rw [ite_eq_right h]
    have hsing := hF.eq_singletons h
    rw [hlin] at hsing
    obtain ⟨a, ha⟩ : s.taxa.Nonempty := card_pos.1 (by rw [s.card_taxa]; omega)
    refine cherryMass_eq_third hN hθ hρ hinj s.card_taxa (fun x => ?_) ha (fun x hx y hy _ _ => ?_)
      (mem_treesOn.2 rfl)
    · constructor
      · rintro ⟨u, hu⟩
        by_cases hul : u = l
        · rw [hul, atInj_self, hlin] at hu
          exact hu
        · rw [atInj_of_ne hul] at hu
          simp at hu
      · intro hx
        exact ⟨l, by rwa [atInj_self, hlin]⟩
    · funext v
      unfold relabelInj
      by_cases hvl : v = l
      · rw [hvl, atInj_self, hsing]
        exact relabelFamily_swap_singletons hx hy
      · rw [atInj_of_ne hvl]
        simp

variable {Q : Finset X} {l : V}

omit [Fintype E] in
/-- No taxon of a set of at least two taxa is at or above a stable ancestor of them. -/
theorem taxaInj_of_notMem_strictBelow (hN : N.IsPhylogenetic) (hnt : (Q : Set X).Nontrivial)
    (hst : N.IsStableAncestor (Q : Set X) l) {v : V} (hv : v ∉ strictBelow N l) :
    taxaInj N Q v = ∅ := by
  refine eq_empty_of_forall_notMem fun A hA => ?_
  obtain ⟨x, hx, rfl, -⟩ := mem_taxaInj.1 hA
  exact hv (mem_strictBelow.2 ⟨hst.reaches_leaf hN hx, hst.leaf_ne hN hnt x⟩)

/-- The lineages leave what is strictly below a stable ancestor through it. -/
theorem top_eq_empty_of_stable (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) v bot top ≠ 0) {f : E}
    (hf : N.graph.target f ∈ strictBelow N l) (hs : N.graph.source f ∉ strictBelow N l)
    (hsl : N.graph.source f ≠ l) : top f = ∅ := by
  have hn : f ∉ N.belowArcs l (Q : Set X) := fun hm =>
    hs (mem_strictBelow.2 ⟨hm.1, hsl⟩)
  exact ((support_strictBelow hN hst h hf).1 hn).2

/-- The forest arriving at a stable ancestor is a binary forest on all the lineages. -/
theorem good_lineages_arriving_stable (hN : N.IsPhylogenetic) (hnt : (Q : Set X).Nontrivial)
    (hst : N.IsStableAncestor (Q : Set X) l) {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) v bot top ≠ 0) :
    IsGoodForest (arriving N (taxaInj N Q) top l) ∧ lineages (arriving N (taxaInj N Q) top l) = Q := by
  have hinj := validInj_taxaInj (N := N) Q
  have hFr := frontier_of_prod_ne_zero hN hinj (downClosed_strictBelow hN l) h
  have hlD : l ∉ strictBelow N l := fun h => (mem_strictBelow.1 h).2 rfl
  have hch : ∀ e, N.graph.source e = l → N.graph.target e ∈ strictBelow N l := fun e he =>
    target_mem_strictBelow hN (he ▸ .refl)
  refine ⟨hFr.good_arriving hinj hlD hch, ?_⟩
  ext x
  rw [mem_lineages_arriving]
  constructor
  · rintro (hx | ⟨e, he, hx⟩)
    · rw [taxaInj_of_notMem_strictBelow hN hnt hst hlD] at hx
      simp at hx
    · obtain ⟨u, -, hxu⟩ := (hFr.mem x).1 ⟨e, hch e he, he ▸ hlD, hx⟩
      exact (mem_lineages_taxaInj.1 hxu).1
  · intro hx
    have hxD : N.leaf x ∈ strictBelow N l :=
      mem_strictBelow.2 ⟨hst.reaches_leaf hN hx, hst.leaf_ne hN hnt x⟩
    obtain ⟨e, het, hes, hxe⟩ := (hFr.mem x).2 ⟨_, hxD, mem_lineages_taxaInj.2 ⟨hx, rfl⟩⟩
    by_cases hsl : N.graph.source e = l
    · exact Or.inr ⟨e, hsl, hxe⟩
    · rw [top_eq_empty_of_stable hN hst h het hes hsl] at hxe
      simp at hxe

/-- **What lies above a stable ancestor does not matter for a quartet tree on four taxa.** -/
theorem strictMass_mul_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hnt : (Q : Set X).Nontrivial) (hst : N.IsStableAncestor (Q : Set X) l) {s : QuartetTree X}
    (hs : s.taxa = Q) :
    strictMass X N l * cherryMass N θ ρ (taxaInj N Q) s =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) v bot top) *
          quartetValue s (arriving N (taxaInj N Q) top l) := by
  rw [sum_sum_mul_cherryMass_atInj hN hθ.isNormalized hρ.1 (validInj_taxaInj Q)
    (fun _ hv => taxaInj_of_notMem_strictBelow hN hnt hst hv)
    (fun _ _ h _ hf hs' hsl => top_eq_empty_of_stable hN hst h hf hs' hsl)]
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ v ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) v bot top = 0
  · simp [hg]
  · obtain ⟨hgood, hlin⟩ := good_lineages_arriving_stable hN hnt hst hg
    rw [cherryMass_atInj hN hθ hρ l hgood (hlin.trans hs.symm)]

end Quartet

/-! ### The induced subgraph -/

section Below

variable {l : V} {Q : Finset X} {hl : l ∈ N.ancestralVertices (Q : Set X)}
  {hleaf : ∀ x ∈ (Q : Set X), N.graph.Reaches l (N.leaf x)}
  [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]

omit [Fintype V] [Fintype E] [Fintype X] [Fintype (Q : Set X)] in
/-- The mass of a quartet tree and of its image. -/
theorem quartetValue_map (s : QuartetTree (Q : Set X)) (F : Finset (Finset (Q : Set X))) :
    quartetValue (s.map Subtype.val_injective) (embedFamily (taxonEmb Q) F) = quartetValue s F := by
  have hmap : ∀ A : Finset (Q : Set X), A.map (taxonEmb Q) = A.image Subtype.val := fun A =>
    Finset.map_eq_image _ _
  have h1 : (∃ C ∈ embedFamily (taxonEmb Q) F, #C = 2) ↔ ∃ C ∈ F, #C = 2 := by
    constructor
    · rintro ⟨C, hC, hC2⟩
      obtain ⟨A, hA, rfl⟩ := mem_embedFamily.1 hC
      exact ⟨A, hA, by rwa [card_map] at hC2⟩
    · rintro ⟨A, hA, hA2⟩
      exact ⟨A.map (taxonEmb Q), map_mem_embedFamily.2 hA, by rwa [card_map]⟩
  have h2 : (∃ C ∈ embedFamily (taxonEmb Q) F, C ∈ (s.map Subtype.val_injective).val) ↔
      ∃ C ∈ F, C ∈ s.val := by
    rw [QuartetTree.map_val]
    constructor
    · rintro ⟨C, hC, hCs⟩
      obtain ⟨A, hA, rfl⟩ := mem_embedFamily.1 hC
      obtain ⟨B, hB, hBA⟩ := mem_image.1 hCs
      rw [hmap] at hBA
      have hBeq : B = A := image_injective Subtype.val_injective hBA
      exact ⟨A, hA, hBeq ▸ hB⟩
    · rintro ⟨A, hA, hAs⟩
      refine ⟨A.map (taxonEmb Q), map_mem_embedFamily.2 hA, mem_image.2 ⟨A, hAs, ?_⟩⟩
      rw [hmap]
  unfold quartetValue
  simp only [h1, h2]

/-- **Concordance factors in the induced subgraph below a stable ancestor** are those of the network,
for a quartet tree on the four taxa `Q`. The part above is removed here, and it does not matter by the exchangeability in
`cherryMass_atInj`. -/
theorem nmscCF_belowNetwork [Fintype (N.belowVertices l (Q : Set X))]
    [Fintype (N.belowArcs l (Q : Set X))] (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (hQ : #Q = 4) (hnt : (Q : Set X).Nontrivial)
    (hst : N.IsStableAncestor (Q : Set X) l) (s : QuartetTree (Q : Set X)) :
    nmscCF (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ s =
      nmscCF N θ ρ (s.map Subtype.val_injective) := by
  have hNL : (N.belowNetwork l (Q : Set X) hl hleaf).IsPhylogenetic :=
    belowNetwork_isPhylogenetic hN hnt hst
  have hθL := belowMetric_isMetric (hl := hl) (hleaf := hleaf) hN hst hNL hθ
  have hcard : Fintype.card (Q : Set X) = 4 := by
    rw [← hQ]
    exact Fintype.card_coe Q
  have hstaxa : s.taxa = univ := eq_univ_of_card _ (by rw [s.card_taxa, hcard])
  have hmaptaxa : (s.map Subtype.val_injective).taxa = Q := by
    rw [QuartetTree.map_taxa, hstaxa]
    ext x
    simp
  have hntL : ((univ : Finset (Q : Set X)) : Set (Q : Set X)).Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnt
    exact ⟨⟨a, ha⟩, by simp, ⟨b, hb⟩, by simp, fun h => hab (congrArg Subtype.val h)⟩
  have hL1 := strictMass_mul_cherryMass (N := N.belowNetwork l (Q : Set X) hl hleaf) hNL hθL hρ hntL
    (root_isStableAncestor _ _) hstaxa
  have hL2 : strictMass (Q : Set X) (N.belowNetwork l (Q : Set X) hl hleaf)
        (N.belowNetwork l (Q : Set X) hl hleaf).root *
        cherryMass (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
          (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) s =
      ∑ b, ∑ t,
        (∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
            (N.belowNetwork l (Q : Set X) hl hleaf).root,
          vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
            (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t) *
          quartetValue s (arriving (N.belowNetwork l (Q : Set X) hl hleaf)
            (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) t
            (N.belowNetwork l (Q : Set X) hl hleaf).root) :=
    hL1.trans (sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => rfl)
  have hm2 : ∑ b, ∑ t,
        (∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
            (N.belowNetwork l (Q : Set X) hl hleaf).root,
          vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
            (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t) =
      strictMass (Q : Set X) (N.belowNetwork l (Q : Set X) hl hleaf)
        (N.belowNetwork l (Q : Set X) hl hleaf).root := by
    have hm1 := sum_sum_strictBelow_mass hNL hθL.isNormalized hρ.1
      (validInj_taxaInj (N := N.belowNetwork l (Q : Set X) hl hleaf) univ)
      (N.belowNetwork l (Q : Set X) hl hleaf).root
    refine Eq.trans ?_ hm1
    exact sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => rfl
  have hN1 := strictMass_mul_cherryMass hN hθ hρ hnt hst hmaptaxa
  have hB := sum_sum_strictBelow_eq (θ := θ) (ρ := ρ) (hl := hl) (hleaf := hleaf) hN hst hNL
    (quartetValue (s.map Subtype.val_injective))
  have hB1 := sum_sum_strictBelow_eq (θ := θ) (ρ := ρ) (hl := hl) (hleaf := hleaf) hN hst hNL
    (fun _ => 1)
  simp only [mul_one] at hB1
  rw [sum_sum_strictBelow_mass hN hθ.isNormalized hρ.1 (validInj_taxaInj Q), hm2] at hB1
  simp only [quartetValue_map] at hB
  rw [nmscCF_eq_cherryMass hNL hθL hρ, nmscCF_eq_cherryMass hN hθ hρ, hstaxa, hmaptaxa]
  refine (mul_left_cancel₀ (strictMass_pos (N := N) (X := X) l).ne' ?_).symm
  rw [hN1, hB, ← hL2, hB1]
  ring

end Below

end NMSC

end Phylogenetics
