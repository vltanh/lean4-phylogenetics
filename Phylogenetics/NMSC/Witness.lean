module

public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.NMSC.Basic
public import Phylogenetics.NMSC.Factor

/-!
# Concordance factors at boundary parameters

On the boundary of the parameters a hybrid arc of inheritance `0` is effectively deleted, a device of Allman, Baños,
Mitchell, Rhodes (2023). This module proves two facts about the concordance factors at such a point.

* `one_sub_exp_le_nmscCF`: an arc `e` that induces, off the deleted arcs `D`, a split of the quartet
  tree `s` makes the concordance factor of `s` at least `1 - exp (-θ.length e)`. On a history of
  nonzero weight the forests on `D` are empty, so the lineages travel along arcs off `D`. Hence the
  two taxa that `e` dominates reach the bottom of `e`, and the other two taxa never use `e`; two
  lineages coalesce on `e` with probability `1 - exp (-θ.length e)`.
* `nmscCF_withPair`: if at most one taxon of `s` is below a vertex `h` off `D`, whose parents off
  `D` are `k₁, k₂`, then the concordance factor of `s` is affine in the inheritance `(γ, 1 - γ)` of
  `(k₁, k₂)`: a single lineage passes `h`.

## Main results

* `geneTreeDist_nonneg_weak`, `sum_geneTreeDist_weak`, `nmscCF_nonneg_weak`, `sum_nmscCF_weak`: the
  gene tree distribution at boundary parameters.
* `notMem_and_reachesOff_of_mem_lineages_top`: a lineage at the top of an arc came up along arcs off
  `D`.
* `sum_step_mul`, `sum_mul_marginal`: the law of the forests below a set closed under children.
* `one_sub_exp_le_nmscCF`, `nmscCF_le_exp_of_splitOffAt`: the lower bound.
* `RootedNetwork.MetricData.withPair`, `nmscCF_withPair`: the mixture.
* `one_sub_exp_le_nmscCF_withPair_one`, `one_sub_exp_le_nmscCF_withPair_zero`: the lower bound at
  the endpoints of the mixture.

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

/-! ### The gene tree distribution at boundary parameters -/

section GeneTrees

theorem historyWeight_mul_absorption_nonneg_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (bot top : E → Finset (Finset X)) (G : Finset (Finset X)) :
    0 ≤ historyWeight N θ ρ bot top * kingmanAbsorption (arrivingForest N top N.root) G := by
  by_cases h : historyWeight N θ ρ bot top = 0
  · simp [h]
  · exact mul_nonneg (historyWeight_nonneg_weak hθ hρ bot top)
      (kingmanAbsorption_nonneg (good_arrivingForest_root hN h).1.1 G)

theorem geneTreeDist_nonneg_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) (G : Finset (Finset X)) : 0 ≤ geneTreeDist N θ ρ G :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    historyWeight_mul_absorption_nonneg_weak hN hθ hρ _ _ G

/-- The gene tree distribution has total mass one. -/
theorem sum_geneTreeDist_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    [Nonempty X] : ∑ G, geneTreeDist N θ ρ G = 1 := by
  unfold geneTreeDist
  rw [sum_comm, ← sum_sum_historyWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [← mul_sum]
  by_cases h : historyWeight N θ ρ bot top = 0
  · simp [h]
  · rw [kingmanAbsorption_sum (good_arrivingForest_root hN h).1.1, mul_one]

theorem nmscCF_nonneg_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) : 0 ≤ nmscCF N θ ρ s := by
  refine sum_nonneg fun G _ => ?_
  split_ifs
  · exact geneTreeDist_nonneg_weak hN hθ hρ G
  · exact le_rfl

/-- The quartet concordance factors on a set of four taxa sum to one. -/
theorem sum_nmscCF_weak (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {q : Finset X} (hq : q.card = 4) : ∑ r ∈ treesOn q, nmscCF N θ ρ r = 1 := by
  obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < #q)
  have : Nonempty X := ⟨x⟩
  unfold nmscCF
  rw [sum_comm, ← sum_geneTreeDist_weak (θ := θ) (ρ := ρ) hN hθ hρ]
  refine sum_congr rfl fun G _ => ?_
  by_cases hd : geneTreeDist N θ ρ G = 0
  · simp [hd]
  · obtain ⟨hH, hbin⟩ := isBinaryHierarchy_iff_card_childClusters.1 (geneTreeDist_support hN hd)
    obtain ⟨r₀, hr₀, hdisp⟩ := IsBinaryTree.exists_displays ⟨G, hH, rfl, hbin⟩ hq
    rw [sum_eq_single r₀]
    · simp only [hdisp, ↓reduceIte]
    · intro r hr hne
      refine ite_eq_right fun hdr => hne ?_
      exact IsUnrootedTree.displays_unique ⟨G, hH, rfl⟩ hdr hdisp
        ((mem_filter.1 hr).2.trans (mem_filter.1 hr₀).2.symm)
    · exact fun h => absurd hr₀ h

end GeneTrees

/-! ### Reachability off the deleted arcs -/

section Reach

variable {V E X : Type*} {N : RootedNetwork V E X} {D : Set E}

/-- A path off `D` starting below `e` avoids `e`. Unlike `ReachesOff.insert_of_target_reaches`, the
start may be below `e` along deleted arcs only. -/
theorem reachesOff_insert_of_reaches (hA : N.graph.IsAcyclic) {e : E} {a b : V}
    (ha : N.graph.Reaches (N.graph.target e) a) (h : N.ReachesOff D a b) :
    N.ReachesOff (insert e D) a b := by
  induction h with
  | refl => exact .refl
  | @tail b' c hab hstep ih =>
    obtain ⟨f, hf, hs, ht⟩ := hstep
    have hne : f ≠ e := by
      rintro rfl
      exact not_reaches_target_source hA f (hs ▸ ha.trans (ReachesOff.reaches hab))
    exact ih.tail ⟨f, fun h => (Set.mem_insert_iff.1 h).elim hne hf, hs, ht⟩

/-- The other parents of the target of an arc that dominates a taxon off `D` are deleted. -/
theorem mem_of_dominatesOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {e f : E} {x : X}
    (hx : N.DominatesOff D e x) (ht : N.graph.target f = N.graph.target e) (hne : f ≠ e) :
    f ∈ D := by
  by_contra hf
  refine hx ?_
  have h1 : N.ReachesOff (insert e D) N.root (N.graph.source f) :=
    (hD.root_reachesOff hN _).insert_of_not_reaches fun h =>
      not_reaches_target_source hN.acyclic f (ht ▸ h.reaches)
  have h2 : N.ReachesOff (insert e D) (N.graph.target e) (N.leaf x) :=
    reachesOff_insert_of_reaches hN.acyclic .refl (hx.isBelowOff hN hD).2
  exact (h1.tail ⟨f, fun h => (Set.mem_insert_iff.1 h).elim hne hf, rfl, ht⟩).trans h2

end Reach

/-! ### Inheritance zero -/

section Zero

/-- An assignment that uses a parent of inheritance `0` has weight `0`. -/
theorem allocationWeight_eq_zero_of_apply {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P]
    {γ : P → ℝ} (a : R → P) (r : R) (h : γ (a r) = 0) : allocationWeight ρ γ a = 0 := by
  unfold allocationWeight
  rw [prod_eq_zero (mem_image_of_mem a (mem_univ r)) (by rw [h, zero_mul]), mul_zero, zero_div]

omit [Fintype V] in
/-- No root takes a parent of inheritance `0`. -/
theorem bot_eq_empty_of_allocationFactor_ne_zero {F : Finset (Finset X)} {v : V}
    {bot : E → Finset (Finset X)} (h : allocationFactor N θ ρ F v bot ≠ 0) {f : E}
    (hf : N.graph.target f = v) (h0 : θ.inheritance f = 0) : bot f = ∅ := by
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero h
  have hc : ∀ e : {e // N.graph.target e = v},
      bot e.val = forestBelow F ((univ.filter fun r => a r = e).image Subtype.val) := by
    by_contra hne
    exact ha (ite_eq_right hne)
  rw [ite_eq_left hc] at ha
  have hempty : (univ.filter fun r => a r = ⟨f, hf⟩) = ∅ := by
    refine filter_false_of_mem fun r _ hr => ha ?_
    exact allocationWeight_eq_zero_of_apply a r (by rw [hr]; exact h0)
  rw [hc ⟨f, hf⟩, hempty, image_empty]
  ext A
  simp [mem_forestBelow]

omit [Fintype X] in
/-- Kingman's coalescent stays at the empty forest. -/
theorem eq_empty_of_kingmanTransition_empty_ne_zero [Fintype X] {t : ℝ} {G : Finset (Finset X)}
    (h : kingmanTransition t (∅ : Finset (Finset X)) G ≠ 0) : G = ∅ := by
  rw [kingmanTransition_of_card_roots_le_one isForest_empty
    (by simp)] at h
  by_contra hne
  exact h (ite_eq_right hne)

/-- On a history of nonzero weight, the arcs of inheritance `0` are empty and each lineage at the
top of an arc came up along arcs off `D`. -/
theorem notMem_and_reachesOff_of_mem_lineages_top (hN : N.IsPhylogenetic)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Set E}
    (hD : ∀ f ∈ D, θ.inheritance f = 0) {W : Finset V} (hW : DownClosed N W)
    {bot top : E → Finset (Finset X)} (h : ∏ v ∈ W, vertexWeight N θ ρ inj v bot top ≠ 0) {f : E}
    (hf : N.graph.target f ∈ W) {x : X} (hx : x ∈ lineages (top f)) :
    f ∉ D ∧ ∃ u, N.ReachesOff D (N.graph.target f) u ∧ x ∈ lineages (inj u) := by
  induction W using Finset.strongInduction generalizing f x with
  | H W ih =>
    obtain ⟨v, hv, hW', hch⟩ := exists_top_vertex hN hW ⟨_, hf⟩
    rw [← mul_prod_erase W _ hv] at h
    have hrest := right_ne_zero_of_mul h
    have hw := left_ne_zero_of_mul h
    have ih' : ∀ {g : E} {y : X}, N.graph.target g ∈ W.erase v → y ∈ lineages (top g) →
        g ∉ D ∧ ∃ u, N.ReachesOff D (N.graph.target g) u ∧ y ∈ lineages (inj u) :=
      fun hg hy => ih (W.erase v) (erase_ssubset hv) hW' hrest hg hy
    by_cases hfv : N.graph.target f = v
    · have hF := frontier_of_prod_ne_zero hN hinj hW' hrest
      have hg := hF.good_arriving hinj (notMem_erase v W) hch
      obtain ⟨-, -, hmem⟩ := good_of_vertexWeight_ne_zero hg hw
      have hfD : f ∉ D := by
        intro hfD
        have hb := bot_eq_empty_of_allocationFactor_ne_zero (left_ne_zero_of_mul hw) hfv (hD f hfD)
        have hK : kingmanTransition (θ.length f) (bot f) (top f) ≠ 0 :=
          prod_ne_zero_iff.1 (right_ne_zero_of_mul hw) f (mem_arcsInto.2 hfv)
        rw [hb] at hK
        rw [eq_empty_of_kingmanTransition_empty_ne_zero hK] at hx
        simp at hx
      refine ⟨hfD, ?_⟩
      rcases (mem_lineages_arriving inj top v x).1 ((hmem x).1 ⟨f, hfv, hx⟩) with h' | ⟨g, hg1, hg2⟩
      · exact ⟨v, hfv ▸ .refl, h'⟩
      · obtain ⟨hgD, u, hu, hxu⟩ := ih' (hch g hg1) hg2
        exact ⟨u, hfv ▸ .head ⟨g, hgD, hg1, rfl⟩ hu, hxu⟩
    · exact ih' (mem_erase.2 ⟨hfv, hf⟩) hx

end Zero

/-! ### The law of the forests below a set closed under children -/

section Marginal

omit [Fintype V] [Fintype E] in
theorem isForest_assignedForest {F : Finset (Finset X)} (hF : IsForest F) (v : V)
    (a : {A // A ∈ roots F} → {e // N.graph.target e = v}) (f : E) :
    IsForest (assignedForest N F v a f) := by
  unfold assignedForest
  split_ifs
  · exact hF.subset fun _ h => (mem_forestBelow.1 h).1
  · exact isForest_empty

omit [Fintype V] in
/-- The chain at a vertex, as a sum over the assignments of the roots. -/
theorem vertexKernel_eq_sum (v : V) (F : Finset (Finset X)) (ψ : (E → Finset (Finset X)) → ℝ) :
    vertexKernel N θ ρ v F ψ =
      ∑ a, allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a *
        ((∑ t : E → Finset (Finset X),
            (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a f) (t f)) *
              ψ t) *
          (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) := by
  refine sum_allocationFactor_mul F v (fun b => ∑ t : E → Finset (Finset X),
    (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) * ψ t) ?_
  intro b b' h
  refine sum_congr rfl fun t _ => ?_
  congr 1
  exact prod_congr rfl fun f hf => by rw [h f hf]

omit [Fintype V] in
/-- The chain at a vertex has total mass one, up to the number of values of the other arcs. -/
theorem vertexKernel_const (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) {v : V}
    (hv : v ≠ N.root) {F : Finset (Finset X)} (hF : IsForest F) (c : ℝ) :
    vertexKernel N θ ρ v F (fun _ => c) =
      c * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 := by
  rw [vertexKernel_eq_sum]
  have h : ∀ a : {A // A ∈ roots F} → {e // N.graph.target e = v},
      (∑ t : E → Finset (Finset X),
        (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (assignedForest N F v a f) (t f)) * c) =
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ * c := fun a => by
    rw [← sum_mul, sum_prod_of_sum_eq_one _ _ fun f _ =>
      kingmanTransition_sum (isForest_assignedForest hF v a f) _]
  simp only [h]
  rw [← sum_mul, sum_allocationWeight hρ (sum_inheritance_weak hN hθ hv)]
  ring

omit [Fintype V] [Fintype X] [DecidableEq X] in
theorem card_filter_target_mem {W : Finset V} {v : V} (hv : v ∈ W) :
    #(univ.filter fun e => N.graph.target e ∈ W) =
      #(univ.filter fun e => N.graph.target e ∈ W.erase v) + #(arcsInto N v) := by
  have hdis : Disjoint (univ.filter fun e => N.graph.target e ∈ W.erase v) (arcsInto N v) :=
    disjoint_left.2 fun e he he' =>
      notMem_erase v W (mem_arcsInto.1 he' ▸ (mem_filter.1 he).2)
  rw [← card_union_of_disjoint hdis]
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_arcsInto, mem_erase]
  constructor
  · intro he
    by_cases h : N.graph.target e = v
    · exact Or.inr h
    · exact Or.inl ⟨h, he⟩
  · rintro (⟨-, he⟩ | he)
    · exact he
    · exact he ▸ hv

omit [Fintype V] [DecidableEq X] in
/-- The number of values of the arcs. -/
theorem card_fun_arcs (v : V) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) =
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v) *
        (Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ := by
  rw [← pow_add, card_add_card_compl, Fintype.card_fun, Nat.cast_pow]

/-- The topmost vertex of `insert v D` sums out of a test function of the forests at the arcs
entering `D`. -/
theorem sum_step_mul (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D) {v : V}
    (hvD : v ∉ D) (hv : v ≠ N.root) (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D)
    (φ : (E → Finset (Finset X)) → ℝ)
    (hφ : ∀ t t', (∀ f, N.graph.target f ∈ D → t f = t' f) → φ t = φ t') :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hB.ne')
  have hstep := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD hvD hch φ
  have hterm : ∀ bot top : E → Finset (Finset X),
      (∏ u ∈ D, vertexWeight N θ ρ inj u bot top) *
          vertexKernel N θ ρ v (arriving N inj top v)
            (fun t => φ (overwrite (arcsInto N v) top t)) =
        c * ((∏ u ∈ D, vertexWeight N θ ρ inj u bot top) * φ top) := by
    intro bot top
    by_cases hg : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hg]
    have hF := (frontier_of_prod_ne_zero hN hinj hD hg).good_arriving hinj hvD hch
    have hconst : (fun t => φ (overwrite (arcsInto N v) top t)) = fun _ => φ top := by
      funext t
      exact hφ _ _ fun f hf => overwrite_of_notMem (notMem_arcsInto_of_mem hf hvD) _ _
    rw [hconst, vertexKernel_const hN hθ hρ hv hF.1]
    ring
  simp only [hterm] at hstep
  simp only [← mul_sum] at hstep
  refine mul_left_cancel₀ hc0 ?_
  rw [← hstep, card_fun_arcs (N := N) v, hc]
  ring

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- A vertex of `W₂` outside `W₁` without an ancestor there. -/
theorem exists_top_vertex_sdiff (hN : N.IsPhylogenetic) {W₁ W₂ : Finset V} (hW₁ : DownClosed N W₁)
    (hW₂ : DownClosed N W₂) (hne : (W₂ \ W₁).Nonempty) :
    ∃ v ∈ W₂ \ W₁, DownClosed N (W₂.erase v) ∧
      ∀ e, N.graph.source e = v → N.graph.target e ∈ W₂.erase v := by
  have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨hN.acyclic⟩
  have hwf : WellFounded (Relation.TransGen N.graph.Adj) :=
    Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨v, hv, hmin⟩ := hwf.has_min ((W₂ \ W₁ : Finset V) : Set V) hne
  have hv' : v ∈ W₂ \ W₁ := hv
  obtain ⟨hv2, hv1⟩ := mem_sdiff.1 hv'
  refine ⟨v, hv', fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨hne', hs⟩ := mem_erase.1 he
    refine mem_erase.2 ⟨fun ht => ?_, hW₂ e hs⟩
    have hs1 : N.graph.source e ∉ W₁ := fun h => hv1 (ht ▸ hW₁ e h)
    exact hmin _ (mem_sdiff.2 ⟨hs, hs1⟩) (Relation.TransGen.single ⟨e, rfl, ht⟩)
  · refine mem_erase.2 ⟨fun ht => ?_, hW₂ e (he ▸ hv2)⟩
    exact source_ne_target hN e (he.trans ht.symm)

/-- **The law of the forests below `W₁`** is the same in the process on a larger set `W₂` closed
under children, up to the number of values of the arcs. -/
theorem sum_mul_marginal (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {W₁ W₂ : Finset V}
    (hW₁ : DownClosed N W₁) (hW₂ : DownClosed N W₂) (hsub : W₁ ⊆ W₂) (hroot : N.root ∉ W₂)
    (φ : (E → Finset (Finset X)) → ℝ)
    (hφ : ∀ t t', (∀ f, N.graph.target f ∈ W₁ → t f = t' f) → φ t = φ t') :
    ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ W₂)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ W₂, vertexWeight N θ ρ inj u bot top) * φ top =
      ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈ W₁)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ W₁, vertexWeight N θ ρ inj u bot top) * φ top := by
  induction W₂ using Finset.strongInduction with
  | H W₂ ih =>
    by_cases hne : (W₂ \ W₁).Nonempty
    · obtain ⟨v, hv, hD', hch⟩ := exists_top_vertex_sdiff hN hW₁ hW₂ hne
      obtain ⟨hv2, hv1⟩ := mem_sdiff.1 hv
      have hsub' : W₁ ⊆ W₂.erase v := fun x hx =>
        mem_erase.2 ⟨fun h => hv1 (h ▸ hx), hsub hx⟩
      have hstep := sum_step_mul hN hθ hρ hinj hD' (notMem_erase v W₂)
        (fun h => hroot (h ▸ hv2)) hch φ fun t t' h => hφ t t' fun f hf => h f (hsub' hf)
      rw [insert_erase hv2] at hstep
      rw [← ih _ (erase_ssubset hv2) hD' hsub' (fun h => hroot (mem_of_mem_erase h)), ← hstep,
        card_filter_target_mem hv2, pow_add]
      ring
    · have : W₂ = W₁ :=
        Subset.antisymm (sdiff_eq_empty_iff_subset.1 (not_nonempty_iff_eq_empty.1 hne)) hsub
      rw [this]

/-- The kernel at the topmost vertex of `insert v D` bounds the mass of a test function from
below. -/
theorem le_sum_of_le_vertexKernel (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) {v : V} (hvD : v ∉ D)
    (hch : ∀ e, N.graph.source e = v → N.graph.target e ∈ D) (φ : (E → Finset (Finset X)) → ℝ)
    (hnn : ∀ bot top : E → Finset (Finset X), 0 ≤ ∏ u ∈ D, vertexWeight N θ ρ inj u bot top)
    {c₀ : ℝ}
    (hκ : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ inj u bot top ≠ 0 →
      c₀ * ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 ≤
        vertexKernel N θ ρ v (arriving N inj top v) fun t => φ (overwrite (arcsInto N v) top t)) :
    c₀ * ((Fintype.card (Finset (Finset X)) : ℝ) ^ Fintype.card E) ^ 2 ≤
      ((Fintype.card (Finset (Finset X)) : ℝ) ^
          #(univ.filter fun e => N.graph.target e ∈ insert v D)) ^ 2 *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top := by
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hBdef
  have hstep := card_sq_mul_sum_insert (θ := θ) (ρ := ρ) (inj := inj) hD hvD hch φ
  set X₀ := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    ∏ u ∈ D, vertexWeight N θ ρ inj u bot top with hX₀
  have h₀ : (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 * X₀ =
      (B ^ Fintype.card E) ^ 2 :=
    sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj hD hroot
  have hY : c₀ * (B ^ #(arcsInto N v)ᶜ) ^ 2 * X₀ ≤
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top) := by
    rw [hstep, hX₀, mul_sum]
    refine sum_le_sum fun bot _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun top _ => ?_
    by_cases hg : ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = 0
    · simp [hg]
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hκ bot top hg) (hnn bot top)
  have hcard : #(univ.filter fun e => N.graph.target e ∈ insert v D) =
      #(univ.filter fun e => N.graph.target e ∈ D) + #(arcsInto N v) := by
    have := card_filter_target_mem (N := N) (W := insert v D) (v := v) (mem_insert_self _ _)
    rwa [erase_insert hvD] at this
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) = B ^ Fintype.card E := by
    rw [Fintype.card_fun, Nat.cast_pow]
  have hE : B ^ Fintype.card E = B ^ #(arcsInto N v) * B ^ #(arcsInto N v)ᶜ :=
    hM.symm.trans (card_fun_arcs (N := N) (X := X) v)
  rw [hcard, pow_add]
  set Z := ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
    (∏ u ∈ insert v D, vertexWeight N θ ρ inj u bot top) * φ top
  have hS : 0 < (B ^ #(arcsInto N v)ᶜ) ^ 2 := by positivity
  refine le_of_mul_le_mul_right ?_ hS
  have hA : 0 ≤ (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hY hA
  rw [hM] at h1
  calc c₀ * (B ^ Fintype.card E) ^ 2 * (B ^ #(arcsInto N v)ᶜ) ^ 2
      = (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
          (c₀ * (B ^ #(arcsInto N v)ᶜ) ^ 2 * X₀) := by rw [← h₀]; ring
    _ ≤ (B ^ #(univ.filter fun e => N.graph.target e ∈ D)) ^ 2 *
          (B ^ Fintype.card E * (B ^ Fintype.card E * Z)) := h1
    _ = _ := by rw [hE]; ring

end Marginal

/-! ### Two lineages along an arc -/

section Kernel

omit [Fintype X] in
theorem card_eq_one_of_mem_of_notMem {G : Finset (Finset X)} {P : Finset X}
    (hG : IsForest G) (hP : lineages G = P) (hP2 : #P = 2) (hPG : P ∉ G) {A : Finset X}
    (hA : A ∈ G) : #A = 1 := by
  have hsub : A ⊂ P := (hP ▸ subset_lineages hA : A ⊆ P).ssubset_of_ne fun h => hPG (h ▸ hA)
  have h1 := card_lt_card hsub
  have h2 := (hG.1 A hA).card_pos
  omega

/-- Two lineages have merged after a time `t` with probability `1 - exp (-t)`, or at least that much
if they merged before. -/
theorem one_sub_exp_le_sum_kingmanTransition {F : Finset (Finset X)} {P : Finset X}
    (hF : IsGoodForest F) (hP : lineages F = P) (hP2 : #P = 2) (t : ℝ) :
    1 - Real.exp (-t) ≤ ∑ G, kingmanTransition t F G * (if P ∈ G then 1 else 0) := by
  have h1 := kingmanTransition_sum hF.1 t
  have hsplit : ∑ G, kingmanTransition t F G * (if P ∈ G then 1 else 0) +
      ∑ G, kingmanTransition t F G * (if P ∈ G then 0 else 1) = 1 := by
    rw [← sum_add_distrib]
    refine (sum_congr rfl fun G _ => ?_).trans h1
    split_ifs <;> ring
  suffices h : ∑ G, kingmanTransition t F G * (if P ∈ G then 0 else 1) ≤ Real.exp (-t) by linarith
  by_cases hPF : P ∈ F
  · rw [sum_eq_zero]
    · exact (Real.exp_pos _).le
    · intro G _
      by_cases hK : kingmanTransition t F G = 0
      · simp [hK]
      · simp [(kingmanTransition_support_good hF hK).2.1 hPF]
  · rw [sum_eq_single F]
    · have hroots : #(roots F) = 2 := by
        have hs := hF.1.sum_card_roots
        rw [hP, hP2, sum_congr rfl fun R hR =>
          card_eq_one_of_mem_of_notMem hF.1 hP hP2 hPF (roots_subset F hR)] at hs
        simpa using hs
      rw [ite_eq_right hPF, mul_one, kingmanTransition_apply_self hF.1, hroots]
      norm_num
    · intro G _ hne
      by_cases hK : kingmanTransition t F G = 0
      · simp [hK]
      by_cases hPG : P ∈ G
      · simp [hPG]
      exfalso
      obtain ⟨hgood, hFG, hlin⟩ := kingmanTransition_support_good hF hK
      refine hne (Subset.antisymm (fun A hA => ?_) hFG)
      obtain ⟨x, hx⟩ := card_eq_one.1
        (card_eq_one_of_mem_of_notMem hgood.1 (hlin.trans hP) hP2 hPG hA)
      obtain ⟨B, hB, hxB⟩ := mem_lineages.1 (hlin ▸ subset_lineages hA (hx ▸ mem_singleton_self x))
      exact hx ▸ hF.singleton_mem hB hxB
    · exact fun h => absurd (mem_univ F) h

/-- A constant assignment to a parent of inheritance one has weight one. -/
theorem allocationWeight_const_eq_one {R P : Type*} [Fintype R] [Fintype P] [DecidableEq P]
    [Nonempty R] (hρ : 0 ≤ ρ) {γ : P → ℝ} {e : P} (he : γ e = 1) :
    allocationWeight ρ γ (fun _ : R => e) = 1 := by
  rw [allocationWeight_const, he, one_mul]
  simp only [mul_one]
  exact div_self (prod_ne_zero_iff.2 fun i hi => (urn_denominator_pos hρ (mem_Ico.1 hi).1).ne')

omit [Fintype V] in
/-- At a vertex whose parent of positive inheritance is `e`, a forest on two lineages moves to `e`,
where they have merged at the top with probability at least `1 - exp (-θ.length e)`. -/
theorem one_sub_exp_mul_le_vertexKernel (hρ : 0 ≤ ρ) {v : V} {e : E} (he : N.graph.target e = v)
    (h1 : θ.inheritance e = 1) (h0 : ∀ f, N.graph.target f = v → f ≠ e → θ.inheritance f = 0)
    {F : Finset (Finset X)} (hF : IsGoodForest F) {P : Finset X} (hP : lineages F = P)
    (hP2 : #P = 2) :
    (1 - Real.exp (-θ.length e)) *
        ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 ≤
      vertexKernel N θ ρ v F fun t => if P ∈ t e then 1 else 0 := by
  rw [vertexKernel_eq_sum]
  set e' : {e // N.graph.target e = v} := ⟨e, he⟩ with he'
  have hne : Nonempty {A // A ∈ roots F} := by
    obtain ⟨x, hx⟩ : P.Nonempty := card_pos.1 (by omega)
    obtain ⟨A, hA, -⟩ := mem_lineages.1 (hP ▸ hx)
    exact ⟨⟨_, (exists_mem_roots_subset hA).choose_spec.1⟩⟩
  rw [sum_eq_single (fun _ => e')]
  · rw [allocationWeight_const_eq_one hρ (γ := fun e : {e // N.graph.target e = v} =>
      θ.inheritance e.val) h1, one_mul]
    set b := assignedForest N F v fun _ => e' with hb
    have hbe : b e = F := by
      simp only [hb, assignedForest, he, ↓reduceDIte]
      have hfil : (univ.filter fun _ : {A // A ∈ roots F} => e' = ⟨e, he⟩) = univ :=
        filter_true_of_mem fun _ _ => rfl
      rw [hfil]
      ext A
      rw [mem_forestBelow]
      constructor
      · exact fun h => h.1
      · intro hA
        obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
        exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩
    have heS : e ∈ arcsInto N v := mem_arcsInto.2 he
    have hinner := sum_prod_mem (arcsInto N v) (fun f τ =>
      kingmanTransition (θ.length f) (b f) τ * if f = e then (if P ∈ τ then 1 else 0) else 1)
    have hprod : ∀ t : E → Finset (Finset X),
        ∏ f ∈ arcsInto N v, (kingmanTransition (θ.length f) (b f) (t f) *
            if f = e then (if P ∈ t f then 1 else 0) else 1) =
          (∏ f ∈ arcsInto N v, kingmanTransition (θ.length f) (b f) (t f)) *
            if P ∈ t e then 1 else 0 := fun t => by
      rw [prod_mul_distrib, prod_ite_eq' _ e, ite_eq_left heS]
    simp only [hprod] at hinner
    rw [hinner, prod_eq_single_of_mem e heS fun f _ hfe => by
      simp only [hfe, ↓reduceIte, mul_one]
      exact kingmanTransition_sum (isForest_assignedForest hF.1 v _ f) _]
    simp only [↓reduceIte, hbe]
    have hp := one_sub_exp_le_sum_kingmanTransition hF hP hP2 (θ.length e)
    have hc : 0 ≤ ((Fintype.card (Finset (Finset X)) : ℝ) ^ #(arcsInto N v)ᶜ) ^ 2 := by positivity
    calc _ ≤ _ := mul_le_mul_of_nonneg_right hp hc
      _ = _ := by ring
  · intro a _ ha
    obtain ⟨r, hr⟩ : ∃ r, a r ≠ e' := Function.ne_iff.1 ha
    rw [allocationWeight_eq_zero_of_apply a r (h0 _ (a r).property fun h => hr (Subtype.ext h)),
      zero_mul]
  · exact fun h => absurd (mem_univ _) h

end Kernel

/-! ### The lower bound -/

section LowerBound

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem downClosed_belowSet_erase [Fintype V] (hN : N.IsPhylogenetic) (e : E) :
    DownClosed N ((belowSet N e).erase (N.graph.target e)) := fun f hf => by
  obtain ⟨-, hs⟩ := mem_erase.1 hf
  refine mem_erase.2 ⟨fun ht => ?_, downClosed_belowSet e f hs⟩
  exact not_reaches_target_source hN.acyclic f (ht ▸ mem_belowSet.1 hs)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem target_mem_belowSet_erase [Fintype V] (hN : N.IsPhylogenetic) {e f : E}
    (hs : N.graph.source f = N.graph.target e) :
    N.graph.target f ∈ (belowSet N e).erase (N.graph.target e) :=
  mem_erase.2 ⟨fun ht => source_ne_target hN f (hs.trans ht.symm),
    downClosed_belowSet e f (hs ▸ target_mem_belowSet e)⟩

/-- Off the deleted arcs, the lineages arriving at the target of an arc `e` are those of the taxa
that `e` dominates, when the other taxa are not below `e`. -/
theorem lineages_arriving_eq (hN : N.IsPhylogenetic) {D : Set E} (hDel : N.IsDeletion D)
    (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {e : E} (he : e ∉ D) {Y P : Finset X} (hPY : P ⊆ Y)
    (hdom : ∀ x ∈ P, N.DominatesOff D e x) (hQ : ∀ x ∈ Y \ P, ¬ N.IsBelowOff D e x)
    {bot top : E → Finset (Finset X)}
    (h : ∏ u ∈ (belowSet N e).erase (N.graph.target e),
      vertexWeight N θ ρ (taxaInj N Y) u bot top ≠ 0) :
    lineages (arriving N (taxaInj N Y) top (N.graph.target e)) = P := by
  have hW := downClosed_belowSet_erase (N := N) hN e
  have hinj := validInj_taxaInj (N := N) Y
  have hoff : ∀ {f x}, N.graph.target f ∈ (belowSet N e).erase (N.graph.target e) →
      x ∈ lineages (top f) → f ∉ D ∧
        ∃ u, N.ReachesOff D (N.graph.target f) u ∧ x ∈ lineages (taxaInj N Y u) := fun hf hx =>
    notMem_and_reachesOff_of_mem_lineages_top hN hinj hD0 hW h hf hx
  have hin : ∀ {x}, x ∈ Y → N.ReachesOff D (N.graph.target e) (N.leaf x) → x ∈ P := fun hY hr => by
    by_contra hn
    exact hQ _ (mem_sdiff.2 ⟨hY, hn⟩) ⟨he, hr⟩
  ext x
  rw [mem_lineages_arriving]
  constructor
  · rintro (hx | ⟨g, hg, hxg⟩)
    · obtain ⟨hY, hv⟩ := mem_lineages_taxaInj.1 hx
      exact hin hY (hv ▸ .refl)
    · obtain ⟨hgD, u, hu, hxu⟩ := hoff (target_mem_belowSet_erase hN hg) hxg
      obtain ⟨hY, rfl⟩ := mem_lineages_taxaInj.1 hxu
      exact hin hY (.head ⟨g, hgD, hg, rfl⟩ hu)
  · intro hxP
    obtain ⟨-, hr⟩ := (hdom x hxP).isBelowOff hN hDel
    by_cases hlv : N.leaf x = N.graph.target e
    · exact Or.inl (mem_lineages_taxaInj.2 ⟨hPY hxP, hlv⟩)
    have hlW : N.leaf x ∈ (belowSet N e).erase (N.graph.target e) :=
      mem_erase.2 ⟨hlv, mem_belowSet.2 hr.reaches⟩
    have hF := frontier_of_prod_ne_zero hN hinj hW h
    obtain ⟨f, hft, hfs, hxf⟩ := (hF.mem x).2
      ⟨N.leaf x, hlW, mem_lineages_taxaInj.2 ⟨hPY hxP, rfl⟩⟩
    obtain ⟨hfD, u, hu, hxu⟩ := hoff hft hxf
    obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
    by_cases hsv : N.graph.source f = N.graph.target e
    · exact Or.inr ⟨f, hsv, hxf⟩
    exfalso
    refine hdom x hxP ?_
    have h1 : N.ReachesOff (insert e D) N.root (N.graph.source f) :=
      (hDel.root_reachesOff hN _).insert_of_not_reaches fun hr' =>
        hfs (mem_erase.2 ⟨hsv, mem_belowSet.2 hr'.reaches⟩)
    have hfe : f ≠ e := by
      rintro rfl
      exact (mem_erase.1 hft).1 rfl
    have h2 := reachesOff_insert_of_reaches hN.acyclic
      (mem_belowSet.1 (mem_of_mem_erase hft)) hu
    exact (h1.tail ⟨f, fun h => (Set.mem_insert_iff.1 h).elim hfe hfD, rfl, rfl⟩).trans h2

/-- If a cluster is at the top of an arc, it is in the forest above the root. -/
theorem sum_mul_mem_le (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) (e : E) (P : Finset X) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ univ.erase N.root, vertexWeight N θ ρ inj u bot top) *
          (if P ∈ top e then 1 else 0) ≤
      ∑ H, if P ∈ H then injDist N θ ρ inj H else 0 := by
  have hR : ∑ H, (if P ∈ H then injDist N θ ρ inj H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        injWeight N θ ρ inj bot top *
          ∑ H, if P ∈ H then kingmanAbsorption (arriving N inj top N.root) H else 0 := by
    unfold injDist
    have hH : ∀ H : Finset (Finset X), (if P ∈ H then
          ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
            injWeight N θ ρ inj bot top * kingmanAbsorption (arriving N inj top N.root) H else 0) =
        ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          injWeight N θ ρ inj bot top *
            if P ∈ H then kingmanAbsorption (arriving N inj top N.root) H else 0 := by
      intro H
      split_ifs <;> simp
    simp only [hH]
    rw [sum_comm]
    refine sum_congr rfl fun bot _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun top _ => ?_
    rw [mul_sum]
  rw [hR]
  refine sum_le_sum fun bot _ => sum_le_sum fun top _ => ?_
  change injWeight N θ ρ inj bot top * _ ≤ _
  by_cases hw : injWeight N θ ρ inj bot top = 0
  · simp [hw]
  have hnn := injWeight_nonneg_weak hθ hρ inj bot top
  have hgood := (good_arriving_root hN hinj hw).1
  refine mul_le_mul_of_nonneg_left ?_ hnn
  by_cases hP : P ∈ top e
  · have hPr : P ∈ arriving N inj top N.root :=
      mem_arriving_root hN hinj hw (N.graph.source e)
        (mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, rfl⟩, hP⟩))
    rw [ite_eq_left hP, ← kingmanAbsorption_sum hgood.1]
    refine sum_le_sum fun H _ => ?_
    by_cases hA : kingmanAbsorption (arriving N inj top N.root) H = 0
    · simp [hA]
    · rw [ite_eq_left ((kingmanAbsorption_support_good hgood hA).2.1 hPr)]
  · rw [ite_eq_right hP]
    refine sum_nonneg fun H _ => ?_
    split_ifs
    · exact kingmanAbsorption_nonneg hgood.1 H
    · exact le_rfl

/-- **The lower bound.** If, off a set
`D` of arcs of inheritance `0`, the arc `e` induces the split of the quartet tree `s`, then the
concordance factor of `s` is at least the probability that two lineages coalesce along `e`. -/
theorem one_sub_exp_le_nmscCF (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {D : Set E} (hDel : N.IsDeletion D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {e : E}
    {s : QuartetTree X} (hs : N.SplitOffAt D e s) :
    1 - Real.exp (-θ.length e) ≤ nmscCF N θ ρ s := by
  obtain ⟨P, hP, hdom, hQ⟩ := hs
  have hdom' : ∀ x ∈ P, N.DominatesOff D e x := fun x hx => hdom x (by exact_mod_cast hx)
  have hQ' : ∀ x ∈ s.taxa \ P, ¬ N.IsBelowOff D e x := fun x hx => hQ x (by exact_mod_cast hx)
  have hP2 := s.card_of_mem hP
  obtain ⟨p, hp⟩ : P.Nonempty := card_pos.1 (by omega)
  obtain ⟨he, -⟩ := (hdom' p hp).isBelowOff hN hDel
  have hv : N.graph.target e ≠ N.root := target_ne_root hN e
  have h0 : ∀ f, N.graph.target f = N.graph.target e → f ≠ e → θ.inheritance f = 0 :=
    fun f ht hne => hD0 f (mem_of_dominatesOff hN hDel (hdom' p hp) ht hne)
  have h1 : θ.inheritance e = 1 := by
    have h := sum_inheritance_weak hN hθ.isNormalized hv
    rw [Fintype.sum_eq_single (⟨e, rfl⟩ : {f // N.graph.target f = N.graph.target e})
      fun f hf => h0 f.val f.property fun h => hf (Subtype.ext h)] at h
    exact h
  have hinj := validInj_taxaInj (N := N) s.taxa
  set inj := taxaInj N s.taxa with hinjdef
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  let φ : (E → Finset (Finset X)) → ℝ := fun top => if P ∈ top e then 1 else 0
  have hD₀ := downClosed_belowSet_erase (N := N) hN e
  have hge := le_sum_of_le_vertexKernel (θ := θ) (ρ := ρ) (c₀ := 1 - Real.exp (-θ.length e)) hN
    hθ.isNormalized hρ.1 hinj hD₀
    (fun h => root_notMem_belowSet hN e (mem_of_mem_erase h)) (notMem_erase _ _)
    (fun f hf => target_mem_belowSet_erase hN hf) φ
    (fun bot top => prod_nonneg fun u _ => vertexWeight_nonneg_weak hθ hρ inj u bot top)
    (fun bot top hg => by
      have hF := (frontier_of_prod_ne_zero hN hinj hD₀ hg).good_arriving hinj (notMem_erase _ _)
        fun f hf => target_mem_belowSet_erase hN hf
      have hlin := lineages_arriving_eq hN hDel hD0 he (s.subset_taxa hP) hdom' hQ' hg
      have hψ : (fun t => φ (overwrite (arcsInto N (N.graph.target e)) top t)) =
          fun t => if P ∈ t e then 1 else 0 := by
        funext t
        simp only [φ, overwrite_of_mem (mem_arcsInto.2 rfl : e ∈ arcsInto N (N.graph.target e))]
      rw [hψ]
      exact one_sub_exp_mul_le_vertexKernel hρ.1 rfl h1 h0 hF hlin hP2)
  rw [insert_erase (target_mem_belowSet e)] at hge
  have hmar := sum_mul_marginal (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hinj
    (downClosed_belowSet e) (downClosed_erase_root hN) (belowSet_subset_erase hN e)
    (notMem_erase _ _) φ fun t t' h => by
      simp only [φ, h e (target_mem_belowSet e)]
  have hall : (univ.filter fun f => N.graph.target f ∈ univ.erase N.root) = univ :=
    filter_true_of_mem fun f _ => mem_erase.2 ⟨target_ne_root hN f, mem_univ _⟩
  rw [hall, card_univ] at hmar
  rw [← hmar, mul_comm] at hge
  have hfin := le_of_mul_le_mul_left hge (by positivity)
  refine hfin.trans ((sum_mul_mem_le hN hθ hρ hinj e P).trans ?_)
  rw [nmscCF_eq_cherryMass_weak hN hθ.isNormalized hρ.1 s]
  refine sum_le_sum fun H _ => ?_
  by_cases hPH : P ∈ H
  · rw [ite_eq_left hPH, ite_eq_left (⟨P, hP, hPH⟩ : ∃ B ∈ s.val, B ∈ H)]
  · rw [ite_eq_right hPH]
    split_ifs
    · exact injDist_nonneg_weak hN hθ hρ hinj H
    · exact le_rfl

/-- The other quartet trees on the taxa of `s` have a small concordance factor. -/
theorem nmscCF_le_exp_of_splitOffAt (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {D : Set E} (hDel : N.IsDeletion D)
    (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {e : E} {s : QuartetTree X} (hs : N.SplitOffAt D e s)
    {r : QuartetTree X} (hr : r.taxa = s.taxa) (hne : r ≠ s) :
    nmscCF N θ ρ r ≤ Real.exp (-θ.length e) := by
  have hsum := sum_nmscCF_weak (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 s.card_taxa
  have hle : ∑ t ∈ ({r, s} : Finset (QuartetTree X)), nmscCF N θ ρ t ≤
      ∑ t ∈ treesOn s.taxa, nmscCF N θ ρ t := by
    refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_)
      fun t _ _ => nmscCF_nonneg_weak hN hθ hρ t
    rcases mem_insert.1 ht with rfl | ht
    · exact mem_treesOn.2 hr
    · rw [mem_singleton.1 ht]
      exact mem_treesOn.2 rfl
  rw [sum_pair hne, hsum] at hle
  have := one_sub_exp_le_nmscCF hN hθ hρ hDel hD0 hs
  linarith

end LowerBound

/-! ### The mixture -/

section Mixture

/-- The parameters `θ` with inheritance `γ` on the arc `k₁` and `1 - γ` on the arc `k₂`. -/
def _root_.Phylogenetics.RootedNetwork.MetricData.withPair (θ : RootedNetwork.MetricData E)
    (k₁ k₂ : E) (γ : ℝ) : RootedNetwork.MetricData E where
  length := θ.length
  inheritance f := if f = k₁ then γ else if f = k₂ then 1 - γ else θ.inheritance f

omit [Fintype E] in
@[simp] theorem withPair_length (k₁ k₂ : E) (γ : ℝ) : (θ.withPair k₁ k₂ γ).length = θ.length := rfl

omit [Fintype E] in
theorem withPair_inheritance_left (k₁ k₂ : E) (γ : ℝ) :
    (θ.withPair k₁ k₂ γ).inheritance k₁ = γ := by
  simp [RootedNetwork.MetricData.withPair]

omit [Fintype E] in
theorem withPair_inheritance_right {k₁ k₂ : E} (hk : k₁ ≠ k₂) (γ : ℝ) :
    (θ.withPair k₁ k₂ γ).inheritance k₂ = 1 - γ := by
  simp [RootedNetwork.MetricData.withPair, hk.symm]

omit [Fintype E] in
theorem withPair_inheritance_of_ne {k₁ k₂ f : E} (h₁ : f ≠ k₁) (h₂ : f ≠ k₂) (γ : ℝ) :
    (θ.withPair k₁ k₂ γ).inheritance f = θ.inheritance f := by
  simp [RootedNetwork.MetricData.withPair, h₁, h₂]

omit [Fintype E] in
/-- Parameters are the replacement of themselves by their own inheritance. -/
theorem withPair_eq_self {k₁ k₂ : E} {γ : ℝ} (h₁ : θ.inheritance k₁ = γ)
    (h₂ : k₁ ≠ k₂ → θ.inheritance k₂ = 1 - γ) : θ.withPair k₁ k₂ γ = θ := by
  obtain ⟨ℓ, g⟩ := θ
  simp only [RootedNetwork.MetricData.withPair, RootedNetwork.MetricData.mk.injEq, true_and]
  funext f
  by_cases hf : f = k₁
  · subst hf
    simp [← h₁]
  by_cases hf2 : f = k₂
  · subst hf2
    simp only [hf, ↓reduceIte]
    exact (h₂ (Ne.symm hf)).symm
  · simp [hf, hf2]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Two arcs into a vertex are hybrid arcs. -/
theorem isHybridArc_of_target_eq {k₁ k₂ : E} (hk : k₁ ≠ k₂)
    (ht : N.graph.target k₂ = N.graph.target k₁) : N.IsHybridArc k₁ := by
  unfold RootedNetwork.IsHybridArc
  rw [indegree_eq_card]
  exact one_lt_card.2 ⟨k₁, mem_arcsInto.2 rfl, k₂, mem_arcsInto.2 ht, hk⟩

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Replacing the inheritance of the parents `k₁, k₂` of a vertex, whose other parents have
inheritance `0`, keeps the sums. -/
theorem isNormalized_withPair (hθ : N.IsNormalized θ) {k₁ k₂ : E} (hk : k₁ ≠ k₂)
    (ht : N.graph.target k₂ = N.graph.target k₁)
    (h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0)
    (γ : ℝ) : N.IsNormalized (θ.withPair k₁ k₂ γ) := by
  have hh₁ := isHybridArc_of_target_eq (N := N) hk ht
  have hh₂ := isHybridArc_of_target_eq (N := N) hk.symm ht.symm
  refine ⟨fun f hf => ?_, fun v hv => ?_⟩
  · have h₁ : f ≠ k₁ := by
      rintro rfl
      unfold RootedNetwork.IsTreeArc at hf
      unfold RootedNetwork.IsHybridArc at hh₁
      omega
    have h₂ : f ≠ k₂ := by
      rintro rfl
      unfold RootedNetwork.IsTreeArc at hf
      unfold RootedNetwork.IsHybridArc at hh₂
      omega
    rw [withPair_inheritance_of_ne h₁ h₂]
    exact hθ.1 f hf
  · by_cases hvh : v = N.graph.target k₁
    · subst hvh
      rw [sum_eq_add k₁ k₂ hk]
      · simp only [ht, ↓reduceIte]
        rw [withPair_inheritance_left, withPair_inheritance_right hk]
        ring
      · rintro f - ⟨h₁, h₂⟩
        split_ifs with hf
        · rw [withPair_inheritance_of_ne h₁ h₂]
          exact h0 f hf h₁ h₂
        · rfl
      · exact fun h => absurd (mem_univ _) h
      · exact fun h => absurd (mem_univ _) h
    · rw [← hθ.2 v hv]
      refine sum_congr rfl fun f _ => ?_
      split_ifs with hf
      · refine withPair_inheritance_of_ne ?_ ?_ γ
        · rintro rfl
          exact hvh hf.symm
        · rintro rfl
          exact hvh (hf.symm.trans ht)
      · rfl

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- Replacing the inheritance by a probability pair keeps weak parameters weak. -/
theorem isWeakMetric_withPair (hθ : N.IsWeakMetric θ) {k₁ k₂ : E} (hk : k₁ ≠ k₂)
    (ht : N.graph.target k₂ = N.graph.target k₁)
    (h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0)
    {γ : ℝ} (hγ : 0 ≤ γ ∧ γ ≤ 1) : N.IsWeakMetric (θ.withPair k₁ k₂ γ) := by
  refine ⟨hθ.1, fun f hf => ?_, isNormalized_withPair hθ.isNormalized hk ht h0 γ⟩
  by_cases h₁ : f = k₁
  · subst h₁
    rw [withPair_inheritance_left]
    exact hγ.1
  by_cases h₂ : f = k₂
  · subst h₂
    rw [withPair_inheritance_right hk]
    linarith [hγ.2]
  · rw [withPair_inheritance_of_ne h₁ h₂]
    exact hθ.2.1 f hf

omit [Fintype E] in
/-- At the endpoint `(1, 0)` the arc `k₂` is deleted. -/
theorem withPair_one_inheritance_eq_zero {D : Set E} (hD0 : ∀ f ∈ D, θ.inheritance f = 0)
    {k₁ k₂ : E} (hk : k₁ ≠ k₂) (hk₁ : k₁ ∉ D) :
    ∀ f ∈ insert k₂ D, (θ.withPair k₁ k₂ 1).inheritance f = 0 := by
  intro f hf
  by_cases h₂ : f = k₂
  · subst h₂
    rw [withPair_inheritance_right hk, sub_self]
  · have hfD := (Set.mem_insert_iff.1 hf).resolve_left h₂
    rw [withPair_inheritance_of_ne (by rintro rfl; exact hk₁ hfD) h₂]
    exact hD0 f hfD

omit [Fintype E] in
/-- At the endpoint `(0, 1)` the arc `k₁` is deleted. -/
theorem withPair_zero_inheritance_eq_zero {D : Set E} (hD0 : ∀ f ∈ D, θ.inheritance f = 0)
    {k₁ k₂ : E} (hk₂ : k₂ ∉ D) :
    ∀ f ∈ insert k₁ D, (θ.withPair k₁ k₂ 0).inheritance f = 0 := by
  intro f hf
  by_cases h₁ : f = k₁
  · subst h₁
    rw [withPair_inheritance_left]
  · have hfD := (Set.mem_insert_iff.1 hf).resolve_left h₁
    rw [withPair_inheritance_of_ne h₁ (by rintro rfl; exact hk₂ hfD)]
    exact hD0 f hfD

/-- At most one lineage: the allocation is affine in the inheritance. -/
theorem allocationWeight_affine {R P : Type*} [Fintype R] [Subsingleton R] [Fintype P]
    [DecidableEq P] {γ₀ γ₁ γ₂ : P → ℝ} {c : ℝ} (h : ∀ e, γ₀ e = c * γ₁ e + (1 - c) * γ₂ e)
    (a : R → P) :
    allocationWeight ρ γ₀ a = c * allocationWeight ρ γ₁ a + (1 - c) * allocationWeight ρ γ₂ a := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [allocationWeight]
  · obtain ⟨r⟩ := id hR
    have hconst : a = fun _ => a r := funext fun r' => congrArg a (Subsingleton.elim r' r)
    have hcard : Fintype.card R = 1 := Fintype.card_eq_one_iff.2 ⟨r, fun y => Subsingleton.elim y r⟩
    have hform : ∀ γ : P → ℝ, allocationWeight ρ γ a = γ (a r) := fun γ => by
      rw [hconst, allocationWeight_const, hcard]
      simp
    rw [hform, hform, hform, h]

omit [Fintype V] in
/-- At most one lineage arrives at `v`: the allocation is affine in the inheritance. -/
theorem allocationFactor_affine {θ₀ θ₁ θ₂ : RootedNetwork.MetricData E} {c : ℝ} {v : V}
    (h : ∀ f, N.graph.target f = v →
      θ₀.inheritance f = c * θ₁.inheritance f + (1 - c) * θ₂.inheritance f)
    {F : Finset (Finset X)} (hF : IsForest F) (hl : #(lineages F) ≤ 1)
    (bot : E → Finset (Finset X)) :
    allocationFactor N θ₀ ρ F v bot =
      c * allocationFactor N θ₁ ρ F v bot + (1 - c) * allocationFactor N θ₂ ρ F v bot := by
  have hsub : Subsingleton {A // A ∈ roots F} :=
    ⟨fun a b => Subtype.ext (card_le_one.1 (hF.card_roots_le_card_lineages.trans hl) _ a.property _
      b.property)⟩
  unfold allocationFactor
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  split_ifs
  · exact allocationWeight_affine (fun e => h e.val e.property) a
  · ring

omit [Fintype V] in
/-- The allocation at `v` sees the inheritance of the arcs entering `v` only. -/
theorem allocationFactor_congr_inheritance {θ' : RootedNetwork.MetricData E} {v : V}
    (h : ∀ f, N.graph.target f = v → θ.inheritance f = θ'.inheritance f)
    (F : Finset (Finset X)) (bot : E → Finset (Finset X)) :
    allocationFactor N θ ρ F v bot = allocationFactor N θ' ρ F v bot := by
  have hf : (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) =
      fun e => θ'.inheritance e.val := funext fun e => h e.val e.property
  unfold allocationFactor
  rw [hf]

omit [Fintype V] in
/-- The factors of the vertices other than the target of `k₁` do not see the pair. -/
theorem vertexWeight_withPair_of_ne {k₁ k₂ : E} (ht : N.graph.target k₂ = N.graph.target k₁)
    (γ : ℝ) (inj : V → Finset (Finset X)) {u : V} (hu : u ≠ N.graph.target k₁)
    (bot top : E → Finset (Finset X)) :
    vertexWeight N (θ.withPair k₁ k₂ γ) ρ inj u bot top = vertexWeight N θ ρ inj u bot top := by
  unfold vertexWeight
  rw [allocationFactor_congr_inheritance (θ' := θ) fun f hf => ?_]
  · rfl
  · refine withPair_inheritance_of_ne ?_ ?_ γ
    · rintro rfl
      exact hu hf.symm
    · rintro rfl
      exact hu (hf.symm.trans ht)

/-- **The weight of a history is affine in the pair**, if at most one lineage can pass the target of
`k₁`. -/
theorem injWeight_withPair (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)}
    (hinj : ValidInj inj) {D : Set E} (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {k₁ k₂ : E}
    (ht : N.graph.target k₂ = N.graph.target k₁) {a : X}
    (hl : ∀ u x, x ∈ lineages (inj u) → N.ReachesOff D (N.graph.target k₁) u → x = a) (γ : ℝ)
    (bot top : E → Finset (Finset X)) :
    injWeight N (θ.withPair k₁ k₂ γ) ρ inj bot top =
      γ * injWeight N (θ.withPair k₁ k₂ 1) ρ inj bot top +
        (1 - γ) * injWeight N (θ.withPair k₁ k₂ 0) ρ inj bot top := by
  set h := N.graph.target k₁ with hh
  have hmem : h ∈ univ.erase N.root := mem_erase.2 ⟨target_ne_root hN k₁, mem_univ _⟩
  have hrest : ∀ γ' : ℝ, ∏ u ∈ (univ.erase N.root).erase h,
      vertexWeight N (θ.withPair k₁ k₂ γ') ρ inj u bot top =
        ∏ u ∈ (univ.erase N.root).erase h, vertexWeight N θ ρ inj u bot top := fun γ' =>
    prod_congr rfl fun u hu => vertexWeight_withPair_of_ne ht γ' inj (ne_of_mem_erase hu) bot top
  unfold injWeight
  rw [← mul_prod_erase _ _ hmem, ← mul_prod_erase _ _ hmem, ← mul_prod_erase _ _ hmem, hrest, hrest,
    hrest]
  set R := ∏ u ∈ (univ.erase N.root).erase h, vertexWeight N θ ρ inj u bot top with hR
  by_cases hR0 : R = 0
  · simp [hR0]
  -- the vertices strictly below `h`
  have hW := downClosed_belowSet_erase (N := N) hN k₁
  have hsub : (belowSet N k₁).erase h ⊆ (univ.erase N.root).erase h := fun u hu =>
    mem_erase.2 ⟨ne_of_mem_erase hu, belowSet_subset_erase hN k₁ (mem_of_mem_erase hu)⟩
  have hprod : ∏ u ∈ (belowSet N k₁).erase h, vertexWeight N θ ρ inj u bot top ≠ 0 :=
    prod_ne_zero_iff.2 fun u hu => prod_ne_zero_iff.1 hR0 u (hsub hu)
  have hch : ∀ f, N.graph.source f = h → N.graph.target f ∈ (belowSet N k₁).erase h :=
    fun f hf => target_mem_belowSet_erase hN hf
  have hF := (frontier_of_prod_ne_zero hN hinj hW hprod).good_arriving hinj (notMem_erase _ _) hch
  have hlin : #(lineages (arriving N inj top h)) ≤ 1 := by
    refine card_le_one.2 fun x hx y hy => ?_
    have key : ∀ z ∈ lineages (arriving N inj top h), z = a := by
      intro z hz
      rcases (mem_lineages_arriving inj top h z).1 hz with hz | ⟨g, hg, hzg⟩
      · exact hl h z hz .refl
      · obtain ⟨hgD, u, hu, hzu⟩ := notMem_and_reachesOff_of_mem_lineages_top hN hinj hD0 hW hprod
          (hch g hg) hzg
        exact hl u z hzu (.head ⟨g, hgD, hg, rfl⟩ hu)
    rw [key x hx, key y hy]
  have haff := allocationFactor_affine (N := N) (ρ := ρ) (θ₀ := θ.withPair k₁ k₂ γ)
    (θ₁ := θ.withPair k₁ k₂ 1) (θ₂ := θ.withPair k₁ k₂ 0) (c := γ) (v := h) (fun f _ => by
      simp only [RootedNetwork.MetricData.withPair]
      split_ifs <;> ring) hF.1 hlin bot
  unfold vertexWeight
  simp only [withPair_length]
  rw [haff]
  ring

/-- **The mixture.** Let `k₁, k₂` be the
only parents of a vertex off a set `D` of arcs of inheritance `0`, and suppose that at most one
taxon of the quartet tree `s` is below that vertex off `D`. Then the concordance factor of `s` at
inheritance `(γ, 1 - γ)` is the mixture of those at `(1, 0)` and `(0, 1)`, for all real `γ`. Other
taxa may be below the vertex: the concordance factor is read from the lineages of the taxa of `s`
alone. -/
theorem nmscCF_withPair (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) {D : Set E}
    (hD0 : ∀ f ∈ D, θ.inheritance f = 0) {k₁ k₂ : E} (hk : k₁ ≠ k₂)
    (ht : N.graph.target k₂ = N.graph.target k₁)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂)
    (s : QuartetTree X) (a : X)
    (honly : ∀ x ∈ s.taxa, x ≠ a → ¬ N.ReachesOff D (N.graph.target k₁) (N.leaf x)) (γ : ℝ) :
    nmscCF N (θ.withPair k₁ k₂ γ) ρ s =
      γ * nmscCF N (θ.withPair k₁ k₂ 1) ρ s + (1 - γ) * nmscCF N (θ.withPair k₁ k₂ 0) ρ s := by
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 := by
    intro f hf h₁ h₂
    refine hD0 f ?_
    by_contra hfD
    exact (hpar f hf hfD).elim h₁ h₂
  have hnorm := isNormalized_withPair hθ hk ht h0
  simp only [nmscCF_eq_cherryMass_weak hN (hnorm _) hρ s]
  have hinj := validInj_taxaInj (N := N) s.taxa
  have hl : ∀ u x, x ∈ lineages (taxaInj N s.taxa u) →
      N.ReachesOff D (N.graph.target k₁) u → x = a := by
    intro u x hx hr
    obtain ⟨hxs, rfl⟩ := mem_lineages_taxaInj.1 hx
    by_contra hne
    exact honly x hxs hne hr
  unfold cherryMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun H _ => ?_
  split_ifs
  · unfold injDist
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun bot _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun top _ => ?_
    rw [injWeight_withPair hN hinj hD0 ht hl γ bot top]
    ring
  · ring

/-- `one_sub_exp_le_nmscCF` at the endpoint `(1, 0)` of the mixture, where `k₂` is deleted. -/
theorem one_sub_exp_le_nmscCF_withPair_one (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {D : Set E} (hDel : N.IsDeletion D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0)
    {k₁ k₂ : E} (hk : k₁ ≠ k₂) (ht : N.graph.target k₂ = N.graph.target k₁) (hk₁ : k₁ ∉ D)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) {e : E}
    {s : QuartetTree X} (hs : N.SplitOffAt (insert k₂ D) e s) :
    1 - Real.exp (-θ.length e) ≤ nmscCF N (θ.withPair k₁ k₂ 1) ρ s := by
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 :=
    fun f hf h₁ h₂ => hD0 f (by_contra fun hfD => (hpar f hf hfD).elim h₁ h₂)
  exact one_sub_exp_le_nmscCF hN (isWeakMetric_withPair hθ hk ht h0 ⟨zero_le_one, le_rfl⟩) hρ
    (hDel.insert hN hk.symm ht hk₁) (withPair_one_inheritance_eq_zero hD0 hk hk₁) hs

/-- `one_sub_exp_le_nmscCF` at the endpoint `(0, 1)` of the mixture, where `k₁` is deleted. -/
theorem one_sub_exp_le_nmscCF_withPair_zero (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) {D : Set E} (hDel : N.IsDeletion D) (hD0 : ∀ f ∈ D, θ.inheritance f = 0)
    {k₁ k₂ : E} (hk : k₁ ≠ k₂) (ht : N.graph.target k₂ = N.graph.target k₁) (hk₂ : k₂ ∉ D)
    (hpar : ∀ f, N.graph.target f = N.graph.target k₁ → f ∉ D → f = k₁ ∨ f = k₂) {e : E}
    {s : QuartetTree X} (hs : N.SplitOffAt (insert k₁ D) e s) :
    1 - Real.exp (-θ.length e) ≤ nmscCF N (θ.withPair k₁ k₂ 0) ρ s := by
  have h0 : ∀ f, N.graph.target f = N.graph.target k₁ → f ≠ k₁ → f ≠ k₂ → θ.inheritance f = 0 :=
    fun f hf h₁ h₂ => hD0 f (by_contra fun hfD => (hpar f hf hfD).elim h₁ h₂)
  exact one_sub_exp_le_nmscCF hN (isWeakMetric_withPair hθ hk ht h0 ⟨le_rfl, zero_le_one⟩) hρ
    (hDel.insert hN hk ht.symm hk₂) (withPair_zero_inheritance_eq_zero hD0 hk₂) hs

end Mixture

end NMSC

end Phylogenetics
