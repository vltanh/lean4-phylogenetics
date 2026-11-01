module

public import Phylogenetics.Network.InducedMetric
public import Phylogenetics.NMSC.Witness

/-!
# Suppression does not change the gene tree distribution

Suppressing the vertices of indegree one and outdegree one of a network (`RootedNetwork.suppress`),
with the lengths along each chain added (`RootedNetwork.suppressMetric`), does not change the gene
tree distribution: at a chain vertex the allocation is forced and has weight one, and Kingman's
semigroup merges the consecutive arcs.

## Main results

* `NMSC.geneTreeDist_suppress`: the theorem.

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

/-! ### Functions of disjoint sets of coordinates -/

section Coordinates

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

omit [Fintype ι] [DecidableEq ι] [Fintype β] in
/-- A sum over a finite type does not depend on the instance. -/
theorem sum_congr_instance {α : Type*} (i₁ i₂ : Fintype α) (f g : α → ℝ) (h : ∀ a, f a = g a) :
    @Finset.sum _ _ _ (@Finset.univ _ i₁) f = @Finset.sum _ _ _ (@Finset.univ _ i₂) g := by
  obtain rfl := Subsingleton.elim i₁ i₂
  exact sum_congr rfl fun a _ => h a

/-- Functions of complementary sets of coordinates are independent under the uniform measure. -/
theorem card_mul_sum_mul_of_depends (A : Finset ι) (g h : (ι → β) → ℝ)
    (hg : ∀ y y', (∀ i, i ∉ A → y i = y' i) → g y = g y')
    (hh : ∀ y y', (∀ i ∈ A, y i = y' i) → h y = h y') :
    (Fintype.card (ι → β) : ℝ) * ∑ y, g y * h y = (∑ y, g y) * ∑ y, h y := by
  rw [card_mul_sum_mul A g h fun x y => hg _ _ fun i hi => overwrite_of_notMem hi x y, sum_mul]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  exact sum_congr rfl fun y _ => hh _ _ fun i hi => overwrite_of_mem hi x y

theorem card_fun_eq_pow : (Fintype.card (ι → β) : ℝ) = (Fintype.card β : ℝ) ^ Fintype.card ι := by
  rw [Fintype.card_fun, Nat.cast_pow]

/-- The sum of a product of functions of disjoint sets of coordinates is the product of the sums,
up to the number of values of the other coordinates. -/
theorem card_pow_mul_sum_prod [Nonempty β] {κ : Type*} (T : Finset κ) (A : κ → Finset ι)
    (Ω : κ → (ι → β) → ℝ) (c : κ → ℝ)
    (hdisj : ∀ k ∈ T, ∀ k' ∈ T, k ≠ k' → Disjoint (A k) (A k'))
    (hdep : ∀ k ∈ T, ∀ y y', (∀ i ∈ A k, y i = y' i) → Ω k y = Ω k y')
    (hsum : ∀ k ∈ T, (Fintype.card β : ℝ) ^ #(A k) * ∑ y, Ω k y =
      c k * (Fintype.card β : ℝ) ^ Fintype.card ι) :
    (Fintype.card β : ℝ) ^ #(T.biUnion A) * ∑ y, ∏ k ∈ T, Ω k y =
      (∏ k ∈ T, c k) * (Fintype.card β : ℝ) ^ Fintype.card ι := by
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  induction T using Finset.induction_on with
  | empty =>
    simp only [biUnion_empty, card_empty, pow_zero, one_mul, prod_empty, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    exact card_fun_eq_pow
  | insert k T hk ih =>
    have hih := ih (fun a ha b hb => hdisj a (mem_insert_of_mem ha) b (mem_insert_of_mem hb))
      (fun a ha => hdep a (mem_insert_of_mem ha)) (fun a ha => hsum a (mem_insert_of_mem ha))
    have hd : Disjoint (A k) (T.biUnion A) := by
      rw [disjoint_biUnion_right]
      intro a ha
      exact hdisj k (mem_insert_self _ _) a (mem_insert_of_mem ha) fun h => hk (h ▸ ha)
    have hind := card_mul_sum_mul_of_depends (A k) (fun y => ∏ a ∈ T, Ω a y) (Ω k)
      (fun y y' h => prod_congr rfl fun a ha => hdep a (mem_insert_of_mem ha) y y' fun i hi =>
        h i fun hik => disjoint_left.1 hd hik (mem_biUnion.2 ⟨a, ha, hi⟩))
      (hdep k (mem_insert_self _ _))
    rw [card_fun_eq_pow] at hind
    have hsk := hsum k (mem_insert_self _ _)
    rw [biUnion_insert, card_union_of_disjoint hd, prod_insert hk, pow_add]
    refine mul_left_cancel₀ (pow_ne_zero (Fintype.card ι) hB.ne') ?_
    have hrw : ∑ y, ∏ a ∈ insert k T, Ω a y = ∑ y, (∏ a ∈ T, Ω a y) * Ω k y :=
      sum_congr rfl fun y _ => by rw [prod_insert hk, mul_comm]
    rw [hrw]
    calc (Fintype.card β : ℝ) ^ Fintype.card ι * ((Fintype.card β : ℝ) ^ #(A k) *
          (Fintype.card β : ℝ) ^ #(T.biUnion A) * ∑ y, (∏ a ∈ T, Ω a y) * Ω k y)
        = (Fintype.card β : ℝ) ^ #(A k) * (Fintype.card β : ℝ) ^ #(T.biUnion A) *
            ((Fintype.card β : ℝ) ^ Fintype.card ι * ∑ y, (∏ a ∈ T, Ω a y) * Ω k y) := by ring
      _ = ((Fintype.card β : ℝ) ^ #(A k) * ∑ y, Ω k y) *
            ((Fintype.card β : ℝ) ^ #(T.biUnion A) * ∑ y, ∏ a ∈ T, Ω a y) := by
          rw [hind]; ring
      _ = _ := by rw [hsk, hih]; ring

/-- A value at one coordinate. -/
theorem card_mul_sum_ite_coord [Nonempty β] [DecidableEq β] (e : ι) (b : β) (w : ℝ) :
    (Fintype.card β : ℝ) * ∑ y : ι → β, (if y e = b then w else 0) =
      w * (Fintype.card β : ℝ) ^ Fintype.card ι := by
  have h := sum_ite_forall_eq ({e} : Finset ι) (fun _ => b) w
  simp only [mem_singleton, forall_eq] at h
  rw [h, card_compl, card_singleton]
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨e⟩
  obtain ⟨n, hn'⟩ := Nat.exists_eq_add_of_le hn
  rw [hn', Nat.add_sub_cancel_left, pow_add, pow_one]
  ring

end Coordinates

/-! ### Reindexing the allocation -/

section Reindex

/-- `allocationWeight` does not depend on the names of the parents. -/
theorem allocationWeight_equiv_comp {R P P' : Type*} [Fintype R] [Fintype P] [Fintype P']
    [DecidableEq P] [DecidableEq P'] (σ : P' ≃ P) (ρ : ℝ) (γ : P → ℝ) (a : R → P') :
    allocationWeight ρ γ (σ ∘ a) = allocationWeight ρ (γ ∘ σ) a := by
  have him : univ.image (σ ∘ a) = (univ.image a).map σ.toEmbedding := by
    ext e
    simp only [mem_image, mem_univ, true_and, Function.comp, mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨a r, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
  have hc : ∀ e, (univ.filter fun r => (σ ∘ a) r = σ e) = univ.filter fun r => a r = e := by
    intro e
    ext r
    simp
  unfold allocationWeight
  rw [him, card_map, prod_map]
  simp

variable {V₁ E₁ X₁ V₂ E₂ X₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype V₂] [Fintype E₂] [Fintype X₂] [DecidableEq X₂]
  {N₁ : RootedNetwork V₁ E₁ X₁} {N₂ : RootedNetwork V₂ E₂ X₂}
  {θ₁ : RootedNetwork.MetricData E₁} {θ₂ : RootedNetwork.MetricData E₂} {ρ : ℝ}

omit [Fintype V₁] [Fintype V₂] in
/-- The allocation at a vertex of a network, along a bijection of the arcs entering it and of the
roots of the forest arriving there. -/
theorem allocationFactor_eq_of_equiv {F₁ : Finset (Finset X₁)} {F₂ : Finset (Finset X₂)} {v₁ : V₁}
    {v₂ : V₂} {b₁ : E₁ → Finset (Finset X₁)} {b₂ : E₂ → Finset (Finset X₂)}
    (σ : {e // N₂.graph.target e = v₂} ≃ {e // N₁.graph.target e = v₁})
    (τ : {A // A ∈ roots F₂} ≃ {A // A ∈ roots F₁})
    (hγ : ∀ e, θ₂.inheritance e.1 = θ₁.inheritance (σ e).1)
    (hb : ∀ (a : {A // A ∈ roots F₂} → {e // N₂.graph.target e = v₂})
      (e : {e // N₂.graph.target e = v₂}),
      b₂ e.1 = forestBelow F₂ ((univ.filter fun r => a r = e).image Subtype.val) ↔
        b₁ (σ e).1 = forestBelow F₁ ((univ.filter fun r => a (τ.symm r) = e).image Subtype.val)) :
    allocationFactor N₁ θ₁ ρ F₁ v₁ b₁ = allocationFactor N₂ θ₂ ρ F₂ v₂ b₂ := by
  unfold allocationFactor
  rw [← (Equiv.arrowCongr τ σ).sum_comp]
  refine sum_congr rfl fun a _ => ?_
  have hap : ∀ r, Equiv.arrowCongr τ σ a r = σ (a (τ.symm r)) := fun _ => rfl
  have hc : (∀ e : {e // N₁.graph.target e = v₁}, b₁ e.val = forestBelow F₁
        ((univ.filter fun r => Equiv.arrowCongr τ σ a r = e).image Subtype.val)) ↔
      ∀ e : {e // N₂.graph.target e = v₂}, b₂ e.val = forestBelow F₂
        ((univ.filter fun r => a r = e).image Subtype.val) := by
    rw [σ.forall_congr_left]
    refine forall_congr' fun e => ?_
    simp only [hb a (σ.symm e), hap, ← Equiv.eq_symm_apply, Equiv.apply_symm_apply]
  have hw : allocationWeight ρ (fun e : {e // N₁.graph.target e = v₁} => θ₁.inheritance e.val)
        (Equiv.arrowCongr τ σ a) =
      allocationWeight ρ (fun e : {e // N₂.graph.target e = v₂} => θ₂.inheritance e.val) a := by
    have h1 : Equiv.arrowCongr τ σ a = (σ ∘ a) ∘ τ.symm := rfl
    rw [h1, allocationWeight_comp, allocationWeight_equiv_comp]
    congr 1
    funext e
    exact (hγ e).symm
  simp only [hc, hw]

end Reindex

/-! ### The chains of a network -/

section Chain

variable {V E X : Type*} [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E}

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- A chain vertex has only one arc leaving it. -/
theorem IsChainVertex.out_unique {v : V} (hv : N.IsChainVertex v) {g g' : E}
    (hg : N.graph.source g = v) (hg' : N.graph.source g' = v) : g = g' := by
  obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff v).mp hv.2
  rw [(he g).mp hg, (he g').mp hg']

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- A chain vertex has only one arc entering it. -/
theorem IsChainVertex.in_unique {v : V} (hv : N.IsChainVertex v) {g g' : E}
    (hg : N.graph.target g = v) (hg' : N.graph.target g' = v) : g = g' := by
  obtain ⟨e, he⟩ := (N.graph.indegree_eq_one_iff v).mp hv.1
  rw [(he g).mp hg, (he g').mp hg']

variable (N) in
/-- The arcs on the chain from the arc `e`, downwards, including `e`. -/
def chainArcs (e : E) : Finset E := univ.filter fun g => N.IsOnChain e g

omit [Fintype X] [DecidableEq X] in
theorem mem_chainArcs {e g : E} : g ∈ chainArcs N e ↔ N.IsOnChain e g := by
  simp [chainArcs]

omit [Fintype X] [DecidableEq X] in
theorem self_mem_chainArcs (e : E) : e ∈ chainArcs N e := mem_chainArcs.2 (Or.inl rfl)

omit [Fintype X] [DecidableEq X] in
/-- The chain from an arc entering a vertex that is not a chain vertex is that arc. -/
theorem chainArcs_of_not_isChainVertex {e : E} (h : ¬ N.IsChainVertex (N.graph.target e)) :
    chainArcs N e = {e} := by
  ext g
  rw [mem_chainArcs, mem_singleton]
  constructor
  · rintro (rfl | ⟨hc, hr⟩)
    · rfl
    · exfalso
      rcases Relation.ReflTransGen.cases_head hr with h' | ⟨a, ha, -⟩
      · exact h (h' ▸ hc)
      · exact h ha.1
  · rintro rfl
    exact Or.inl rfl

omit [Fintype X] [DecidableEq X] in
/-- The chain from an arc entering a chain vertex is that arc and the chain from the next arc. -/
theorem chainArcs_of_isChainVertex {e g : E} (h : N.IsChainVertex (N.graph.target e))
    (hg : N.graph.source g = N.graph.target e) : chainArcs N e = insert e (chainArcs N g) := by
  ext g'
  rw [mem_insert, mem_chainArcs, mem_chainArcs]
  constructor
  · rintro (rfl | ⟨hc, hr⟩)
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases Relation.ReflTransGen.cases_head hr with h' | ⟨a, ha, har⟩
      · exact Or.inl (IsChainVertex.out_unique h h'.symm hg)
      · have hat : a = N.graph.target g := h.adj_unique ha.2 ⟨g, hg, rfl⟩
        subst hat
        exact Or.inr ⟨hc, har⟩
  · rintro (rfl | rfl | ⟨hc, hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hg ▸ h, hg ▸ .refl⟩
    · exact Or.inr ⟨hc, Relation.ReflTransGen.head ⟨h, g, hg, rfl⟩ hr⟩

omit [Fintype X] [DecidableEq X] in
theorem notMem_chainArcs_next (hN : N.IsPhylogenetic) {e g : E}
    (hg : N.graph.source g = N.graph.target e) : e ∉ chainArcs N g := by
  rw [mem_chainArcs]
  rintro (rfl | ⟨-, hr⟩)
  · exact source_ne_target hN e hg
  · exact hN.acyclic _ (Relation.TransGen.trans_right hr.reaches
      (Relation.TransGen.head' ⟨e, rfl, rfl⟩ (Relation.ReflTransGen.single ⟨g, hg, rfl⟩)))

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- The arc `g` on the chain from `e` ends the part of the chain from `e` down to it. -/
theorem IsOnChain.chainReach_target {e g : E} (h : N.IsOnChain e g) :
    N.ChainReach (N.graph.target e) (N.graph.target g) := by
  rcases h with rfl | ⟨hc, hr⟩
  · exact .refl
  · exact hr.tail ⟨hc, g, rfl, rfl⟩

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- The arc of the chain from `e` entering the end of the chain. -/
theorem exists_lastArc (hN : N.IsPhylogenetic) (e : E) :
    ∃ g, N.IsOnChain e g ∧ N.graph.target g = chainEnd hN (N.graph.target e) := by
  rcases Relation.ReflTransGen.cases_tail (chainReach_chainEnd hN (N.graph.target e)) with
    h | ⟨a, ha, hc, g, hs, ht⟩
  · exact ⟨e, Or.inl rfl, h.symm⟩
  · exact ⟨g, Or.inr ⟨hs ▸ hc, hs ▸ ha⟩, ht⟩

/-- The last arc of the chain from the arc `e`. -/
def lastArc (hN : N.IsPhylogenetic) (e : E) : E := Classical.choose (exists_lastArc hN e)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem isOnChain_lastArc (hN : N.IsPhylogenetic) (e : E) : N.IsOnChain e (lastArc hN e) :=
  (Classical.choose_spec (exists_lastArc hN e)).1

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem target_lastArc (hN : N.IsPhylogenetic) (e : E) :
    N.graph.target (lastArc hN e) = chainEnd hN (N.graph.target e) :=
  (Classical.choose_spec (exists_lastArc hN e)).2

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem not_isChainVertex_target_lastArc (hN : N.IsPhylogenetic) (e : E) :
    ¬ N.IsChainVertex (N.graph.target (lastArc hN e)) := by
  rw [target_lastArc]
  exact not_isChainVertex_chainEnd hN _

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- An arc of the chain from `e` entering a vertex that is not a chain vertex is the last arc. -/
theorem eq_lastArc (hN : N.IsPhylogenetic) {e g : E} (h : N.IsOnChain e g)
    (ht : ¬ N.IsChainVertex (N.graph.target g)) : g = lastArc hN e :=
  IsOnChain.eq_of_target h (isOnChain_lastArc hN e)
    ((chainEnd_eq_of_chainReach hN (IsOnChain.chainReach_target h) ht).symm.trans
      (target_lastArc hN e).symm) ht

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem lastArc_of_not_isChainVertex (hN : N.IsPhylogenetic) {e : E}
    (h : ¬ N.IsChainVertex (N.graph.target e)) : lastArc hN e = e :=
  (eq_lastArc hN (Or.inl rfl) h).symm

omit [Fintype X] [DecidableEq X] in
theorem lastArc_of_isChainVertex (hN : N.IsPhylogenetic) {e g : E}
    (h : N.IsChainVertex (N.graph.target e)) (hg : N.graph.source g = N.graph.target e) :
    lastArc hN e = lastArc hN g := by
  refine (eq_lastArc hN ?_ (not_isChainVertex_target_lastArc hN g)).symm
  have hm : lastArc hN g ∈ chainArcs N e := by
    rw [chainArcs_of_isChainVertex h hg]
    exact mem_insert_of_mem (mem_chainArcs.2 (isOnChain_lastArc hN g))
  exact mem_chainArcs.1 hm

omit [Fintype X] [DecidableEq X] in
/-- The next arc after an arc of a chain lies on that chain. -/
theorem mem_chainArcs_of_source_eq {f g h : E} (hg : g ∈ chainArcs N f)
    (hc : N.IsChainVertex (N.graph.target g)) (hs : N.graph.source h = N.graph.target g) :
    h ∈ chainArcs N f :=
  mem_chainArcs.2 (Or.inr ⟨hs ▸ hc, hs ▸ IsOnChain.chainReach_target (mem_chainArcs.1 hg)⟩)

variable (N θ) in
/-- The factor of an arc: Kingman's coalescent along it and, if it enters a chain vertex, the forced
allocation at that vertex. -/
def arcFactor (e : E) (bot top : E → Finset (Finset X)) : ℝ :=
  kingmanTransition (θ.length e) (bot e) (top e) *
    if N.IsChainVertex (N.graph.target e) → ∀ g, N.graph.source g = N.graph.target e → bot e = top g
    then 1 else 0

theorem arcFactor_of_not_isChainVertex {e : E} (h : ¬ N.IsChainVertex (N.graph.target e))
    (bot top : E → Finset (Finset X)) :
    arcFactor N θ e bot top = kingmanTransition (θ.length e) (bot e) (top e) := by
  unfold arcFactor
  rw [ite_eq_left fun hc => absurd hc h, mul_one]

theorem arcFactor_of_isChainVertex {e g : E} (h : N.IsChainVertex (N.graph.target e))
    (hg : N.graph.source g = N.graph.target e) (bot top : E → Finset (Finset X)) :
    arcFactor N θ e bot top =
      kingmanTransition (θ.length e) (bot e) (top e) * if bot e = top g then 1 else 0 := by
  unfold arcFactor
  congr 1
  refine if_congr ⟨fun hh => hh h g hg, fun hh _ g' hg' => ?_⟩ rfl rfl
  rw [IsChainVertex.out_unique h hg' hg]
  exact hh

/-- The forests at the bottom and at the top of the arcs, as one function. -/
abbrev BotTop (E X : Type*) [DecidableEq X] := E → Finset (Finset X) × Finset (Finset X)

/-- The factor of an arc on a function of pairs. -/
abbrev arcFactorPair (N : RootedNetwork V E X) (θ : RootedNetwork.MetricData E) (e : E)
    (y : BotTop E X) : ℝ :=
  arcFactor N θ e (fun i => (y i).1) (fun i => (y i).2)

theorem arcFactorPair_congr {f g : E} (hg : g ∈ chainArcs N f) {y y' : BotTop E X}
    (h : ∀ i ∈ chainArcs N f, y i = y' i) :
    arcFactorPair N θ g y = arcFactorPair N θ g y' := by
  by_cases hc : N.IsChainVertex (N.graph.target g)
  · obtain ⟨g', hg'⟩ := (N.graph.outdegree_eq_one_iff _).mp hc.2
    have hs : N.graph.source g' = N.graph.target g := (hg' g').mpr rfl
    simp only [arcFactorPair, arcFactor_of_isChainVertex hc hs]
    rw [h g hg, h g' (mem_chainArcs_of_source_eq hg hc hs)]
  · simp only [arcFactorPair, arcFactor_of_not_isChainVertex hc]
    rw [h g hg]

/-- The number of values of a bottom and a top. -/
abbrev pairCard (X : Type*) [Fintype X] [DecidableEq X] : ℝ :=
  (Fintype.card (Finset (Finset X) × Finset (Finset X)) : ℝ)

/-- **Kingman's semigroup along a chain.** The forests at the bottom of the last arc and the top of
the first arc of a chain have the law of Kingman's coalescent along the sum of the lengths. -/
theorem card_pow_mul_sum_chain (hN : N.IsPhylogenetic) (θ : RootedNetwork.MetricData E) (e : E)
    (b t : Finset (Finset X)) :
    pairCard X ^ #(chainArcs N e) * ∑ y : BotTop E X,
        (if (y (lastArc hN e)).1 = b ∧ (y e).2 = t then 1 else 0) *
          ∏ g ∈ chainArcs N e, arcFactorPair N θ g y =
      kingmanTransition (∑ g ∈ chainArcs N e, θ.length g) b t * pairCard X ^ Fintype.card E := by
  have hC : (0 : ℝ) < pairCard X := by exact_mod_cast Fintype.card_pos
  set C := pairCard X with hCdef
  induction hn : #(chainArcs N e) using Nat.strong_induction_on generalizing e b t with
  | _ n ih =>
    by_cases h : N.IsChainVertex (N.graph.target e)
    · obtain ⟨g, hg⟩ := (N.graph.outdegree_eq_one_iff _).mp h.2
      have hs : N.graph.source g = N.graph.target e := (hg g).mpr rfl
      have hnot := notMem_chainArcs_next hN hs
      have hce := chainArcs_of_isChainVertex h hs
      have hn' : n = #(chainArcs N g) + 1 := by rw [← hn, hce, card_insert_of_notMem hnot]
      have hlast := lastArc_of_isChainVertex hN h hs
      rw [hn', hce, hlast, sum_insert hnot]
      -- the part of the chain below `e`, and the arc `e`
      let Ω : Finset (Finset X) → BotTop E X → ℝ := fun σ y =>
        (if (y (lastArc hN g)).1 = b ∧ (y g).2 = σ then 1 else 0) *
          ∏ g' ∈ chainArcs N g, arcFactorPair N θ g' y
      let R : Finset (Finset X) → BotTop E X → ℝ := fun σ y =>
        if y e = (σ, t) then kingmanTransition (θ.length e) σ t else 0
      have hpt : ∀ y : BotTop E X,
          (if (y (lastArc hN g)).1 = b ∧ (y e).2 = t then 1 else 0) *
            ∏ g' ∈ insert e (chainArcs N g), arcFactorPair N θ g' y =
          ∑ σ, Ω σ y * R σ y := by
        intro y
        rw [prod_insert hnot, sum_eq_single (y g).2]
        · simp only [Ω, R, arcFactorPair, arcFactor_of_isChainVertex h hs]
          by_cases h4 : y e = ((y g).2, t)
          · have h3 : (y e).1 = (y g).2 := congrArg Prod.fst h4
            have h2 : (y e).2 = t := congrArg Prod.snd h4
            simp only [h4, and_true, ↓reduceIte]
            ring
          · rw [ite_eq_right h4, mul_zero]
            by_cases h2 : (y e).2 = t
            · have h3 : ¬ (y e).1 = (y g).2 := fun h3 => h4 (Prod.ext h3 h2)
              rw [ite_eq_right h3]
              ring
            · rw [ite_eq_right fun h' => h2 h'.2]
              ring
        · intro σ _ hσ
          simp only [Ω]
          rw [ite_eq_right fun h' => hσ h'.2.symm]
          ring
        · exact fun h' => absurd (mem_univ _) h'
      have hlastm : lastArc hN g ∈ chainArcs N g := mem_chainArcs.2 (isOnChain_lastArc hN g)
      have hind : ∀ σ, C ^ Fintype.card E * ∑ y, Ω σ y * R σ y =
          (∑ y, Ω σ y) * ∑ y, R σ y := by
        intro σ
        have := card_mul_sum_mul_of_depends ({e} : Finset E) (Ω σ) (R σ) (fun y y' hyy => ?_)
          (fun y y' hyy => ?_)
        · rwa [card_fun_eq_pow] at this
        · have hag : ∀ i ∈ chainArcs N g, y i = y' i := fun i hi =>
            hyy i fun hie => hnot (mem_singleton.1 hie ▸ hi)
          simp only [Ω]
          rw [hag _ hlastm, hag g (self_mem_chainArcs g),
            prod_congr rfl fun g' hg' => arcFactorPair_congr hg' hag]
        · simp only [R]
          rw [hyy e (mem_singleton_self e)]
      have hΩ : ∀ σ, C ^ #(chainArcs N g) * ∑ y, Ω σ y =
          kingmanTransition (∑ g' ∈ chainArcs N g, θ.length g') b σ * C ^ Fintype.card E :=
        fun σ => ih _ (by omega) g b σ rfl
      have hR : ∀ σ, C * ∑ y, R σ y = kingmanTransition (θ.length e) σ t * C ^ Fintype.card E :=
        fun σ => card_mul_sum_ite_coord e (σ, t) (kingmanTransition (θ.length e) σ t)
      have hM : C ^ Fintype.card E ≠ 0 := pow_ne_zero _ hC.ne'
      refine mul_left_cancel₀ hM ?_
      have hsum : ∑ y : BotTop E X, (if (y (lastArc hN g)).1 = b ∧ (y e).2 = t then 1 else 0) *
            ∏ g' ∈ insert e (chainArcs N g), arcFactorPair N θ g' y =
          ∑ σ, ∑ y, Ω σ y * R σ y := by
        rw [sum_comm]
        exact sum_congr rfl fun y _ => hpt y
      rw [hsum, add_comm (θ.length e), kingmanTransition_add, Matrix.mul_apply, sum_mul, mul_sum,
        mul_sum, mul_sum]
      refine sum_congr rfl fun σ _ => ?_
      calc C ^ Fintype.card E * (C ^ (#(chainArcs N g) + 1) * ∑ y, Ω σ y * R σ y)
          = C ^ (#(chainArcs N g) + 1) * (C ^ Fintype.card E * ∑ y, Ω σ y * R σ y) := by ring
        _ = (C ^ #(chainArcs N g) * ∑ y, Ω σ y) * (C * ∑ y, R σ y) := by
            rw [hind, pow_succ]; ring
        _ = _ := by rw [hΩ, hR]; ring
    · rw [chainArcs_of_not_isChainVertex h] at hn ⊢
      rw [lastArc_of_not_isChainVertex hN h, ← hn, card_singleton, pow_one, sum_singleton]
      have hpt : ∀ y : BotTop E X,
          (if (y e).1 = b ∧ (y e).2 = t then 1 else 0) *
            ∏ g' ∈ ({e} : Finset E), arcFactorPair N θ g' y =
          if y e = (b, t) then kingmanTransition (θ.length e) b t else 0 := by
        intro y
        rw [prod_singleton]
        simp only [arcFactorPair, arcFactor_of_not_isChainVertex h]
        by_cases h1 : y e = (b, t)
        · rw [ite_eq_left h1, ite_eq_left ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩, one_mul, h1]
        · rw [ite_eq_right h1, ite_eq_right fun h' => h1 (Prod.ext h'.1 h'.2), zero_mul]
      simp only [hpt]
      exact card_mul_sum_ite_coord e (b, t) (kingmanTransition (θ.length e) b t)

omit [Fintype X] [DecidableEq X] in
/-- Each arc lies on the chain of exactly one arc leaving a vertex that is not a chain vertex. -/
theorem biUnion_chainArcs [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) :
    (univ : Finset {e // ¬ N.IsChainVertex (N.graph.source e)}).biUnion
      (fun f => chainArcs N f.1) = univ := by
  ext e
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  obtain ⟨f, hf, hon⟩ := exists_isOnChain hN e
  exact ⟨⟨f, hf⟩, mem_chainArcs.2 hon⟩

omit [Fintype X] [DecidableEq X] in
theorem disjoint_chainArcs {f f' : {e // ¬ N.IsChainVertex (N.graph.source e)}} (h : f ≠ f') :
    Disjoint (chainArcs N f.1) (chainArcs N f'.1) := by
  rw [disjoint_left]
  intro g hg hg'
  exact h (Subtype.ext (IsOnChain.unique (mem_chainArcs.1 hg) (mem_chainArcs.1 hg') f.2 f'.2))

/-- **Kingman's semigroup along all the chains.** -/
theorem sum_prod_arcFactorPair [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) (θ : RootedNetwork.MetricData E)
    (b t : {e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X)) :
    ∑ y : BotTop E X,
        (if ∀ f, (y (lastArc hN f.1)).1 = b f ∧ (y f.1).2 = t f then 1 else 0) *
          ∏ g, arcFactorPair N θ g y =
      ∏ f, kingmanTransition (∑ g ∈ chainArcs N f.1, θ.length g) (b f) (t f) := by
  have hC : (0 : ℝ) < pairCard X := by exact_mod_cast Fintype.card_pos
  let Ω : {e // ¬ N.IsChainVertex (N.graph.source e)} → BotTop E X → ℝ := fun f y =>
    (if (y (lastArc hN f.1)).1 = b f ∧ (y f.1).2 = t f then 1 else 0) *
      ∏ g ∈ chainArcs N f.1, arcFactorPair N θ g y
  have hprod : ∀ y : BotTop E X, ∏ f, Ω f y =
      (if ∀ f, (y (lastArc hN f.1)).1 = b f ∧ (y f.1).2 = t f then 1 else 0) *
        ∏ g, arcFactorPair N θ g y := by
    intro y
    simp only [Ω]
    rw [prod_mul_distrib, prod_ite_zero, prod_const_one]
    congr 1
    · simp only [mem_univ, true_implies]
    · rw [← prod_biUnion fun f _ f' _ h => disjoint_chainArcs h, biUnion_chainArcs hN]
  have h := card_pow_mul_sum_prod (univ : Finset {e // ¬ N.IsChainVertex (N.graph.source e)})
    (fun f => chainArcs N f.1) Ω
    (fun f => kingmanTransition (∑ g ∈ chainArcs N f.1, θ.length g) (b f) (t f))
    (fun f _ f' _ hne => disjoint_chainArcs hne)
    (fun f _ y y' hyy => by
      simp only [Ω]
      rw [hyy _ (mem_chainArcs.2 (isOnChain_lastArc hN f.1)), hyy _ (self_mem_chainArcs f.1),
        prod_congr rfl fun g hg => arcFactorPair_congr hg hyy])
    (fun f _ => card_pow_mul_sum_chain hN θ f.1 (b f) (t f))
  rw [biUnion_chainArcs hN, card_univ] at h
  simp only [hprod] at h
  exact mul_left_cancel₀ (pow_ne_zero _ hC.ne') (h.trans (mul_comm _ _))

/-- A sum over the bottoms and the tops of the arcs, as a sum over one function of pairs. -/
theorem sum_sum_eq_sum_botTop (H : (E → Finset (Finset X)) → (E → Finset (Finset X)) → ℝ) :
    ∑ bot, ∑ top, H bot top = ∑ y : BotTop E X, H (fun i => (y i).1) (fun i => (y i).2) := by
  rw [← Fintype.sum_prod_type']
  exact ((Equiv.arrowProdEquivProdArrow E (fun _ => Finset (Finset X))
    (fun _ => Finset (Finset X))).sum_comp fun p => H p.1 p.2).symm

/-- **Summing out the arcs of the chains.** A function of the forests at the bottom of the last arcs
and the top of the first arcs of the chains sees Kingman's coalescent along each whole chain. -/
theorem sum_sum_mul_prod_arcFactor [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) (θ : RootedNetwork.MetricData E)
    (Φ : ({e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X)) →
      ({e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X)) → ℝ) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        Φ (fun f => bot (lastArc hN f.1)) (fun f => top f.1) * ∏ g, arcFactor N θ g bot top =
      ∑ b, ∑ t, Φ b t *
        ∏ f, kingmanTransition (∑ g ∈ chainArcs N f.1, θ.length g) (b f) (t f) := by
  rw [sum_sum_eq_sum_botTop]
  simp only [← sum_prod_arcFactorPair hN θ, mul_sum]
  have hR : ∀ b t : {e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X),
      ∑ y : BotTop E X, Φ b t *
        ((if ∀ f, (y (lastArc hN f.1)).1 = b f ∧ (y f.1).2 = t f then 1 else 0) *
          ∏ g, arcFactorPair N θ g y) =
      ∑ y : BotTop E X, if b = (fun f => (y (lastArc hN f.1)).1) ∧ t = (fun f => (y f.1).2) then
        Φ (fun f => (y (lastArc hN f.1)).1) (fun f => (y f.1).2) *
          ∏ g, arcFactorPair N θ g y else 0 := by
    intro b t
    refine sum_congr rfl fun y _ => ?_
    by_cases h : b = (fun f => (y (lastArc hN f.1)).1) ∧ t = (fun f => (y f.1).2)
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [ite_eq_right h, ite_eq_right, zero_mul, mul_zero]
      intro hh
      exact h ⟨funext fun f => (hh f).1.symm, funext fun f => (hh f).2.symm⟩
  simp only [hR]
  refine Eq.symm ((sum_congr rfl fun b _ => sum_comm).trans ?_)
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_eq_single (fun f => (y (lastArc hN f.1)).1), sum_eq_single (fun f => (y f.1).2)]
  · simp
  · intro t _ ht
    exact ite_eq_right fun h => ht h.2
  · exact fun h => absurd (mem_univ _) h
  · intro b _ hb
    exact sum_eq_zero fun t _ => ite_eq_right fun h => hb h.1
  · exact fun h => absurd (mem_univ _) h

end Chain

/-! ### The suppressed network -/

section Suppress

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}

omit [Fintype V] in
/-- The forest arriving at a vertex of the suppressed network. -/
theorem arrivingForest_suppress [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) (top : E → Finset (Finset X)) (v : {v // ¬ N.IsChainVertex v}) :
    arrivingForest (N.suppress hN) (fun f => top f.1) v = arrivingForest N top v.1 := by
  ext A
  simp only [arrivingForest, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_biUnion]
  refine or_congr ?_ ⟨?_, ?_⟩
  · refine exists_congr fun x => and_congr_left fun _ => ?_
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · rintro ⟨f, hf, hA⟩
    exact ⟨f.1, congrArg Subtype.val hf, hA⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨⟨e, by rw [he]; exact v.2⟩, Subtype.ext he, hA⟩

/-- The arcs entering a vertex of the suppressed network are the arcs entering it in the network: an
arc of the suppressed network goes to the last arc of its chain. -/
def suppressArcsInto (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    {f // (N.suppress hN).graph.target f = v} ≃ {e // N.graph.target e = v.1} :=
  Equiv.ofBijective
    (fun f => ⟨lastArc hN f.1.1, (target_lastArc hN f.1.1).trans (congrArg Subtype.val f.2)⟩)
    ⟨fun f f' h => by
      have h' : lastArc hN f.1.1 = lastArc hN f'.1.1 := congrArg Subtype.val h
      refine Subtype.ext (Subtype.ext (IsOnChain.unique (isOnChain_lastArc hN f.1.1) ?_ f.1.2
        f'.1.2))
      rw [h']
      exact isOnChain_lastArc hN f'.1.1,
    fun e => by
      obtain ⟨f, hf, hon⟩ := exists_isOnChain hN e.1
      have he : ¬ N.IsChainVertex (N.graph.target e.1) := by rw [e.2]; exact v.2
      have hl : e.1 = lastArc hN f := eq_lastArc hN hon he
      refine ⟨⟨⟨f, hf⟩, Subtype.ext ?_⟩, Subtype.ext hl.symm⟩
      change chainEnd hN (N.graph.target f) = v.1
      rw [← target_lastArc, ← hl, e.2]⟩

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem suppressArcsInto_apply (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v})
    (f : {f // (N.suppress hN).graph.target f = v}) :
    (suppressArcsInto hN v f).1 = lastArc hN f.1.1 := rfl

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- An arc of the chain from `f` other than the last has inheritance one. -/
theorem inheritance_eq_one_of_isChainVertex (hθ : N.IsNormalized θ) {g : E}
    (hg : N.IsChainVertex (N.graph.target g)) : θ.inheritance g = 1 :=
  hθ.1 g hg.1

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The inheritance of an arc of the suppressed network is that of the last arc of its chain. -/
theorem suppressMetric_inheritance_eq_lastArc (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ)
    (f : {e // ¬ N.IsChainVertex (N.graph.source e)}) :
    (N.suppressMetric θ).inheritance f = θ.inheritance (lastArc hN f.1) := by
  change ∏ g ∈ chainArcs N f.1, θ.inheritance g = _
  refine prod_eq_single_of_mem _ (mem_chainArcs.2 (isOnChain_lastArc hN f.1)) fun g hg hne => ?_
  refine inheritance_eq_one_of_isChainVertex hθ ?_
  by_contra hc
  exact hne (eq_lastArc hN (mem_chainArcs.1 hg) hc)

omit [Fintype V] in
/-- The allocation at a vertex of the suppressed network. -/
theorem allocationFactor_suppress [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (F : Finset (Finset X))
    (v : {v // ¬ N.IsChainVertex v}) (bot : E → Finset (Finset X)) :
    allocationFactor (N.suppress hN) (N.suppressMetric θ) ρ F v (fun f => bot (lastArc hN f.1)) =
      allocationFactor N θ ρ F v.1 bot := by
  refine (allocationFactor_eq_of_equiv (suppressArcsInto hN v) (Equiv.refl _)
    (fun e => suppressMetric_inheritance_eq_lastArc hN hθ e.1) ?_).symm
  intro a e
  rfl

omit [Fintype V] [Fintype E] in
/-- The part of a forest below all its roots is the forest. -/
theorem forestBelow_image_univ (F : Finset (Finset X)) :
    forestBelow F ((univ : Finset {A // A ∈ roots F}).image Subtype.val) = F := by
  ext A
  rw [mem_forestBelow]
  constructor
  · exact fun h => h.1
  · intro hA
    obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
    exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩

omit [Fintype V] in
/-- At a vertex with one arc entering it, of inheritance one, the allocation is forced. -/
theorem allocationFactor_of_unique_arc (hρ : 0 ≤ ρ) {v : V} {e : E} (he : N.graph.target e = v)
    (huniq : ∀ g, N.graph.target g = v → g = e) (h1 : θ.inheritance e = 1) (F : Finset (Finset X))
    (bot : E → Finset (Finset X)) :
    allocationFactor N θ ρ F v bot = if bot e = F then 1 else 0 := by
  let e₀ : {g // N.graph.target g = v} := ⟨e, he⟩
  have hsub : ∀ g : {g // N.graph.target g = v}, g = e₀ := fun g => Subtype.ext (huniq g.1 g.2)
  have : Subsingleton {g // N.graph.target g = v} := ⟨fun g g' => (hsub g).trans (hsub g').symm⟩
  unfold allocationFactor
  rw [Fintype.sum_subsingleton _ (fun _ => e₀)]
  have hc : (∀ g : {g // N.graph.target g = v}, bot g.val = forestBelow F
        ((univ.filter fun r : {A // A ∈ roots F} => e₀ = g).image Subtype.val)) ↔ bot e = F := by
    constructor
    · intro h
      have := h e₀
      rwa [filter_true_of_mem (fun _ _ => rfl), forestBelow_image_univ] at this
    · intro h g
      rw [hsub g, filter_true_of_mem (fun _ _ => rfl), forestBelow_image_univ]
      exact h
  simp only [hc]
  refine if_ctx_congr Iff.rfl (fun _ => ?_) fun _ => rfl
  rcases isEmpty_or_nonempty {A // A ∈ roots F} with hR | hR
  · simp [allocationWeight]
  · exact allocationWeight_const_eq_one hρ (γ := fun g : {g // N.graph.target g = v} =>
      θ.inheritance g.val) h1

omit [Fintype V] in
/-- The forest arriving at a chain vertex is the forest at the top of the arc leaving it. -/
theorem arrivingForest_of_isChainVertex (hN : N.IsPhylogenetic) {v : V} (hv : N.IsChainVertex v)
    {g : E} (hg : N.graph.source g = v) (top : E → Finset (Finset X)) :
    arrivingForest N top v = top g := by
  have h1 : (univ.filter fun x => N.leaf x = v) = ∅ :=
    filter_false_of_mem fun x _ hx => not_isChainVertex_leaf hN x (hx ▸ hv)
  have h2 : (univ.filter fun e => N.graph.source e = v) = {g} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun he => IsChainVertex.out_unique hv he hg, fun he => he ▸ hg⟩
  unfold arrivingForest
  rw [h1, h2, image_empty, empty_union, singleton_biUnion]

/-- The factors of the arcs are the factors of Kingman's coalescent along them and the forced
allocations at the chain vertices. -/
theorem prod_arcFactor (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (bot top : E → Finset (Finset X)) :
    ∏ g, arcFactor N θ g bot top =
      (∏ e, kingmanTransition (θ.length e) (bot e) (top e)) *
        ∏ v ∈ univ.filter fun v => N.IsChainVertex v,
          allocationFactor N θ ρ (arrivingForest N top v) v bot := by
  unfold arcFactor
  rw [prod_mul_distrib]
  congr 1
  have hsplit : ∏ e, (if N.IsChainVertex (N.graph.target e) →
        ∀ g, N.graph.source g = N.graph.target e → bot e = top g then (1 : ℝ) else 0) =
      ∏ e ∈ univ.filter fun e => N.IsChainVertex (N.graph.target e),
        (if N.IsChainVertex (N.graph.target e) →
          ∀ g, N.graph.source g = N.graph.target e → bot e = top g then (1 : ℝ) else 0) := by
    refine (prod_subset (filter_subset _ _) fun e _ he => ?_).symm
    have hne : ¬ N.IsChainVertex (N.graph.target e) := fun h => he (mem_filter.2 ⟨mem_univ _, h⟩)
    exact ite_eq_left fun h => absurd h hne
  rw [hsplit]
  refine prod_bij (fun e _ => N.graph.target e)
    (fun e he => mem_filter.2 ⟨mem_univ _, (mem_filter.1 he).2⟩) ?_ ?_ ?_
  · intro e he e' he' h
    exact IsChainVertex.in_unique (mem_filter.1 he).2 rfl h.symm
  · intro v hv
    have hv' := (mem_filter.1 hv).2
    obtain ⟨e, he⟩ := (N.graph.indegree_eq_one_iff v).mp hv'.1
    have ht : N.graph.target e = v := (he e).mpr rfl
    exact ⟨e, mem_filter.2 ⟨mem_univ _, ht ▸ hv'⟩, ht⟩
  · intro e he
    have hc := (mem_filter.1 he).2
    obtain ⟨g, hg⟩ := (N.graph.outdegree_eq_one_iff _).mp hc.2
    have hs : N.graph.source g = N.graph.target e := (hg g).mpr rfl
    rw [allocationFactor_of_unique_arc hρ rfl (fun g' hg' => IsChainVertex.in_unique hc hg' rfl)
      (inheritance_eq_one_of_isChainVertex hθ hc), arrivingForest_of_isChainVertex hN hc hs]
    refine if_congr ⟨fun h => h hc g hs, fun h _ g' hg' => ?_⟩ rfl rfl
    rw [IsChainVertex.out_unique hc hg' hs]
    exact h

omit [Fintype E] [Fintype X] [DecidableEq X] in
/-- The non-root vertices are the vertices of the suppressed network and the chain vertices. -/
theorem prod_erase_root_eq (hN : N.IsPhylogenetic) [Fintype {v // ¬ N.IsChainVertex v}]
    [iV : DecidableEq {v // ¬ N.IsChainVertex v}] (g : V → ℝ) :
    ∏ v ∈ univ.erase N.root, g v =
      (∏ v ∈ univ.erase (N.suppress hN).root, g v.1) *
        ∏ v ∈ univ.filter fun v => N.IsChainVertex v, g v := by
  have hroot : (N.suppress hN).root.1 = N.root := rfl
  have h1 : ∏ v ∈ univ.erase (N.suppress hN).root, g v.1 =
      ∏ v ∈ (univ.erase N.root).filter fun v => ¬ N.IsChainVertex v, g v := by
    refine prod_bij (fun v _ => v.1) (fun v hv => ?_) (fun v _ v' _ h => Subtype.ext h) ?_
      fun _ _ => rfl
    · exact mem_filter.2 ⟨mem_erase.2 ⟨fun h => (mem_erase.1 hv).1 (Subtype.ext h), mem_univ _⟩, v.2⟩
    · intro v hv
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      exact ⟨⟨v, hv2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 hv1).1 (congrArg Subtype.val h),
        mem_univ _⟩, rfl⟩
  have h2 : (univ.erase N.root).filter (fun v => N.IsChainVertex v) =
      univ.filter fun v => N.IsChainVertex v := by
    ext v
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, and_iff_right_iff_imp]
    rintro hv rfl
    exact not_isChainVertex_root hN hv
  rw [h1, ← h2, mul_comm]
  exact (prod_filter_mul_prod_filter_not _ _ _).symm

/-- **Suppression does not change the gene tree distribution**, for every network and every gene
tree: a node of indegree and outdegree one is replaced by one edge, whose length is the sum of the two
lengths and which retains the hybridization parameter of the lower edge. The history factors into the
vertices that stay (`prod_erase_root_eq`, `allocationFactor_suppress`, `arrivingForest_suppress`), and
the arcs of the chains with their forced allocations (`prod_arcFactor`), which sum out by Kingman's
semigroup (`sum_sum_mul_prod_arcFactor`). -/
theorem geneTreeDist_suppress [Fintype {v // ¬ N.IsChainVertex v}]
    [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}] (hN : N.IsPhylogenetic)
    (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (G : Finset (Finset X)) :
    geneTreeDist (N.suppress hN) (N.suppressMetric θ) ρ G = geneTreeDist N θ ρ G := by
  let Φ : ({e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X)) →
      ({e // ¬ N.IsChainVertex (N.graph.source e)} → Finset (Finset X)) → ℝ := fun b t =>
    (∏ v ∈ @Finset.erase _ (fun a b => Classical.propDecidable (a = b)) univ (N.suppress hN).root,
      allocationFactor (N.suppress hN) (N.suppressMetric θ) ρ
        (arrivingForest (N.suppress hN) t v) v b) *
    kingmanAbsorption (arrivingForest (N.suppress hN) t (N.suppress hN).root) G
  have hL : geneTreeDist (N.suppress hN) (N.suppressMetric θ) ρ G =
      ∑ b, ∑ t, Φ b t *
        ∏ f, kingmanTransition (∑ g ∈ chainArcs N f.1, θ.length g) (b f) (t f) := by
    refine sum_congr_instance _ _ _ _ fun b => sum_congr_instance _ _ _ _ fun t => ?_
    simp only [historyWeight, Φ]
    change _ * (∏ f, kingmanTransition (∑ g ∈ chainArcs N f.1, θ.length g) (b f) (t f)) * _ = _
    ring
  have hR : geneTreeDist N θ ρ G = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      Φ (fun f => bot (lastArc hN f.1)) (fun f => top f.1) * ∏ g, arcFactor N θ g bot top := by
    refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
    simp only [Φ, arrivingForest_suppress hN top, allocationFactor_suppress hN hθ]
    rw [prod_arcFactor hN hθ hρ, historyWeight,
      prod_erase_root_eq hN (iV := fun a b => Classical.propDecidable (a = b))
        fun v => allocationFactor N θ ρ (arrivingForest N top v) v bot]
    change _ = _ * kingmanAbsorption (arrivingForest N top N.root) G * _
    ring
  rw [hL, hR, sum_sum_mul_prod_arcFactor]

/-- **Suppression does not change the concordance factors.** -/
theorem nmscCF_suppress [Fintype {v // ¬ N.IsChainVertex v}]
    [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}] (hN : N.IsPhylogenetic)
    (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ) (s : QuartetTree X) :
    nmscCF (N.suppress hN) (N.suppressMetric θ) ρ s = nmscCF N θ ρ s := by
  unfold nmscCF
  simp only [geneTreeDist_suppress hN hθ hρ]

end Suppress

end NMSC

end Phylogenetics
