module

public import Phylogenetics.NMSC.InducedSuppress

/-!
# Gluing the network multispecies coalescent along arcs

Let a network be made of an upper part and a lower part with a root, joined by arcs from the upper part
into that root. Then the history of the lower part gives a law of the forest arriving at that root;
the allocation at that root and the coalescent along the joining arcs give forests at their tops; and
the upper part is the same process with those forests injected at the sources of the joining arcs.

This one formula computes the coalescent on a network built from pieces. A cut arc is the case of one
joining arc, and a reticulation the case of several.

## Main definitions and results

* `rootDist N θ ρ inj`: the law of the forest arriving at the root, in the process with injected forests.
* `injDist_eq_sum_rootDist`: the distribution of gene trees above the root, from it.
* `rootDist_glue`: the formula.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.NMSC

set_option linter.unusedSectionVars false

section RootDist

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq L]

/-- The law of the forest arriving at the root of the process with injected forests. -/
def rootDist (N : RootedNetwork V E L) (θ : RootedNetwork.MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset L)) (F : Finset (Finset L)) : ℝ :=
  ∑ bot : E → Finset (Finset L), ∑ top : E → Finset (Finset L),
    injWeight N θ ρ inj bot top * if arriving N inj top N.root = F then 1 else 0

/-- A function of the forest at the root, averaged over the law at the root. -/
theorem sum_rootDist_mul (N : RootedNetwork V E L) (θ : RootedNetwork.MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset L)) (Φ : Finset (Finset L) → ℝ) :
    ∑ F, rootDist N θ ρ inj F * Φ F =
      ∑ bot : E → Finset (Finset L), ∑ top : E → Finset (Finset L),
        injWeight N θ ρ inj bot top * Φ (arriving N inj top N.root) := by
  unfold rootDist
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun top _ => ?_
  rw [Finset.sum_eq_single (arriving N inj top N.root)]
  · simp
  · intro F _ hF
    rw [ite_eq_right (Ne.symm hF)]
    simp
  · simp

/-- The distribution above the root is the law at the root, followed by the population above it. -/
theorem injDist_eq_sum_rootDist (N : RootedNetwork V E L) (θ : RootedNetwork.MetricData E) (ρ : ℝ)
    (inj : V → Finset (Finset L)) (G : Finset (Finset L)) :
    injDist N θ ρ inj G = ∑ F, rootDist N θ ρ inj F * kingmanAbsorption F G :=
  (sum_rootDist_mul N θ ρ inj fun F => kingmanAbsorption F G).symm

end RootDist

section Glue

variable {V E L V₀ E₀ V₁ E₁ P : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq L]
  [Fintype V₀] [Fintype E₀] [Fintype V₁] [Fintype E₁] [Fintype P]

/-- The arc functions on the pieces, assembled along a bijection of the arcs. -/
def joinArcs {α : Type*} (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (b₀ : E₀ → α) (bP : P → α) (b₁ : E₁ → α) : E → α :=
  fun e => Sum.elim b₀ (Sum.elim bP b₁) (fE.symm e)

omit [Fintype E] [Fintype E₀] [Fintype E₁] [Fintype P] in
@[simp] theorem joinArcs_inl {α : Type*} (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (b₀ : E₀ → α) (bP : P → α)
    (b₁ : E₁ → α) (e : E₀) : joinArcs fE b₀ bP b₁ (fE (.inl e)) = b₀ e := by
  simp [joinArcs]

omit [Fintype E] [Fintype E₀] [Fintype E₁] [Fintype P] in
@[simp] theorem joinArcs_inrl {α : Type*} (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (b₀ : E₀ → α) (bP : P → α)
    (b₁ : E₁ → α) (p : P) : joinArcs fE b₀ bP b₁ (fE (.inr (.inl p))) = bP p := by
  simp [joinArcs]

omit [Fintype E] [Fintype E₀] [Fintype E₁] [Fintype P] in
@[simp] theorem joinArcs_inrr {α : Type*} (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (b₀ : E₀ → α) (bP : P → α)
    (b₁ : E₁ → α) (e : E₁) : joinArcs fE b₀ bP b₁ (fE (.inr (.inr e))) = b₁ e := by
  simp [joinArcs]

/-- A function of the arcs is its three restrictions. -/
def joinEquiv (α : Type*) (fE : E₀ ⊕ P ⊕ E₁ ≃ E) : (E₀ → α) × (P → α) × (E₁ → α) ≃ (E → α) where
  toFun x := joinArcs fE x.1 x.2.1 x.2.2
  invFun b := (fun e => b (fE (.inl e)), fun p => b (fE (.inr (.inl p))),
    fun e => b (fE (.inr (.inr e))))
  left_inv x := by
    obtain ⟨b₀, bP, b₁⟩ := x
    simp
  right_inv b := by
    funext e
    obtain ⟨x, rfl⟩ := fE.surjective e
    rcases x with e | p | e <;> simp

/-- A sum over the functions of the arcs is a sum over their three restrictions. -/
theorem sum_arcs {α : Type*} [Fintype α] (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (g : (E → α) → ℝ) :
    ∑ b, g b = ∑ b₀ : E₀ → α, ∑ bP : P → α, ∑ b₁ : E₁ → α, g (joinArcs fE b₀ bP b₁) := by
  rw [← (joinEquiv α fE).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun b₀ _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

omit [Fintype V] [Fintype E] [Fintype L] [DecidableEq L] [Fintype V₀] [Fintype E₀] [Fintype V₁]
  [Fintype E₁] [Fintype P] in
/-- Reordering six sums. -/
theorem sum_shuffle {A B C D F G : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype F]
    [Fintype G] (f : A → B → C → D → F → G → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g =
      ∑ c, ∑ g, ∑ b, ∑ e, ∑ a, ∑ d, f a b c d e g := by
  have h : ∑ x : A × B × C × D × F × G, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 =
      ∑ y : C × G × B × F × A × D, f y.2.2.2.2.1 y.2.2.1 y.1 y.2.2.2.2.2 y.2.2.2.1 y.2.1 :=
    Fintype.sum_equiv
      { toFun := fun x => (x.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.2.2.1, x.1, x.2.2.2.1)
        invFun := fun y => (y.2.2.2.2.1, y.2.2.1, y.1, y.2.2.2.2.2, y.2.2.2.1, y.2.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun _ => rfl
  simpa only [Fintype.sum_prod_type] using h

variable {N : RootedNetwork V E L} {N₀ : RootedNetwork V₀ E₀ L} {N₁ : RootedNetwork V₁ E₁ L}
  {θ : RootedNetwork.MetricData E} {θ₀ : RootedNetwork.MetricData E₀}
  {θ₁ : RootedNetwork.MetricData E₁} {ρ : ℝ}

/-- How a network is made of an upper part `N₀` and a lower part `N₁`, joined by arcs `P`, of lengths
`ℓ`, from the vertices `s` of the upper part into the root of the lower part. -/
structure IsGlued (N : RootedNetwork V E L) (θ : RootedNetwork.MetricData E)
    (N₀ : RootedNetwork V₀ E₀ L) (θ₀ : RootedNetwork.MetricData E₀)
    (N₁ : RootedNetwork V₁ E₁ L) (θ₁ : RootedNetwork.MetricData E₁)
    (fV : V₀ ⊕ V₁ ≃ V) (fE : E₀ ⊕ P ⊕ E₁ ≃ E) (s : P → V₀) (ℓ : P → ℝ) : Prop where
  source₀ : ∀ e, N.graph.source (fE (.inl e)) = fV (.inl (N₀.graph.source e))
  target₀ : ∀ e, N.graph.target (fE (.inl e)) = fV (.inl (N₀.graph.target e))
  sourceP : ∀ p, N.graph.source (fE (.inr (.inl p))) = fV (.inl (s p))
  targetP : ∀ p, N.graph.target (fE (.inr (.inl p))) = fV (.inr N₁.root)
  source₁ : ∀ e, N.graph.source (fE (.inr (.inr e))) = fV (.inr (N₁.graph.source e))
  target₁ : ∀ e, N.graph.target (fE (.inr (.inr e))) = fV (.inr (N₁.graph.target e))
  root : N.root = fV (.inl N₀.root)
  not_target_root : ∀ e, N₁.graph.target e ≠ N₁.root
  length₀ : ∀ e, θ.length (fE (.inl e)) = θ₀.length e
  lengthP : ∀ p, θ.length (fE (.inr (.inl p))) = ℓ p
  length₁ : ∀ e, θ.length (fE (.inr (.inr e))) = θ₁.length e
  inheritance₀ : ∀ e, θ.inheritance (fE (.inl e)) = θ₀.inheritance e
  inheritance₁ : ∀ e, θ.inheritance (fE (.inr (.inr e))) = θ₁.inheritance e

variable {fV : V₀ ⊕ V₁ ≃ V} {fE : E₀ ⊕ P ⊕ E₁ ≃ E} {s : P → V₀} {ℓ : P → ℝ}

/-- The forests injected in the upper part: those of the network, and the forests `t` at the tops of
the joining arcs. -/
def upperInj (fV : V₀ ⊕ V₁ ≃ V) (s : P → V₀) (inj : V → Finset (Finset L))
    (t : P → Finset (Finset L)) (v : V₀) : Finset (Finset L) :=
  inj (fV (.inl v)) ∪ (univ.filter fun p => s p = v).biUnion t

/-- The forests injected in the lower part: those of the network. -/
def lowerInj (fV : V₀ ⊕ V₁ ≃ V) (inj : V → Finset (Finset L)) (v : V₁) : Finset (Finset L) :=
  inj (fV (.inr v))

namespace IsGlued

variable (hg : IsGlued N θ N₀ θ₀ N₁ θ₁ fV fE s ℓ) (inj : V → Finset (Finset L))
  (b₀ t₀ : E₀ → Finset (Finset L)) (bP tP : P → Finset (Finset L)) (b₁ t₁ : E₁ → Finset (Finset L))
include hg

/-- The forest arriving at a vertex of the upper part. -/
theorem arriving_upper (v : V₀) :
    arriving N inj (joinArcs fE t₀ tP t₁) (fV (.inl v)) =
      arriving N₀ (upperInj fV s inj tP) t₀ v := by
  ext A
  simp only [arriving, upperInj, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
  rw [or_assoc]
  refine or_congr_right ?_
  constructor
  · rintro ⟨e, he, hA⟩
    obtain ⟨x, rfl⟩ := fE.surjective e
    rcases x with e | p | e
    · rw [hg.source₀] at he
      rw [joinArcs_inl] at hA
      exact Or.inr ⟨e, fV.injective he |> Sum.inl.inj, hA⟩ |>.symm.symm
    · rw [hg.sourceP] at he
      rw [joinArcs_inrl] at hA
      exact Or.inl ⟨p, Sum.inl.inj (fV.injective he), hA⟩
    · rw [hg.source₁] at he
      exact absurd (fV.injective he) (by simp)
  · rintro (⟨p, hp, hA⟩ | ⟨e, he, hA⟩)
    · exact ⟨fE (.inr (.inl p)), by rw [hg.sourceP, hp], by rwa [joinArcs_inrl]⟩
    · exact ⟨fE (.inl e), by rw [hg.source₀, he], by rwa [joinArcs_inl]⟩

/-- The forest arriving at a vertex of the lower part. -/
theorem arriving_lower (v : V₁) :
    arriving N inj (joinArcs fE t₀ tP t₁) (fV (.inr v)) =
      arriving N₁ (lowerInj fV inj) t₁ v := by
  ext A
  simp only [arriving, lowerInj, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
  refine or_congr_right ?_
  constructor
  · rintro ⟨e, he, hA⟩
    obtain ⟨x, rfl⟩ := fE.surjective e
    rcases x with e | p | e
    · rw [hg.source₀] at he
      exact absurd (fV.injective he) (by simp)
    · rw [hg.sourceP] at he
      exact absurd (fV.injective he) (by simp)
    · rw [hg.source₁] at he
      rw [joinArcs_inrr] at hA
      exact ⟨e, Sum.inr.inj (fV.injective he), hA⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨fE (.inr (.inr e)), by rw [hg.source₁, he], by rwa [joinArcs_inrr]⟩

/-- The arcs into a vertex of the upper part are those of the upper part. -/
theorem arcsInto_upper (v : V₀) :
    arcsInto N (fV (.inl v)) =
      (arcsInto N₀ v).map ⟨fun e => fE (.inl e), fun _ _ h => Sum.inl.inj (fE.injective h)⟩ := by
  ext e
  obtain ⟨x, rfl⟩ := fE.surjective e
  simp only [mem_arcsInto, mem_map]
  rcases x with e | p | e
  · rw [hg.target₀]
    constructor
    · intro h
      exact ⟨e, Sum.inl.inj (fV.injective h), rfl⟩
    · rintro ⟨e', he', h⟩
      rw [← Sum.inl.inj (fE.injective h), he']
  · rw [hg.targetP]
    constructor
    · intro h
      exact absurd (fV.injective h) (by simp)
    · rintro ⟨e', -, h⟩
      exact absurd (fE.injective h) (by simp)
  · rw [hg.target₁]
    constructor
    · intro h
      exact absurd (fV.injective h) (by simp)
    · rintro ⟨e', -, h⟩
      exact absurd (fE.injective h) (by simp)

/-- The arcs into a vertex of the lower part other than its root are those of the lower part. -/
theorem arcsInto_lower {v : V₁} (hv : v ≠ N₁.root) :
    arcsInto N (fV (.inr v)) =
      (arcsInto N₁ v).map ⟨fun e => fE (.inr (.inr e)),
        fun _ _ h => Sum.inr.inj (Sum.inr.inj (fE.injective h))⟩ := by
  ext e
  obtain ⟨x, rfl⟩ := fE.surjective e
  simp only [mem_arcsInto, mem_map]
  rcases x with e | p | e
  · rw [hg.target₀]
    constructor
    · intro h
      exact absurd (fV.injective h) (by simp)
    · rintro ⟨e', -, h⟩
      exact absurd (fE.injective h) (by simp)
  · rw [hg.targetP]
    constructor
    · intro h
      exact absurd (Sum.inr.inj (fV.injective h)) hv.symm
    · rintro ⟨e', -, h⟩
      exact absurd (fE.injective h) (by simp)
  · rw [hg.target₁]
    constructor
    · intro h
      exact ⟨e, Sum.inr.inj (fV.injective h), rfl⟩
    · rintro ⟨e', he', h⟩
      rw [← Sum.inr.inj (Sum.inr.inj (fE.injective h)), he']

/-- The arcs into the root of the lower part are the joining arcs. -/
theorem arcsInto_root :
    arcsInto N (fV (.inr N₁.root)) =
      (univ : Finset P).map ⟨fun p => fE (.inr (.inl p)),
        fun _ _ h => Sum.inl.inj (Sum.inr.inj (fE.injective h))⟩ := by
  ext e
  obtain ⟨x, rfl⟩ := fE.surjective e
  simp only [mem_arcsInto, mem_map, mem_univ, true_and]
  rcases x with e | p | e
  · rw [hg.target₀]
    constructor
    · intro h
      exact absurd (fV.injective h) (by simp)
    · rintro ⟨e', h⟩
      exact absurd (fE.injective h) (by simp)
  · exact ⟨fun _ => ⟨p, rfl⟩, fun _ => hg.targetP p⟩
  · rw [hg.target₁]
    constructor
    · intro h
      exact absurd (Sum.inr.inj (fV.injective h)) (hg.not_target_root e)
    · rintro ⟨e', h⟩
      exact absurd (fE.injective h) (by simp)

/-- The arcs into a vertex of the upper part, as a bijection. -/
def parentsUpper (v : V₀) :
    {e // N₀.graph.target e = v} ≃ {e // N.graph.target e = fV (.inl v)} :=
  Equiv.ofBijective (fun e => ⟨fE (.inl e.1), by rw [hg.target₀, e.2]⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (Sum.inl.inj (fE.injective (congrArg Subtype.val h)))
    · rintro ⟨e, he⟩
      have hm : e ∈ arcsInto N (fV (.inl v)) := mem_arcsInto.2 he
      rw [hg.arcsInto_upper] at hm
      obtain ⟨e', he', rfl⟩ := mem_map.1 hm
      exact ⟨⟨e', mem_arcsInto.1 he'⟩, rfl⟩)

/-- The arcs into a vertex of the lower part other than its root, as a bijection. -/
def parentsLower {v : V₁} (hv : v ≠ N₁.root) :
    {e // N₁.graph.target e = v} ≃ {e // N.graph.target e = fV (.inr v)} :=
  Equiv.ofBijective (fun e => ⟨fE (.inr (.inr e.1)), by rw [hg.target₁, e.2]⟩) (by
    constructor
    · intro a b h
      exact Subtype.ext (Sum.inr.inj (Sum.inr.inj (fE.injective (congrArg Subtype.val h))))
    · rintro ⟨e, he⟩
      have hm : e ∈ arcsInto N (fV (.inr v)) := mem_arcsInto.2 he
      rw [hg.arcsInto_lower hv] at hm
      obtain ⟨e', he', rfl⟩ := mem_map.1 hm
      exact ⟨⟨e', mem_arcsInto.1 he'⟩, rfl⟩)

/-- The factor of a vertex of the upper part. -/
theorem vertexWeight_upper (v : V₀) :
    vertexWeight N θ ρ inj (fV (.inl v)) (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) =
      vertexWeight N₀ θ₀ ρ (upperInj fV s inj tP) v b₀ t₀ := by
  unfold vertexWeight
  rw [hg.arriving_upper, hg.arcsInto_upper, prod_map]
  congr 1
  · refine allocationFactor_eq_of_equiv (hg.parentsUpper v) (Equiv.refl _)
      (fun e => (hg.inheritance₀ e.1).symm) fun a e => ?_
    have hb : joinArcs fE b₀ bP b₁ (hg.parentsUpper v e).1 = b₀ e.1 := joinArcs_inl fE b₀ bP b₁ e.1
    rw [hb]
    exact Iff.rfl
  · refine prod_congr rfl fun e _ => ?_
    change kingmanTransition (θ.length (fE (.inl e))) (joinArcs fE b₀ bP b₁ (fE (.inl e)))
      (joinArcs fE t₀ tP t₁ (fE (.inl e))) = _
    rw [joinArcs_inl, joinArcs_inl, hg.length₀]

/-- The factor of a vertex of the lower part other than its root. -/
theorem vertexWeight_lower {v : V₁} (hv : v ≠ N₁.root) :
    vertexWeight N θ ρ inj (fV (.inr v)) (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) =
      vertexWeight N₁ θ₁ ρ (lowerInj fV inj) v b₁ t₁ := by
  unfold vertexWeight
  rw [hg.arriving_lower, hg.arcsInto_lower hv, prod_map]
  congr 1
  · refine allocationFactor_eq_of_equiv (hg.parentsLower hv) (Equiv.refl _)
      (fun e => (hg.inheritance₁ e.1).symm) fun a e => ?_
    have hb : joinArcs fE b₀ bP b₁ (hg.parentsLower hv e).1 = b₁ e.1 := joinArcs_inrr fE b₀ bP b₁ e.1
    rw [hb]
    exact Iff.rfl
  · refine prod_congr rfl fun e _ => ?_
    change kingmanTransition (θ.length (fE (.inr (.inr e))))
      (joinArcs fE b₀ bP b₁ (fE (.inr (.inr e)))) (joinArcs fE t₀ tP t₁ (fE (.inr (.inr e)))) = _
    rw [joinArcs_inrr, joinArcs_inrr, hg.length₁]

/-- The factor of the root of the lower part. -/
theorem vertexWeight_root {AF : Finset (Finset L) → (P → Finset (Finset L)) → ℝ}
    (hAF : ∀ F bot, allocationFactor N θ ρ F (fV (.inr N₁.root)) bot =
      AF F fun p => bot (fE (.inr (.inl p)))) :
    vertexWeight N θ ρ inj (fV (.inr N₁.root)) (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) =
      AF (arriving N₁ (lowerInj fV inj) t₁ N₁.root) bP *
        ∏ p, kingmanTransition (ℓ p) (bP p) (tP p) := by
  unfold vertexWeight
  rw [hg.arriving_lower, hg.arcsInto_root, prod_map, hAF]
  congr 1
  · congr 1
    funext p
    simp
  · refine prod_congr rfl fun p _ => ?_
    change kingmanTransition (θ.length (fE (.inr (.inl p))))
      (joinArcs fE b₀ bP b₁ (fE (.inr (.inl p)))) (joinArcs fE t₀ tP t₁ (fE (.inr (.inl p)))) = _
    rw [joinArcs_inrl, joinArcs_inrl, hg.lengthP]

omit hg in
theorem prod_erase_root {M : Type*} [CommMonoid M] (f : V → M) (r₀ : V₀) :
    ∏ v ∈ univ.erase (fV (.inl r₀)), f v =
      (∏ v ∈ univ.erase r₀, f (fV (.inl v))) * ∏ w, f (fV (.inr w)) := by
  have : univ.erase (fV (.inl r₀)) =
      ((univ.erase r₀).disjSum (univ : Finset V₁)).map fV.toEmbedding := by
    ext v
    obtain ⟨x, rfl⟩ := fV.surjective v
    rcases x with x | x <;> simp
  rw [this, prod_map, prod_disjSum]
  rfl

/-- The weight of a history of the whole network, from the weights on the two parts. -/
theorem injWeight_eq {AF : Finset (Finset L) → (P → Finset (Finset L)) → ℝ}
    (hAF : ∀ F bot, allocationFactor N θ ρ F (fV (.inr N₁.root)) bot =
      AF F fun p => bot (fE (.inr (.inl p)))) :
    injWeight N θ ρ inj (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) =
      injWeight N₀ θ₀ ρ (upperInj fV s inj tP) b₀ t₀ *
        (injWeight N₁ θ₁ ρ (lowerInj fV inj) b₁ t₁ *
          (AF (arriving N₁ (lowerInj fV inj) t₁ N₁.root) bP *
            ∏ p, kingmanTransition (ℓ p) (bP p) (tP p))) := by
  unfold injWeight
  rw [hg.root, prod_erase_root, ← mul_prod_erase univ _ (mem_univ N₁.root),
    hg.vertexWeight_root inj b₀ t₀ bP tP b₁ t₁ hAF]
  rw [prod_congr rfl fun v _ => hg.vertexWeight_upper inj b₀ t₀ bP tP b₁ t₁ v,
    prod_congr rfl fun v hv => hg.vertexWeight_lower inj b₀ t₀ bP tP b₁ t₁ (ne_of_mem_erase hv)]
  ring

/-- **Gluing.** The law at the root of a network made of an upper and a lower part. -/
theorem rootDist_eq {AF : Finset (Finset L) → (P → Finset (Finset L)) → ℝ}
    (hAF : ∀ F bot, allocationFactor N θ ρ F (fV (.inr N₁.root)) bot =
      AF F fun p => bot (fE (.inr (.inl p)))) (F : Finset (Finset L)) :
    rootDist N θ ρ inj F =
      ∑ F₁, rootDist N₁ θ₁ ρ (lowerInj fV inj) F₁ *
        ∑ bP : P → Finset (Finset L), AF F₁ bP * ∑ tP : P → Finset (Finset L),
          (∏ p, kingmanTransition (ℓ p) (bP p) (tP p)) *
            rootDist N₀ θ₀ ρ (upperInj fV s inj tP) F := by
  rw [sum_rootDist_mul]
  unfold rootDist
  simp only [mul_sum]
  rw [sum_arcs fE]
  simp only [sum_arcs fE (α := Finset (Finset L)) (fun top => _ * _)]
  have hshuffle := sum_shuffle (A := E₀ → Finset (Finset L)) (B := P → Finset (Finset L))
    (C := E₁ → Finset (Finset L)) (D := E₀ → Finset (Finset L)) (F := P → Finset (Finset L))
    (G := E₁ → Finset (Finset L)) fun b₀ bP b₁ t₀ tP t₁ =>
      injWeight N θ ρ inj (joinArcs fE b₀ bP b₁) (joinArcs fE t₀ tP t₁) *
        if arriving N inj (joinArcs fE t₀ tP t₁) N.root = F then 1 else 0
  rw [hshuffle]
  refine sum_congr rfl fun b₁ _ => sum_congr rfl fun t₁ _ => sum_congr rfl fun bP _ =>
    sum_congr rfl fun tP _ => sum_congr rfl fun b₀ _ => sum_congr rfl fun t₀ _ => ?_
  rw [hg.injWeight_eq inj b₀ t₀ bP tP b₁ t₁ hAF, hg.root, hg.arriving_upper]
  ring

end IsGlued

end Glue

section Congr

variable {V E V' E' L : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E'] [Fintype L]
  [DecidableEq L]

/-- The law at the root does not depend on the names of the vertices and the arcs. -/
theorem rootDist_congr {N : RootedNetwork V E L} {N' : RootedNetwork V' E' L}
    {θ : RootedNetwork.MetricData E} {θ' : RootedNetwork.MetricData E'} {ρ : ℝ} (fV : V ≃ V')
    (fE : E ≃ E') (hs : ∀ e, N'.graph.source (fE e) = fV (N.graph.source e))
    (ht : ∀ e, N'.graph.target (fE e) = fV (N.graph.target e)) (hroot : N'.root = fV N.root)
    (hlen : ∀ e, θ'.length (fE e) = θ.length e)
    (hinh : ∀ e, θ'.inheritance (fE e) = θ.inheritance e) (inj : V' → Finset (Finset L))
    (F : Finset (Finset L)) :
    rootDist N' θ' ρ inj F = rootDist N θ ρ (fun v => inj (fV v)) F := by
  have harr : ∀ (top : E → Finset (Finset L)) (v : V),
      arriving N' inj (fun e => top (fE.symm e)) (fV v) =
        arriving N (fun v => inj (fV v)) top v := by
    intro top v
    ext A
    simp only [arriving, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    refine or_congr_right ?_
    constructor
    · rintro ⟨e, he, hA⟩
      obtain ⟨e, rfl⟩ := fE.surjective e
      rw [hs] at he
      exact ⟨e, fV.injective he, by simpa using hA⟩
    · rintro ⟨e, he, hA⟩
      exact ⟨fE e, by rw [hs, he], by simpa using hA⟩
  have hw : ∀ bot top : E → Finset (Finset L),
      injWeight N' θ' ρ inj (fun e => bot (fE.symm e)) (fun e => top (fE.symm e)) =
        injWeight N θ ρ (fun v => inj (fV v)) bot top := by
    intro bot top
    unfold injWeight
    have hfin : univ.erase N'.root = (univ.erase N.root).map fV.toEmbedding := by
      ext v
      obtain ⟨v, rfl⟩ := fV.surjective v
      simp [hroot]
    rw [hfin, prod_map]
    refine prod_congr rfl fun v _ => ?_
    change vertexWeight N' θ' ρ inj (fV v) _ _ = _
    unfold vertexWeight
    have hinto : arcsInto N' (fV v) = (arcsInto N v).map fE.toEmbedding := by
      ext e
      obtain ⟨e, rfl⟩ := fE.surjective e
      simp [ht]
    rw [harr, hinto, prod_map]
    congr 1
    · refine allocationFactor_eq_of_equiv
        (fE.subtypeEquiv (fun e => by rw [ht, fV.injective.eq_iff])) (Equiv.refl _)
        (fun e => (hinh e.1).symm) fun a e => ?_
      have hb : bot (fE.symm (fE e.1)) = bot e.1 := by simp
      change bot e.1 = _ ↔ bot (fE.symm (fE e.1)) = _
      rw [hb]
      exact Iff.rfl
    · refine prod_congr rfl fun e _ => ?_
      change kingmanTransition (θ'.length (fE e)) (bot (fE.symm (fE e))) (top (fE.symm (fE e))) = _
      rw [fE.symm_apply_apply, hlen]
  unfold rootDist
  rw [← (Equiv.arrowCongr fE (Equiv.refl (Finset (Finset L)))).sum_comp]
  refine sum_congr rfl fun bot _ => ?_
  rw [← (Equiv.arrowCongr fE (Equiv.refl (Finset (Finset L)))).sum_comp]
  refine sum_congr rfl fun top _ => ?_
  have h1 : (Equiv.arrowCongr fE (Equiv.refl (Finset (Finset L)))) bot =
      fun e => bot (fE.symm e) := rfl
  have h2 : (Equiv.arrowCongr fE (Equiv.refl (Finset (Finset L)))) top =
      fun e => top (fE.symm e) := rfl
  rw [h1, h2, hw, hroot, harr]

end Congr

section Instances

variable {V E L V₀ E₀ V₁ E₁ : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq L]
  [Fintype V₀] [Fintype E₀] [Fintype V₁] [Fintype E₁]
  {N : RootedNetwork V E L} {N₀ : RootedNetwork V₀ E₀ L} {N₁ : RootedNetwork V₁ E₁ L}
  {θ : RootedNetwork.MetricData E} {θ₀ : RootedNetwork.MetricData E₀}
  {θ₁ : RootedNetwork.MetricData E₁}

omit [Fintype V] [Fintype E] [Fintype L] [DecidableEq L] [Fintype V₀] [Fintype E₀] [Fintype V₁]
  [Fintype E₁] in
theorem sum_fun_unit {α : Type*} [Fintype α] (inst : Fintype (Unit → α)) (g : (Unit → α) → ℝ) :
    @Finset.sum _ ℝ _ (@univ _ inst) g = ∑ a, g fun _ => a := by
  exact ((Equiv.funUnique Unit α).symm.sum_comp g).symm

omit [Fintype V] [Fintype E] [Fintype L] [DecidableEq L] [Fintype V₀] [Fintype E₀] [Fintype V₁]
  [Fintype E₁] in
theorem sum_fun_bool {α : Type*} [Fintype α] (inst : Fintype (Bool → α)) (g : (Bool → α) → ℝ) :
    @Finset.sum _ ℝ _ (@univ _ inst) g = ∑ b₁, ∑ b₂, g fun p => cond p b₂ b₁ := by
  rw [← (Equiv.boolArrowEquivProd α).symm.sum_comp g, Fintype.sum_prod_type]
  refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₂ _ => ?_
  congr 1
  funext p
  cases p <;> rfl

/-- **One joining arc.** The forest arriving at the root of the lower part goes up the arc, and the
upper part sees the forest at the top of the arc. -/
theorem IsGlued.rootDist_eq_unit {ρ : ℝ} {fV : V₀ ⊕ V₁ ≃ V} {fE : E₀ ⊕ Unit ⊕ E₁ ≃ E} {s : Unit → V₀}
    {ℓ : Unit → ℝ} (hg : IsGlued N θ N₀ θ₀ N₁ θ₁ fV fE s ℓ) (hρ : 0 ≤ ρ)
    (h1 : θ.inheritance (fE (.inr (.inl ()))) = 1) (inj : V → Finset (Finset L))
    (F : Finset (Finset L)) :
    rootDist N θ ρ inj F =
      ∑ t, (∑ F₁, rootDist N₁ θ₁ ρ (lowerInj fV inj) F₁ * kingmanTransition (ℓ ()) F₁ t) *
        rootDist N₀ θ₀ ρ (upperInj fV s inj fun _ => t) F := by
  have hAF : ∀ (F : Finset (Finset L)) (bot : E → Finset (Finset L)),
      allocationFactor N θ ρ F (fV (.inr N₁.root)) bot =
        if bot (fE (.inr (.inl ()))) = F then (1 : ℝ) else 0 := by
    intro F bot
    refine allocationFactor_of_unique_arc hρ (hg.targetP ()) (fun g hg' => ?_) h1 F bot
    have hm : g ∈ arcsInto N (fV (.inr N₁.root)) := mem_arcsInto.2 hg'
    rw [hg.arcsInto_root] at hm
    obtain ⟨p, -, rfl⟩ := mem_map.1 hm
    rfl
  rw [hg.rootDist_eq inj (AF := fun F b => if b () = F then (1 : ℝ) else 0) hAF F]
  simp only [sum_fun_unit, Fintype.prod_unique, PUnit.default_eq_unit]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ite_true]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun F₁ _ => ?_
  ring

/-- The allocation at a reticulation with two parents, at inheritance correlation `0`: each root of the
forest takes the first parent, with probability `γ`, or the second. -/
def allocationTwo (γ : ℝ) (F : Finset (Finset L)) (b : Bool → Finset (Finset L)) : ℝ :=
  ∑ A ∈ (roots F).powerset, γ ^ #A * (1 - γ) ^ #(roots F \ A) *
    if b false = forestBelow F A ∧ b true = forestBelow F (roots F \ A) then 1 else 0

/-- The allocation at a vertex with exactly two parents, as a sum over the subsets of the roots. -/
theorem allocationFactor_eq_allocationTwo {v : V} {e : Bool → E} (he : ∀ p, N.graph.target (e p) = v)
    (huniq : ∀ g, N.graph.target g = v → g = e false ∨ g = e true) (hne : e false ≠ e true) {γ : ℝ}
    (h₁ : θ.inheritance (e false) = γ) (h₂ : θ.inheritance (e true) = 1 - γ)
    (F : Finset (Finset L)) (bot : E → Finset (Finset L)) :
    allocationFactor N θ 0 F v bot = allocationTwo γ F fun p => bot (e p) := by
  let e₁ : {g // N.graph.target g = v} := ⟨e false, he false⟩
  let e₂ : {g // N.graph.target g = v} := ⟨e true, he true⟩
  have hne' : e₁ ≠ e₂ := fun h => hne (congrArg Subtype.val h)
  have hcases : ∀ g : {g // N.graph.target g = v}, g = e₁ ∨ g = e₂ := fun g =>
    (huniq g.1 g.2).imp (fun h => Subtype.ext h) fun h => Subtype.ext h
  -- the subset of the roots taking the first parent
  let S : ({A // A ∈ roots F} → {g // N.graph.target g = v}) → Finset (Finset L) :=
    fun a => (univ.filter fun r => a r = e₁).image Subtype.val
  have hSsub : ∀ a, S a ⊆ roots F := fun a x hx => by
    obtain ⟨r, -, rfl⟩ := mem_image.1 hx
    exact r.2
  have hmem : ∀ a (r : {A // A ∈ roots F}), r.1 ∈ S a ↔ a r = e₁ := fun a r => by
    simp only [S, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨r', h, hr⟩
      rwa [← Subtype.ext hr]
    · exact fun h => ⟨r, h, rfl⟩
  have hS₂ : ∀ a, (univ.filter fun r => a r = e₂).image Subtype.val = roots F \ S a := fun a => by
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_sdiff]
    constructor
    · rintro ⟨r, h, rfl⟩
      refine ⟨r.2, fun hx => hne' ?_⟩
      rw [← (hmem a r).1 hx, h]
    · rintro ⟨hx, hxS⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      exact (hcases _).resolve_left fun h => hxS ((hmem a ⟨x, hx⟩).2 h)
  have hW : ∀ a, allocationWeight 0 (fun g : {g // N.graph.target g = v} => θ.inheritance g.1) a =
      γ ^ #(S a) * (1 - γ) ^ #(roots F \ S a) := fun a => by
    rw [allocationWeight_rho_zero, ← prod_filter_mul_prod_filter_not univ (fun r => a r = e₁)]
    congr 1
    · rw [prod_congr rfl (g := fun _ => γ) fun r hr => by
        rw [(mem_filter.1 hr).2]
        exact h₁]
      rw [prod_const]
      simp only [S]
      rw [card_image_of_injective _ Subtype.val_injective]
    · rw [prod_congr rfl (g := fun _ => 1 - γ) fun r hr => by
        rw [(hcases (a r)).resolve_left (mem_filter.1 hr).2]
        exact h₂]
      rw [prod_const, ← hS₂, card_image_of_injective _ Subtype.val_injective]
      congr 2
      ext r
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => (hcases _).resolve_left h, fun h h' => hne' (h'.symm.trans h)⟩
  unfold allocationFactor allocationTwo
  refine sum_nbij' S (fun A r => if r.1 ∈ A then e₁ else e₂) (fun a _ => mem_powerset.2 (hSsub a))
    (fun _ _ => mem_univ _) (fun a _ => ?_) (fun A hA => ?_) fun a _ => ?_
  · funext r
    by_cases h : a r = e₁
    · rw [ite_eq_left ((hmem a r).2 h), h]
    · rw [ite_eq_right fun hx => h ((hmem a r).1 hx)]
      exact ((hcases _).resolve_left h).symm
  · ext x
    simp only [S, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨r, h, rfl⟩
      by_contra hx
      rw [ite_eq_right hx] at h
      exact hne' h.symm
    · intro hx
      exact ⟨⟨x, mem_powerset.1 hA hx⟩, ite_eq_left hx, rfl⟩
  · rw [hW]
    have hcond : (∀ g : {g // N.graph.target g = v},
        bot g.1 = forestBelow F ((univ.filter fun r => a r = g).image Subtype.val)) ↔
        (bot (e false) = forestBelow F (S a) ∧ bot (e true) = forestBelow F (roots F \ S a)) := by
      constructor
      · intro h
        refine ⟨h e₁, ?_⟩
        have := h e₂
        rwa [hS₂] at this
      · rintro ⟨h₁', h₂'⟩ g
        rcases hcases g with rfl | rfl
        · exact h₁'
        · rw [hS₂]
          exact h₂'
    by_cases hc : bot (e false) = forestBelow F (S a) ∧ bot (e true) = forestBelow F (roots F \ S a)
    · rw [ite_eq_left (hcond.2 hc), ite_eq_left hc, mul_one]
    · rw [ite_eq_right (fun h => hc (hcond.1 h)), ite_eq_right hc, mul_zero]

/-- **Two joining arcs, entering a reticulation.** At inheritance correlation `0`, each root of the
forest at the reticulation takes the first arc with probability `γ`, and the second otherwise. -/
theorem IsGlued.rootDist_eq_bool {fV : V₀ ⊕ V₁ ≃ V} {fE : E₀ ⊕ Bool ⊕ E₁ ≃ E} {s : Bool → V₀}
    {ℓ : Bool → ℝ} (hg : IsGlued N θ N₀ θ₀ N₁ θ₁ fV fE s ℓ) {γ : ℝ}
    (h₁ : θ.inheritance (fE (.inr (.inl false))) = γ)
    (h₂ : θ.inheritance (fE (.inr (.inl true))) = 1 - γ) (inj : V → Finset (Finset L))
    (F : Finset (Finset L)) :
    rootDist N θ 0 inj F =
      ∑ F₁, rootDist N₁ θ₁ 0 (lowerInj fV inj) F₁ * ∑ A ∈ (roots F₁).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F₁ \ A) * ∑ t₁, ∑ t₂,
          kingmanTransition (ℓ false) (forestBelow F₁ A) t₁ *
            kingmanTransition (ℓ true) (forestBelow F₁ (roots F₁ \ A)) t₂ *
              rootDist N₀ θ₀ 0 (upperInj fV s inj fun p => cond p t₂ t₁) F := by
  have hAF : ∀ (F : Finset (Finset L)) (bot : E → Finset (Finset L)),
      allocationFactor N θ 0 F (fV (.inr N₁.root)) bot =
        allocationTwo γ F fun p => bot (fE (.inr (.inl p))) := by
    intro F bot
    refine allocationFactor_eq_allocationTwo (e := fun p => fE (.inr (.inl p))) hg.targetP
      (fun g hg' => ?_) (fun h => by simpa using fE.injective h) h₁ h₂ F bot
    have hm : g ∈ arcsInto N (fV (.inr N₁.root)) := mem_arcsInto.2 hg'
    rw [hg.arcsInto_root] at hm
    obtain ⟨p, -, rfl⟩ := mem_map.1 hm
    cases p
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [hg.rootDist_eq inj hAF F]
  refine sum_congr rfl fun F₁ _ => ?_
  congr 1
  unfold allocationTwo
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun A hA => ?_
  rw [sum_fun_bool]
  rw [Finset.sum_eq_single (forestBelow F₁ A), Finset.sum_eq_single (forestBelow F₁ (roots F₁ \ A))]
  · simp only [Bool.cond_false, Bool.cond_true, and_self, ite_true, mul_one]
    congr 1
    rw [sum_fun_bool]
    refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => ?_
    simp [mul_comm]
  · intro b _ hb'
    simp [hb']
  · simp
  · intro b _ hb'
    refine sum_eq_zero fun b₂ _ => ?_
    simp [hb']
  · simp

end Instances

end Phylogenetics.NMSC
