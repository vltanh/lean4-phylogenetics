module

public import Phylogenetics.Coalescent.Relabel
public import Phylogenetics.NMSC.InducedSuppress

/-!
# Restricting the network multispecies coalescent to the taxa `Y` below a stable ancestor

The lineages of the taxa `Y` stay on the arcs ancestral to `Y`, and below a stable ancestor `l` of `Y`
every arc entering an ancestral vertex other than `l` is an arc of `belowNetwork`. So the forests below
`l` have the same law in the network and in `belowNetwork`, whose taxa are `↥Y` and whose forests are
identified along `Subtype.val`.

## Main results

* `embedFamily`, `kingmanTransition_embedFamily`: Kingman's coalescent is natural with respect to
  injections of the lineages.
* `sum_sum_strictBelow_eq`: the law of the forest arriving at `l` is the same in the two networks.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics

namespace NMSC

open RootedNetwork

/-! ### Injections of the lineages -/

section Embed

variable {L M : Type*} [DecidableEq L] [DecidableEq M]

/-- The image of a family of clusters under an injection of the lineages. -/
def embedFamily (ι : L ↪ M) (F : Finset (Finset L)) : Finset (Finset M) :=
  F.image fun A => A.map ι

omit [DecidableEq L] in
theorem embedFamily_injective (ι : L ↪ M) : Function.Injective (embedFamily ι) :=
  Finset.image_injective (Finset.map_injective ι)

omit [DecidableEq L] in
theorem map_mem_embedFamily {ι : L ↪ M} {F : Finset (Finset L)} {A : Finset L} :
    A.map ι ∈ embedFamily ι F ↔ A ∈ F :=
  (Finset.map_injective ι).mem_finset_image

omit [DecidableEq L] in
theorem mem_embedFamily {ι : L ↪ M} {F : Finset (Finset L)} {B : Finset M} :
    B ∈ embedFamily ι F ↔ ∃ A ∈ F, A.map ι = B := by
  simp [embedFamily]

theorem embedFamily_union (ι : L ↪ M) (F G : Finset (Finset L)) :
    embedFamily ι (F ∪ G) = embedFamily ι F ∪ embedFamily ι G :=
  image_union _ _

omit [DecidableEq L] in
@[simp] theorem embedFamily_empty (ι : L ↪ M) : embedFamily ι ∅ = ∅ := image_empty _

theorem embedFamily_biUnion {κ : Type*} [DecidableEq κ] (ι : L ↪ M) (s : Finset κ)
    (f : κ → Finset (Finset L)) :
    embedFamily ι (s.biUnion f) = s.biUnion fun i => embedFamily ι (f i) := by
  unfold embedFamily
  rw [biUnion_image]

/-- The roots of the image. -/
theorem roots_embedFamily [Fintype L] [Fintype M] (ι : L ↪ M) (F : Finset (Finset L)) :
    roots (embedFamily ι F) = embedFamily ι (roots F) := by
  unfold roots embedFamily
  rw [filter_image]
  congr 1
  refine filter_congr fun A _ => ?_
  rw [Finset.forall_mem_image]
  constructor
  · intro h B hB hAB
    exact Finset.map_injective _ (h hB (Finset.map_subset_map.2 hAB))
  · intro h B hB hAB
    rw [h B hB (Finset.map_subset_map.1 hAB)]

theorem forestBelow_embedFamily [Fintype L] [Fintype M] (ι : L ↪ M) (F A : Finset (Finset L)) :
    forestBelow (embedFamily ι F) (embedFamily ι A) = embedFamily ι (forestBelow F A) := by
  ext D
  rw [mem_forestBelow, mem_embedFamily, mem_embedFamily]
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, C, hC, hDC⟩
    obtain ⟨C', hC', rfl⟩ := mem_embedFamily.1 hC
    exact ⟨B, mem_forestBelow.2 ⟨hB, C', hC', Finset.map_subset_map.1 hDC⟩, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hB', C, hC, hBC⟩ := mem_forestBelow.1 hB
    exact ⟨⟨B, hB', rfl⟩, C.map ι, map_mem_embedFamily.2 hC, Finset.map_subset_map.2 hBC⟩

section Kernels

variable [Fintype L] [Fintype M]

/-- The generator of Kingman's coalescent is natural under injections of the lineages. -/
theorem kingmanGenerator_embedFamily (ι : L ↪ M) (F G : Finset (Finset L)) :
    kingmanGenerator (embedFamily ι F) (embedFamily ι G) = kingmanGenerator F G := by
  unfold kingmanGenerator
  rw [roots_embedFamily]
  have hcard : #(embedFamily ι (roots F)) = #(roots F) :=
    card_image_of_injective _ (Finset.map_injective ι)
  by_cases hGF : G = F
  · subst hGF
    simp [hcard]
  · have hne : embedFamily ι G ≠ embedFamily ι F := fun h => hGF (embedFamily_injective ι h)
    rw [ite_eq_right hne, ite_eq_right hGF]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨A', hA', B', hB', hAB', hF⟩
      obtain ⟨A, hA, rfl⟩ := mem_embedFamily.1 hA'
      obtain ⟨B, hB, rfl⟩ := mem_embedFamily.1 hB'
      refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), embedFamily_injective ι ?_⟩
      rw [hF]
      unfold embedFamily
      rw [image_insert, Finset.map_union]
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      refine ⟨A.map ι, map_mem_embedFamily.2 hA, B.map ι, map_mem_embedFamily.2 hB,
        fun h => hAB (Finset.map_injective _ h), ?_⟩
      unfold embedFamily
      rw [image_insert, Finset.map_union]

/-- The coalescent stays in the families on the image of the injection. -/
theorem kingmanGenerator_embedFamily_of_notMem (ι : L ↪ M) (F : Finset (Finset L))
    {H : Finset (Finset M)} (hH : H ∉ Set.range (embedFamily ι)) :
    kingmanGenerator (embedFamily ι F) H = 0 := by
  unfold kingmanGenerator
  rw [ite_eq_right fun h => hH ⟨F, h.symm⟩, ite_eq_right]
  rintro ⟨A', hA', B', hB', -, rfl⟩
  rw [roots_embedFamily] at hA' hB'
  obtain ⟨A, -, rfl⟩ := mem_embedFamily.1 hA'
  obtain ⟨B, -, rfl⟩ := mem_embedFamily.1 hB'
  refine hH ⟨insert (A ∪ B) F, ?_⟩
  unfold embedFamily
  rw [image_insert, Finset.map_union]

theorem kingmanGenerator_pow_embedFamily (ι : L ↪ M) (n : ℕ) (F G : Finset (Finset L)) :
    (kingmanGenerator ^ n) (embedFamily ι F) (embedFamily ι G) = (kingmanGenerator ^ n) F G := by
  induction n generalizing F with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, (embedFamily_injective ι).eq_iff]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, pow_succ', Matrix.mul_apply]
    have hsub : ∑ H ∈ univ.image (embedFamily ι),
          kingmanGenerator (embedFamily ι F) H * (kingmanGenerator ^ n) H (embedFamily ι G) =
        ∑ H, kingmanGenerator (embedFamily ι F) H * (kingmanGenerator ^ n) H (embedFamily ι G) := by
      refine sum_subset (subset_univ _) fun H _ hH => ?_
      rw [kingmanGenerator_embedFamily_of_notMem ι F, zero_mul]
      rintro ⟨F', rfl⟩
      exact hH (mem_image_of_mem _ (mem_univ _))
    rw [← hsub, sum_image fun _ _ _ _ h => embedFamily_injective ι h]
    exact sum_congr rfl fun F' _ => by rw [kingmanGenerator_embedFamily, ih]

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the exponential of a real matrix are given by the exponential series. -/
private theorem emb_hasSum_exp_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (i j : κ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ))⁻¹ * (A ^ n) i j) (NormedSpace.exp A i j) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h2 := Pi.hasSum.mp (Pi.hasSum.mp h i) j
  simpa using h2

/-- **Kingman's coalescent is natural with respect to injections of the lineages.** -/
theorem kingmanTransition_embedFamily (ι : L ↪ M) (t : ℝ) (F G : Finset (Finset L)) :
    kingmanTransition t (embedFamily ι F) (embedFamily ι G) = kingmanTransition t F G := by
  have h1 := emb_hasSum_exp_apply (t • kingmanGenerator (L := M)) (embedFamily ι F) (embedFamily ι G)
  have h2 := emb_hasSum_exp_apply (t • kingmanGenerator (L := L)) F G
  refine h1.unique ?_
  convert h2 using 1
  · funext n
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, kingmanGenerator_pow_embedFamily]
  · rfl

end Kernels

end Embed

/-! ### Membership in the forests of a history -/

section Membership

variable {V E X : Type*} [Fintype E] [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype E] in
theorem mem_taxaInj {Y : Finset X} {v : V} {A : Finset X} :
    A ∈ taxaInj N Y v ↔ ∃ x, x ∈ Y ∧ N.leaf x = v ∧ {x} = A := by
  simp [taxaInj, and_assoc]

omit [Fintype X] in
theorem mem_arriving {inj : V → Finset (Finset X)} {top : E → Finset (Finset X)} {v : V}
    {A : Finset X} :
    A ∈ arriving N inj top v ↔ A ∈ inj v ∨ ∃ e, N.graph.source e = v ∧ A ∈ top e := by
  simp [arriving]

end Membership

/-- A sum over the part of a finite type where a predicate holds, along an injection. -/
theorem sum_ite_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → Prop) (q : κ → Prop)
    [DecidablePred p] [DecidablePred q] (g : ι → κ) (f : κ → ℝ) (hg : Function.Injective g)
    (hp : ∀ i, p i ↔ q (g i)) (hs : ∀ k, q k → ∃ i, g i = k) :
    ∑ i, (if p i then f (g i) else 0) = ∑ k, if q k then f k else 0 := by
  rw [← sum_filter, ← sum_filter]
  refine sum_bij (fun i _ => g i) (fun i hi => mem_filter.2 ⟨mem_univ _, (hp i).1 (mem_filter.1 hi).2⟩)
    (fun i _ i' _ h => hg h) (fun k hk => ?_) fun _ _ => rfl
  obtain ⟨i, rfl⟩ := hs k (mem_filter.1 hk).2
  exact ⟨i, mem_filter.2 ⟨mem_univ _, (hp i).2 (mem_filter.1 hk).2⟩, rfl⟩

/-! ### Paths avoiding a stable ancestor -/

section Paths

variable {V E X : Type*} {N : RootedNetwork V E X}

/-- A path from a vertex strictly below `l` avoids `l`. -/
theorem pathAvoiding_of_below (hN : N.IsPhylogenetic) {l u v : V} (hlu : N.graph.Reaches l u)
    (hul : u ≠ l) (h : N.graph.Reaches u v) :
    Relation.ReflTransGen (fun a b => N.graph.Adj a b ∧ a ≠ l ∧ b ≠ l) u v ∧ v ≠ l := by
  induction h with
  | refl => exact ⟨.refl, hul⟩
  | @tail a b hua hab ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hb : b ≠ l := by
      rintro rfl
      exact hul (eq_of_reaches_of_reaches hN.acyclic (hua.tail hab) hlu)
    exact ⟨ih1.tail ⟨hab, ih2, hb⟩, hb⟩

/-- An arc entering the part strictly below a stable ancestor from outside what is below it has no
taxon of `Y` below it. -/
theorem not_reaches_leaf_of_isStableAncestor (hN : N.IsPhylogenetic) {Y : Set X} {l : V}
    (hst : N.IsStableAncestor Y l) {e : E} (hlt : N.graph.Reaches l (N.graph.target e))
    (hne : N.graph.target e ≠ l) (hs : ¬ N.graph.Reaches l (N.graph.source e)) {x : X} (hx : x ∈ Y) :
    ¬ N.graph.Reaches (N.graph.target e) (N.leaf x) := by
  intro hr
  obtain ⟨h1, h2⟩ := pathAvoiding_of_below hN hlt hne hr
  have h0 := RootedNetwork.avoiding_of_not_reaches (hN.root_reaches (N.graph.source e)) hs
  have hsl : N.graph.source e ≠ l := by
    rintro h
    exact hs (h ▸ .refl)
  refine hst x hx ⟨?_, h2, (h0.tail ⟨⟨e, rfl, rfl⟩, hsl, hne⟩).trans h1⟩
  intro hrl
  exact hs (hrl ▸ hN.root_reaches _)

end Paths

/-! ### The vertices strictly below a vertex -/

section Strict

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X}

variable (N) in
/-- The vertices strictly below `l`. -/
def strictBelow (l : V) : Finset V := univ.filter fun v => N.graph.Reaches l v ∧ v ≠ l

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem mem_strictBelow {l v : V} : v ∈ strictBelow N l ↔ N.graph.Reaches l v ∧ v ≠ l := by
  simp [strictBelow]

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem target_mem_strictBelow (hN : N.IsPhylogenetic) {l : V} {e : E}
    (hs : N.graph.Reaches l (N.graph.source e)) : N.graph.target e ∈ strictBelow N l := by
  refine mem_strictBelow.2 ⟨hs.tail ⟨e, rfl, rfl⟩, ?_⟩
  intro h
  exact not_reaches_target_source hN.acyclic e (h ▸ hs)

omit [Fintype E] [Fintype X] [DecidableEq X] in
theorem downClosed_strictBelow (hN : N.IsPhylogenetic) (l : V) : DownClosed N (strictBelow N l) :=
  fun _ he => target_mem_strictBelow hN (mem_strictBelow.1 he).1

omit [Fintype X] [DecidableEq X] in
theorem root_notMem_strictBelow (hN : N.IsPhylogenetic) (l : V) : N.root ∉ strictBelow N l := by
  intro h
  obtain ⟨hr, hne⟩ := mem_strictBelow.1 h
  rcases Relation.ReflTransGen.cases_tail hr with h' | ⟨_, -, f, -, hf⟩
  · exact hne h'
  · exact target_ne_root hN f hf

end Strict

/-! ### The induced subgraph below a stable ancestor -/

section Below

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]
variable {N : RootedNetwork V E X} {θ : RootedNetwork.MetricData E} {ρ : ℝ}
variable {l : V} {Q : Finset X} [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]

/-- The taxa of `Q` as taxa of the network. -/
abbrev taxonEmb (Q : Finset X) : (Q : Set X) ↪ X := Function.Embedding.subtype _

/-- The forests on `Q` as forests on all the taxa, on the arcs of the induced subgraph, and the empty
forest on the other arcs. -/
def liftArcs (t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) (e : E) :
    Finset (Finset X) :=
  if h : e ∈ N.belowArcs l (Q : Set X) then embedFamily (taxonEmb Q) (t ⟨e, h⟩) else ∅

omit [Fintype V] [Fintype E] [Fintype X] [Fintype (Q : Set X)] [DecidableEq (Q : Set X)] in
theorem liftArcs_of_mem (t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)))
    (e : N.belowArcs l (Q : Set X)) : liftArcs t e.1 = embedFamily (taxonEmb Q) (t e) := by
  unfold liftArcs
  exact dite_eq_left_of_eq_true (eq_true e.2)

omit [Fintype V] [Fintype E] [Fintype X] [Fintype (Q : Set X)] [DecidableEq (Q : Set X)] in
theorem liftArcs_of_notMem (t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) {e : E}
    (h : e ∉ N.belowArcs l (Q : Set X)) : liftArcs t e = ∅ := by
  unfold liftArcs
  exact dite_eq_right_of_eq_false (eq_false h)

/-- The clusters on `Q` of a family of clusters. -/
def downFamily (F : Finset (Finset X)) : Finset (Finset (Q : Set X)) :=
  F.image fun A => A.subtype (· ∈ (Q : Set X))

omit [Fintype X] [Fintype (Q : Set X)] in
theorem embedFamily_downFamily {F : Finset (Finset X)} (hF : ∀ A ∈ F, A ⊆ Q) :
    embedFamily (taxonEmb Q) (downFamily F) = F := by
  unfold embedFamily downFamily
  rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  refine image_congr fun A hA => ?_
  exact Finset.subtype_map_of_mem fun x hx => hF A hA hx

omit [Fintype X] [Fintype (Q : Set X)] in
theorem downFamily_embedFamily (F : Finset (Finset (Q : Set X))) :
    downFamily (embedFamily (taxonEmb Q) F) = F := by
  unfold embedFamily downFamily
  rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  refine image_congr fun A _ => ?_
  ext x
  simp

variable {hl : l ∈ N.ancestralVertices (Q : Set X)}
  {hleaf : ∀ x ∈ (Q : Set X), N.graph.Reaches l (N.leaf x)}

omit [Fintype V] [Fintype E] in
/-- The singleton lineages of the taxa at a vertex of the induced subgraph. -/
theorem taxaInj_below (u : N.belowVertices l (Q : Set X)) :
    taxaInj N Q u.1 = embedFamily (taxonEmb Q)
      (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ u) := by
  ext A
  rw [mem_taxaInj, mem_embedFamily]
  constructor
  · rintro ⟨x, hxQ, hxu, rfl⟩
    exact ⟨{⟨x, hxQ⟩}, mem_taxaInj.2 ⟨⟨x, hxQ⟩, mem_univ _, Subtype.ext hxu, rfl⟩, by simp⟩
  · rintro ⟨A', hA', rfl⟩
    obtain ⟨x', -, hxu, rfl⟩ := mem_taxaInj.1 hA'
    exact ⟨x'.1, x'.2, congrArg Subtype.val hxu, by simp⟩

variable [Fintype (N.belowVertices l (Q : Set X))] [Fintype (N.belowArcs l (Q : Set X))]

omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] in
/-- The forest arriving at a vertex of the induced subgraph. -/
theorem arriving_below (t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)))
    (u : N.belowVertices l (Q : Set X)) :
    arriving N (taxaInj N Q) (liftArcs t) u.1 = embedFamily (taxonEmb Q)
      (arriving (N.belowNetwork l (Q : Set X) hl hleaf)
        (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) t u) := by
  ext C
  rw [mem_arriving, mem_embedFamily]
  constructor
  · rintro (hC | ⟨e, he, hC⟩)
    · rw [taxaInj_below (hl := hl) (hleaf := hleaf) u] at hC
      obtain ⟨A, hA, rfl⟩ := mem_embedFamily.1 hC
      exact ⟨A, mem_arriving.2 (Or.inl hA), rfl⟩
    · by_cases hm : e ∈ N.belowArcs l (Q : Set X)
      · rw [liftArcs_of_mem t ⟨e, hm⟩] at hC
        obtain ⟨A, hA, rfl⟩ := mem_embedFamily.1 hC
        exact ⟨A, mem_arriving.2 (Or.inr ⟨⟨e, hm⟩, Subtype.ext he, hA⟩), rfl⟩
      · rw [liftArcs_of_notMem t hm] at hC
        exact absurd hC (notMem_empty _)
  · rintro ⟨A, hA, rfl⟩
    rcases mem_arriving.1 hA with hA | ⟨e, he, hA⟩
    · refine Or.inl ?_
      rw [taxaInj_below (hl := hl) (hleaf := hleaf) u]
      exact map_mem_embedFamily.2 hA
    · refine Or.inr ⟨e.1, congrArg Subtype.val he, ?_⟩
      rw [liftArcs_of_mem t e]
      exact map_mem_embedFamily.2 hA

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] [Fintype (Q : Set X)]
  [DecidableEq (Q : Set X)] [Fintype (N.belowVertices l (Q : Set X))]
  [Fintype (N.belowArcs l (Q : Set X))] in
/-- An arc entering a vertex of the induced subgraph other than the stable ancestor `l` is an arc of
the induced subgraph. -/
theorem mem_belowArcs_of_target_eq (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l) {e : E} (he : N.graph.target e = u.1) :
    e ∈ N.belowArcs l (Q : Set X) := by
  have han : e ∈ N.ancestralArcs (Q : Set X) := by
    change N.graph.target e ∈ N.ancestralVertices (Q : Set X)
    rw [he]
    exact u.2.2
  refine ⟨?_, han⟩
  by_contra hs
  obtain ⟨x, hx, hr⟩ := u.2.2
  exact not_reaches_leaf_of_isStableAncestor hN hst (he ▸ u.2.1) (he ▸ hu) hs hx (he ▸ hr)

/-- The arcs entering a vertex of the induced subgraph other than the stable ancestor `l` are those
entering it in the network. -/
def belowArcsInto (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l) :
    {e // (N.belowNetwork l (Q : Set X) hl hleaf).graph.target e = u} ≃
      {e // N.graph.target e = u.1} where
  toFun e := ⟨e.1.1, congrArg Subtype.val e.2⟩
  invFun e := ⟨⟨e.1, mem_belowArcs_of_target_eq hN hst u hu e.2⟩, Subtype.ext e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The roots of a forest on `Q` and of its image. -/
def rootsEmbedEquiv (F : Finset (Finset (Q : Set X))) :
    {A // A ∈ roots F} ≃ {A // A ∈ roots (embedFamily (taxonEmb Q) F)} :=
  Equiv.ofBijective
    (fun A => ⟨A.1.map (taxonEmb Q), by
      rw [roots_embedFamily]
      exact map_mem_embedFamily.2 A.2⟩)
    ⟨fun A B h => Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h)), fun B => by
      have hB : B.1 ∈ embedFamily (taxonEmb Q) (roots F) := by
        rw [← roots_embedFamily]
        exact B.2
      obtain ⟨A, hA, hAB⟩ := mem_embedFamily.1 hB
      exact ⟨⟨A, hA⟩, Subtype.ext hAB⟩⟩

omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] in
/-- The allocation at a vertex of the induced subgraph other than the stable ancestor `l`. -/
theorem allocationFactor_below (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (F : Finset (Finset (Q : Set X))) (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l)
    (b : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) :
    allocationFactor N θ ρ (embedFamily (taxonEmb Q) F) u.1 (liftArcs b) =
      allocationFactor (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ F u
        b := by
  refine allocationFactor_eq_of_equiv (belowArcsInto hN hst u hu) (rootsEmbedEquiv F)
    (fun _ => rfl) fun a e => ?_
  have hR : ∀ (R : Finset {A // A ∈ roots F})
      (R' : Finset {A // A ∈ roots (embedFamily (taxonEmb Q) F)}),
      (∀ r, r ∈ R' ↔ a ((rootsEmbedEquiv F).symm r) = e) → (∀ r, r ∈ R ↔ a r = e) →
      R'.image Subtype.val = embedFamily (taxonEmb Q) (R.image Subtype.val) := by
    intro R R' hR' hR
    ext C
    simp only [mem_embedFamily, mem_image]
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨r₀, rfl⟩ := (rootsEmbedEquiv F).surjective r
      have hr' := (hR' _).1 hr
      rw [Equiv.symm_apply_apply] at hr'
      exact ⟨r₀.1, ⟨r₀, (hR _).2 hr', rfl⟩, rfl⟩
    · rintro ⟨_, ⟨r₀, hr, rfl⟩, rfl⟩
      exact ⟨rootsEmbedEquiv F r₀, (hR' _).2 (by rw [Equiv.symm_apply_apply]; exact (hR _).1 hr),
        rfl⟩
  rw [hR (univ.filter fun r => a r = e) _ (fun r => by simp) (fun r => by simp),
    forestBelow_embedFamily]
  change _ ↔ liftArcs b e.1.1 = _
  rw [liftArcs_of_mem b e.1, (embedFamily_injective _).eq_iff]
  convert Iff.rfl

omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] in
/-- Kingman's coalescent on the arcs entering a vertex of the induced subgraph other than `l`. -/
theorem prod_kingmanTransition_below (hN : N.IsPhylogenetic)
    (hst : N.IsStableAncestor (Q : Set X) l) (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l)
    (b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) :
    ∏ e ∈ arcsInto N u.1, kingmanTransition (θ.length e) (liftArcs b e) (liftArcs t e) =
      ∏ e ∈ arcsInto (N.belowNetwork l (Q : Set X) hl hleaf) u,
        kingmanTransition ((belowMetric l (Q : Set X) θ).length e) (b e) (t e) := by
  symm
  refine prod_bij (fun e _ => e.1) (fun e he => ?_) (fun e _ e' _ h => Subtype.ext h)
    (fun e he => ?_) fun e _ => ?_
  · exact mem_arcsInto.2 (congrArg Subtype.val (mem_arcsInto.1 he))
  · have he' : N.graph.target e = u.1 := mem_arcsInto.1 he
    exact ⟨⟨e, mem_belowArcs_of_target_eq hN hst u hu he'⟩, mem_arcsInto.2 (Subtype.ext he'), rfl⟩
  · rw [liftArcs_of_mem b e, liftArcs_of_mem t e, kingmanTransition_embedFamily]
    rfl

omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] in
/-- The factor of a vertex of the induced subgraph other than the stable ancestor `l`. -/
theorem vertexWeight_below (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l)
    (b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) :
    vertexWeight N θ ρ (taxaInj N Q) u.1 (liftArcs b) (liftArcs t) =
      vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
        (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t := by
  unfold vertexWeight
  rw [arriving_below (hl := hl) (hleaf := hleaf), allocationFactor_below hN hst _ u hu,
    prod_kingmanTransition_below hN hst u hu]

omit [Fintype V] in
/-- No lineages arrive at a vertex that is not ancestral to the taxa: the allocation is trivial. -/
theorem allocationFactor_empty_eq_one {v : V} {b : E → Finset (Finset X)}
    (h : ∀ e, N.graph.target e = v → b e = ∅) :
    allocationFactor N θ ρ (∅ : Finset (Finset X)) v b = 1 := by
  have hemp : IsEmpty {A // A ∈ roots (∅ : Finset (Finset X))} :=
    ⟨fun A => by simpa using A.2⟩
  unfold allocationFactor
  rw [Fintype.sum_subsingleton _ (fun r => isEmptyElim r)]
  rw [ite_eq_left]
  · simp [allocationWeight]
  · intro e
    rw [h e.1 e.2]
    ext A
    simp [mem_forestBelow]

omit [Fintype V] [Fintype (Q : Set X)] [DecidableEq (Q : Set X)]
  [Fintype (N.belowVertices l (Q : Set X))] [Fintype (N.belowArcs l (Q : Set X))] in
/-- The factor of a vertex that is not ancestral to the taxa, on a history from the induced
subgraph. -/
theorem vertexWeight_of_notMem_ancestral {u : V}
    (hu : u ∉ N.ancestralVertices (Q : Set X))
    (b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) :
    vertexWeight N θ ρ (taxaInj N Q) u (liftArcs b) (liftArcs t) = 1 := by
  have hnot : ∀ {e : E}, N.graph.target e = u → e ∉ N.belowArcs l (Q : Set X) := by
    intro e he hm
    exact hu (he ▸ hm.2)
  have harr : arriving N (taxaInj N Q) (liftArcs t) u = ∅ := by
    ext C
    simp only [mem_arriving, notMem_empty, iff_false, not_or, not_exists, not_and]
    refine ⟨fun hC => ?_, fun e he hC => ?_⟩
    · obtain ⟨x, hx, hxu, -⟩ := mem_taxaInj.1 hC
      exact hu ⟨x, hx, hxu ▸ .refl⟩
    · by_cases hm : e ∈ N.belowArcs l (Q : Set X)
      · exact hu (he ▸ N.source_mem_ancestralVertices hm.2)
      · rw [liftArcs_of_notMem t hm] at hC
        exact notMem_empty _ hC
  unfold vertexWeight
  rw [harr, allocationFactor_empty_eq_one fun e he => liftArcs_of_notMem b (hnot he), one_mul]
  refine prod_eq_one fun e he => ?_
  have he' := mem_arcsInto.1 he
  rw [liftArcs_of_notMem b (hnot he'), liftArcs_of_notMem t (hnot he'),
    kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]

/-- The factors of the vertices strictly below the stable ancestor `l`, on a history from the induced
subgraph. -/
theorem prod_strictBelow_liftArcs (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (hNL : (N.belowNetwork l (Q : Set X) hl hleaf).IsPhylogenetic)
    (b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) :
    ∏ u ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) u (liftArcs b) (liftArcs t) =
      ∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
          (N.belowNetwork l (Q : Set X) hl hleaf).root,
        vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
          (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t := by
  have hroot : ∀ u : N.belowVertices l (Q : Set X),
      u ≠ (N.belowNetwork l (Q : Set X) hl hleaf).root → u.1 ≠ l := fun u hu h =>
    hu (Subtype.ext h)
  have hval : ∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
        (N.belowNetwork l (Q : Set X) hl hleaf).root,
      vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
        (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t =
      ∏ v ∈ (strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
        (N.belowNetwork l (Q : Set X) hl hleaf).root).image Subtype.val,
        vertexWeight N θ ρ (taxaInj N Q) v (liftArcs b) (liftArcs t) := by
    rw [prod_image fun _ _ _ _ h => Subtype.ext h]
    exact prod_congr rfl fun u hu =>
      (vertexWeight_below hN hst u (hroot u (mem_strictBelow.1 hu).2) b t).symm
  rw [hval]
  symm
  refine prod_subset (fun v hv => ?_) fun v hv hvn => ?_
  · obtain ⟨u, hu, rfl⟩ := mem_image.1 hv
    exact mem_strictBelow.2 ⟨u.2.1, hroot u (mem_strictBelow.1 hu).2⟩
  · refine vertexWeight_of_notMem_ancestral (fun ha => hvn ?_) b t
    obtain ⟨hr, hne⟩ := mem_strictBelow.1 hv
    exact mem_image.2 ⟨⟨v, hr, ha⟩, mem_strictBelow.2 ⟨hNL.root_reaches _,
      fun h => hne (congrArg Subtype.val h)⟩, rfl⟩

omit [Fintype (Q : Set X)] [DecidableEq (Q : Set X)] [Fintype (N.belowVertices l (Q : Set X))]
  [Fintype (N.belowArcs l (Q : Set X))] in
/-- On a history of nonzero weight, the arcs not in the induced subgraph are empty, and the forests
on the others are forests on the taxa `Q`. -/
theorem support_strictBelow (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    {bot top : E → Finset (Finset X)}
    (h : ∏ u ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) u bot top ≠ 0) {e : E}
    (he : N.graph.target e ∈ strictBelow N l) :
    (e ∉ N.belowArcs l (Q : Set X) → bot e = ∅ ∧ top e = ∅) ∧ (∀ A ∈ bot e, A ⊆ Q) ∧
      ∀ A ∈ top e, A ⊆ Q := by
  have hF := frontier_of_prod_ne_zero hN (validInj_taxaInj Q) (downClosed_strictBelow hN l) h
  have hgt := hF.good_top e he
  have hgb := hF.good_bot e he
  have hw : vertexWeight N θ ρ (taxaInj N Q) (N.graph.target e) bot top ≠ 0 :=
    prod_ne_zero_iff.1 h _ he
  have hK : kingmanTransition (θ.length e) (bot e) (top e) ≠ 0 :=
    prod_ne_zero_iff.1 (right_ne_zero_of_mul hw) e (mem_arcsInto.2 rfl)
  have hlin : lineages (top e) = lineages (bot e) := (kingmanTransition_support_good hgb hK).2.2
  have hbelow : ∀ x ∈ lineages (top e), x ∈ Q ∧ N.graph.Reaches (N.graph.target e) (N.leaf x) := by
    intro x hx
    obtain ⟨u, hr, hxu⟩ := hF.below e he x hx
    obtain ⟨hxQ, rfl⟩ := mem_lineages_taxaInj.1 hxu
    exact ⟨hxQ, hr⟩
  refine ⟨fun hn => ?_, fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · have hlt := mem_strictBelow.1 he
    have hempty : lineages (top e) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨hxQ, hr⟩ := hbelow x hx
      have hs : ¬ N.graph.Reaches l (N.graph.source e) := fun hs =>
        hn ⟨hs, ⟨x, hxQ, hr⟩⟩
      exact not_reaches_leaf_of_isStableAncestor hN hst hlt.1 hlt.2 hs hxQ hr
    constructor
    · refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨x, hx⟩ := hgb.1.1 A hA
      have : x ∈ lineages (top e) := hlin ▸ mem_lineages.2 ⟨A, hA, hx⟩
      rw [hempty] at this
      exact notMem_empty _ this
    · refine eq_empty_of_forall_notMem fun A hA => ?_
      obtain ⟨x, hx⟩ := hgt.1.1 A hA
      have : x ∈ lineages (top e) := mem_lineages.2 ⟨A, hA, hx⟩
      rw [hempty] at this
      exact notMem_empty _ this
  · exact (hbelow x (hlin ▸ mem_lineages.2 ⟨A, hA, hx⟩)).1
  · exact (hbelow x (mem_lineages.2 ⟨A, hA, hx⟩)).1

/-- **The law of the forest arriving at a stable ancestor** of the taxa `Q` is the same in the
network and in the induced subgraph below it, up to the number of values of the other arcs. -/
theorem sum_sum_strictBelow_eq (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (hNL : (N.belowNetwork l (Q : Set X) hl hleaf).IsPhylogenetic)
    (ψ : Finset (Finset X) → ℝ) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) u bot top) *
          ψ (arriving N (taxaInj N Q) top l) =
      (Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈
          strictBelow N l)ᶜ *
        (Fintype.card (Finset (Finset X)) : ℝ) ^ #(univ.filter fun e => N.graph.target e ∈
          strictBelow N l)ᶜ *
        ∑ b, ∑ t,
          (∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
              (N.belowNetwork l (Q : Set X) hl hleaf).root,
            vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
              (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t) *
            ψ (embedFamily (taxonEmb Q) (arriving (N.belowNetwork l (Q : Set X) hl hleaf)
              (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) t
              (N.belowNetwork l (Q : Set X) hl hleaf).root)) := by
  set A : Finset E := univ.filter fun e => N.graph.target e ∈ strictBelow N l with hA
  set C : ℝ := (Fintype.card (Finset (Finset X)) : ℝ) with hC
  let Θ : (E → Finset (Finset X)) → (E → Finset (Finset X)) → ℝ := fun bot top =>
    (∏ u ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) u bot top) *
      ψ (arriving N (taxaInj N Q) top l)
  have hmemA : ∀ {e : E}, N.graph.target e ∈ strictBelow N l → e ∈ A := fun he =>
    mem_filter.2 ⟨mem_univ _, he⟩
  have hdep : ∀ bot bot' top top' : E → Finset (Finset X), (∀ e ∈ A, bot e = bot' e) →
      (∀ e ∈ A, top e = top' e) → Θ bot top = Θ bot' top' := by
    intro bot bot' top top' hb ht
    simp only [Θ]
    congr 1
    · refine prod_congr rfl fun u hu => vertexWeight_congr rfl (fun e he => ?_) (fun e he => ?_)
        fun e he => ?_
      · exact hb e (hmemA (he ▸ hu))
      · exact ht e (hmemA (he ▸ hu))
      · exact ht e (hmemA (downClosed_strictBelow hN l e (he ▸ hu)))
    · rw [arriving_congr rfl fun e he => ht e (hmemA (target_mem_strictBelow hN (he ▸ .refl)))]
  have hbelowA : ∀ e : N.belowArcs l (Q : Set X), e.1 ∈ A := fun e =>
    hmemA (target_mem_strictBelow hN e.2.1)
  have hone : ∀ bot top : E → Finset (Finset X), Θ bot top =
      ∑ b : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
        ∑ t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
          if ∀ e ∈ A, bot e = liftArcs b e then
            (if ∀ e ∈ A, top e = liftArcs t e then Θ (liftArcs b) (liftArcs t) else 0) else 0 := by
    intro bot top
    by_cases hW : ∏ u ∈ strictBelow N l, vertexWeight N θ ρ (taxaInj N Q) u bot top = 0
    · have h0 : Θ bot top = 0 := by simp only [Θ, hW, zero_mul]
      rw [h0]
      refine (sum_eq_zero fun b _ => sum_eq_zero fun t _ => ?_).symm
      split_ifs with h1 h2
      · rw [← hdep bot _ top _ h1 h2, h0]
      · rfl
      · rfl
    · have hsup : ∀ e ∈ A, _ := fun e he =>
        support_strictBelow (θ := θ) (ρ := ρ) hN hst hW (mem_filter.1 he).2
      let b₀ : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)) :=
        fun e => downFamily (bot e.1)
      let t₀ : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)) :=
        fun e => downFamily (top e.1)
      have hb₀ : ∀ e ∈ A, bot e = liftArcs b₀ e := by
        intro e he
        by_cases hm : e ∈ N.belowArcs l (Q : Set X)
        · rw [liftArcs_of_mem b₀ ⟨e, hm⟩]
          exact (embedFamily_downFamily (hsup e he).2.1).symm
        · rw [liftArcs_of_notMem b₀ hm]
          exact ((hsup e he).1 hm).1
      have ht₀ : ∀ e ∈ A, top e = liftArcs t₀ e := by
        intro e he
        by_cases hm : e ∈ N.belowArcs l (Q : Set X)
        · rw [liftArcs_of_mem t₀ ⟨e, hm⟩]
          exact (embedFamily_downFamily (hsup e he).2.2).symm
        · rw [liftArcs_of_notMem t₀ hm]
          exact ((hsup e he).1 hm).2
      have hb₁ : ∀ b, (∀ e ∈ A, bot e = liftArcs b e) → b = b₀ := by
        intro b hb
        funext e
        have h1 := hb e.1 (hbelowA e)
        rw [liftArcs_of_mem b e] at h1
        simp only [b₀, h1, downFamily_embedFamily]
      have ht₁ : ∀ t, (∀ e ∈ A, top e = liftArcs t e) → t = t₀ := by
        intro t ht
        funext e
        have h1 := ht e.1 (hbelowA e)
        rw [liftArcs_of_mem t e] at h1
        simp only [t₀, h1, downFamily_embedFamily]
      rw [sum_eq_single b₀, sum_eq_single t₀]
      · rw [ite_eq_left hb₀, ite_eq_left ht₀]
        exact hdep _ _ _ _ hb₀ ht₀
      · intro t _ ht
        rw [ite_eq_left hb₀, ite_eq_right fun h => ht (ht₁ t h)]
      · exact fun h => absurd (mem_univ _) h
      · intro b _ hb
        exact sum_eq_zero fun t _ => ite_eq_right fun h => hb (hb₁ b h)
      · exact fun h => absurd (mem_univ _) h
  have hinner : ∀ (b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X))) (c : ℝ),
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (if ∀ e ∈ A, bot e = liftArcs b e then
          (if ∀ e ∈ A, top e = liftArcs t e then c else 0) else 0) = C ^ #Aᶜ * C ^ #Aᶜ * c := by
    intro b t c
    have h1 : ∀ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (if ∀ e ∈ A, bot e = liftArcs b e then
          (if ∀ e ∈ A, top e = liftArcs t e then c else 0) else 0) =
        if ∀ e ∈ A, bot e = liftArcs b e then c * C ^ #Aᶜ else 0 := by
      intro bot
      split_ifs
      · exact sum_ite_forall_eq A (liftArcs t) c
      · simp
    simp only [h1]
    rw [sum_ite_forall_eq A (liftArcs b) (c * C ^ #Aᶜ)]
    ring
  have hΛ : ∀ b t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
      Θ (liftArcs b) (liftArcs t) =
        (∏ u ∈ strictBelow (N.belowNetwork l (Q : Set X) hl hleaf)
            (N.belowNetwork l (Q : Set X) hl hleaf).root,
          vertexWeight (N.belowNetwork l (Q : Set X) hl hleaf) (belowMetric l (Q : Set X) θ) ρ
            (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) u b t) *
          ψ (embedFamily (taxonEmb Q) (arriving (N.belowNetwork l (Q : Set X) hl hleaf)
            (taxaInj (N.belowNetwork l (Q : Set X) hl hleaf) univ) t
            (N.belowNetwork l (Q : Set X) hl hleaf).root)) := by
    intro b t
    simp only [Θ]
    rw [prod_strictBelow_liftArcs hN hst hNL]
    congr 2
    exact arriving_below t (N.belowNetwork l (Q : Set X) hl hleaf).root
  calc ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X), Θ bot top
      = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          ∑ b : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
          ∑ t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
          if ∀ e ∈ A, bot e = liftArcs b e then
            (if ∀ e ∈ A, top e = liftArcs t e then Θ (liftArcs b) (liftArcs t) else 0) else 0 :=
        sum_congr rfl fun bot _ => sum_congr rfl fun top _ => hone bot top
    _ = ∑ b : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
          ∑ t : N.belowArcs l (Q : Set X) → Finset (Finset (Q : Set X)),
          ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          if ∀ e ∈ A, bot e = liftArcs b e then
            (if ∀ e ∈ A, top e = liftArcs t e then Θ (liftArcs b) (liftArcs t) else 0) else 0 := by
        refine (sum_congr rfl fun bot _ => sum_comm).trans ?_
        refine sum_comm.trans ?_
        refine sum_congr rfl fun b _ => ?_
        refine (sum_congr rfl fun bot _ => sum_comm).trans ?_
        exact sum_comm
    _ = _ := by
        simp only [hinner, hΛ, mul_sum]


omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] [Fintype (N.belowArcs l (Q : Set X))]
  [Fintype (Q : Set X)] [DecidableEq (Q : Set X)] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The arcs entering a vertex of the induced subgraph, other than `l`, are as many as in the
network. -/
theorem indegree_belowNetwork (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (u : N.belowVertices l (Q : Set X)) (hu : u.1 ≠ l) :
    (N.belowNetwork l (Q : Set X) hl hleaf).graph.indegree u = N.graph.indegree u.1 :=
  Set.ncard_congr' ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩,
    fun e => ⟨⟨e.1, mem_belowArcs_of_target_eq hN hst u hu e.2⟩, Subtype.ext e.2⟩,
    fun _ => rfl, fun _ => rfl⟩

omit [Fintype V] [Fintype (N.belowVertices l (Q : Set X))] [Fintype (Q : Set X)]
  [DecidableEq (Q : Set X)] [Fintype X] [DecidableEq X] in
/-- **The parameters of the induced subgraph are valid.** -/
theorem belowMetric_isMetric (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor (Q : Set X) l)
    (hNL : (N.belowNetwork l (Q : Set X) hl hleaf).IsPhylogenetic) (hθ : N.IsMetric θ) :
    (N.belowNetwork l (Q : Set X) hl hleaf).IsMetric (belowMetric l (Q : Set X) θ) := by
  have htgt : ∀ e : N.belowArcs l (Q : Set X),
      ((N.belowNetwork l (Q : Set X) hl hleaf).graph.target e).1 ≠ l := fun e h =>
    target_ne_root hNL e (Subtype.ext h)
  have hdeg : ∀ e : N.belowArcs l (Q : Set X),
      (N.belowNetwork l (Q : Set X) hl hleaf).graph.indegree
        ((N.belowNetwork l (Q : Set X) hl hleaf).graph.target e) =
        N.graph.indegree (N.graph.target e.1) := fun e =>
    indegree_belowNetwork hN hst _ (htgt e)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hθ
  refine ⟨fun e he => h1 e.1 ?_, fun e he => h2 e.1 ?_, fun e he => h3 e.1 ?_,
    fun e he => h4 e.1 ?_, fun v hv => ?_⟩
  · exact (hdeg e).symm.trans he
  · exact le_of_le_of_eq he (hdeg e)
  · exact (hdeg e).symm.trans he
  · exact le_of_le_of_eq he (hdeg e)
  · have hvl : v.1 ≠ l := by
      intro h
      have hr : v = (N.belowNetwork l (Q : Set X) hl hleaf).root := Subtype.ext h
      rw [hr, hNL.root_indegree] at hv
      omega
    rw [indegree_belowNetwork hN hst v hvl] at hv
    refine Eq.trans (@sum_ite_of_injective _ _ _ _
      (fun e => (N.belowNetwork l (Q : Set X) hl hleaf).graph.target e = v)
      (fun e => N.graph.target e = v.1) (fun _ => Classical.propDecidable _)
      (fun _ => Classical.propDecidable _) Subtype.val θ.inheritance Subtype.val_injective
      (fun e => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩) fun e he => ?_)
      (h5 v.1 hv)
    exact ⟨⟨e, mem_belowArcs_of_target_eq hN hst v hvl he⟩, rfl⟩

end Below

end NMSC

end Phylogenetics
