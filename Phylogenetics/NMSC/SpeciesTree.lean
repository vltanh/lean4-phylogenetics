module

public import Phylogenetics.MSC.Basic
public import Phylogenetics.NMSC.InducedSuppress
public import Phylogenetics.Network.OfHierarchy

/-!
# The multispecies coalescent is the network multispecies coalescent on a tree

The multispecies coalescent `forestDist` is defined by recursion over the clusters of a hierarchy: the forests leaving the
populations of the children of a cluster are independent. The network multispecies coalescent `geneTreeDist` is defined as a
sum over all histories of a network at once. On the network of a hierarchy, where no vertex is a reticulation, they agree
for every inheritance correlation.

The proof writes the recursion as a sum over the forests at the tops of all arcs below a cluster, as functions on the arcs that
are `∅` off those arcs (`FunctionBox.box`), by induction over the clusters: the arcs below a cluster are those of its children, and the
arcs into its children.

Lineages may be sampled several times from a taxon: `sampleNetwork H hH s` has the lineages `L` as taxa, with `l` at the
leaf of `s l`.

## Main results

* `FunctionBox.prod_sum_box`, `FunctionBox.sum_box_overlay`: sums over functions on a set of coordinates that is a
  disjoint union.
* `forestDist_eq_sum_box`: the recursion, as a sum over the forests at the tops of the arcs below a cluster.
* `forestDist_univ_eq_geneTreeDist`, `SpeciesTree.rootedDist_eq_geneTreeDist`: the two coalescents agree.
* `SpeciesTree.nmscCF_eq`: the concordance factors of the network of a species tree.
* `SpeciesTree.isMetric_hierarchyMetric`: its lengths are valid parameters of the network.
-/

@[expose] public noncomputable section

open Finset

namespace Phylogenetics

/-! ### Sums over functions on a set of coordinates -/

namespace FunctionBox

section Box

variable {E S ι : Type*} [Fintype E] [DecidableEq E] [Fintype S] [DecidableEq S]

/-- The functions on `E` that take the value `d` off `U`. -/
def box (d : S) (U : Finset E) : Finset (E → S) :=
  univ.filter fun t => ∀ e, e ∉ U → t e = d

theorem mem_box {d : S} {U : Finset E} {t : E → S} : t ∈ box d U ↔ ∀ e, e ∉ U → t e = d := by
  simp [box]

theorem box_univ (d : S) : box d (univ : Finset E) = univ := by
  ext t
  simp [mem_box]

/-- A product of sums over functions on disjoint sets of coordinates is the sum over functions on their union. -/
theorem prod_sum_box [Fintype ι] [DecidableEq ι] (d : S) (U : ι → Finset E)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (g : ι → (E → S) → ℝ)
    (hg : ∀ i t t', (∀ e ∈ U i, t e = t' e) → g i t = g i t') :
    ∏ i, ∑ t ∈ box d (U i), g i t = ∑ t ∈ box d (univ.biUnion U), ∏ i, g i t := by
  classical
  rw [Finset.prod_univ_sum]
  have hmem : ∀ {e i j}, e ∈ U i → e ∈ U j → i = j := by
    intro e i j hi hj
    by_contra hne
    exact disjoint_left.1 (hU i j hne) hi hj
  let merge : (ι → E → S) → E → S := fun x e => if h : ∃ i, e ∈ U i then x h.choose e else d
  have hmerge : ∀ x i e, e ∈ U i → merge x e = x i e := by
    intro x i e he
    have h : ∃ i, e ∈ U i := ⟨i, he⟩
    simp only [merge, dite_eq_left h]
    rw [hmem h.choose_spec he]
  refine Finset.sum_nbij' merge (fun t i e => if e ∈ U i then t e else d) ?_ ?_ ?_ ?_ ?_
  · intro x _
    refine mem_box.2 fun e he => ?_
    have : ¬ ∃ i, e ∈ U i := fun ⟨i, hi⟩ => he (mem_biUnion.2 ⟨i, mem_univ i, hi⟩)
    simp only [merge, dite_eq_right this]
  · intro t _
    refine Fintype.mem_piFinset.2 fun i => mem_box.2 fun e he => ?_
    simp only [ite_eq_right he]
  · intro x hx
    funext i e
    by_cases he : e ∈ U i
    · simp only [ite_eq_left he]
      exact hmerge x i e he
    · simp only [ite_eq_right he]
      exact (mem_box.1 (Fintype.mem_piFinset.1 hx i) e he).symm
  · intro t ht
    funext e
    by_cases h : ∃ i, e ∈ U i
    · simp only [merge, dite_eq_left h, ite_eq_left h.choose_spec]
    · simp only [merge, dite_eq_right h]
      refine (mem_box.1 ht e fun he => ?_).symm
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 he
      exact h ⟨i, hi⟩
  · intro x _
    exact prod_congr rfl fun i _ => hg i _ _ fun e he => (hmerge x i e he).symm

/-- The function `f` on the coordinates `k i`, and `t` on the others. -/
def overlay (k : ι → E) (f : ι → S) (t : E → S) (e : E) : S :=
  open Classical in if h : ∃ i, k i = e then f h.choose else t e

omit [Fintype E] [DecidableEq E] [Fintype S] [DecidableEq S] in
theorem overlay_apply {k : ι → E} (hk : Function.Injective k) (f : ι → S) (t : E → S) (i : ι) :
    overlay k f t (k i) = f i := by
  have h : ∃ j, k j = k i := ⟨i, rfl⟩
  simp only [overlay, dite_eq_left h]
  rw [hk h.choose_spec]

omit [Fintype E] [DecidableEq E] [Fintype S] [DecidableEq S] in
theorem overlay_of_ne {k : ι → E} (f : ι → S) (t : E → S) {e : E} (h : ∀ i, k i ≠ e) :
    overlay k f t e = t e := by
  have h' : ¬ ∃ i, k i = e := fun ⟨i, hi⟩ => h i hi
  simp only [overlay, dite_eq_right h']

/-- A sum over functions on some coordinates `k i` and on `U` is a sum over functions on each. -/
theorem sum_box_overlay [Fintype ι] [DecidableEq ι] (d : S) {k : ι → E} (hk : Function.Injective k)
    (U : Finset E) (hU : ∀ i, k i ∉ U) (F : (E → S) → ℝ) :
    ∑ t ∈ box d (univ.image k ∪ U), F t = ∑ f : ι → S, ∑ t ∈ box d U, F (overlay k f t) := by
  rw [← Finset.sum_product' (univ : Finset (ι → S)) (box d U) (fun f t => F (overlay k f t))]
  have hleft : ∀ t ∈ box d (univ.image k ∪ U),
      overlay k (fun i => t (k i)) (fun e => if e ∈ U then t e else d) = t := by
    intro t ht
    funext e
    by_cases h : ∃ i, k i = e
    · obtain ⟨i, rfl⟩ := h
      exact overlay_apply hk _ _ i
    · have h' : ∀ i, k i ≠ e := fun i hi => h ⟨i, hi⟩
      rw [overlay_of_ne _ _ h']
      by_cases he : e ∈ U
      · simp only [ite_eq_left he]
      · simp only [ite_eq_right he]
        refine (mem_box.1 ht e fun hm => ?_).symm
        rcases mem_union.1 hm with hm | hm
        · obtain ⟨i, -, hi⟩ := mem_image.1 hm
          exact h ⟨i, hi⟩
        · exact he hm
  refine Finset.sum_nbij' (fun t => (fun i => t (k i), fun e => if e ∈ U then t e else d))
    (fun p => overlay k p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro t _
    refine mem_product.2 ⟨mem_univ _, mem_box.2 fun e he => ?_⟩
    simp only [ite_eq_right he]
  · rintro ⟨f, t⟩ hp
    refine mem_box.2 fun e he => ?_
    have h' : ∀ i, k i ≠ e := fun i hi =>
      he (mem_union.2 (Or.inl (mem_image.2 ⟨i, mem_univ i, hi⟩)))
    change overlay k f t e = d
    rw [overlay_of_ne _ _ h']
    exact mem_box.1 (mem_product.1 hp).2 e fun hm => he (mem_union.2 (Or.inr hm))
  · exact hleft
  · rintro ⟨f, t⟩ hp
    refine Prod.ext ?_ ?_
    · funext i
      exact overlay_apply hk _ _ i
    · funext e
      by_cases he : e ∈ U
      · have h' : ∀ i, k i ≠ e := fun i hi => hU i (hi ▸ he)
        change (if e ∈ U then overlay k f t e else d) = t e
        rw [ite_eq_left he, overlay_of_ne _ _ h']
      · change (if e ∈ U then overlay k f t e else d) = t e
        rw [ite_eq_right he]
        exact (mem_box.1 (mem_product.1 hp).2 e he).symm
  · intro t ht
    exact congrArg F (hleft t ht).symm

end Box

end FunctionBox

open FunctionBox

/-! ### The network of a hierarchy, with sampled lineages -/

section Network

variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]
  {H : Finset (Finset X)}

/-- The network of a hierarchy, with the lineages `L` as taxa, the lineage `l` at the leaf of `s l`. -/
def sampleNetwork (H : Finset (Finset X)) (hH : IsHierarchy H) (s : L → X) :
    RootedNetwork (HierarchyVertex H) (HierarchyArc H) L where
  graph := (hierarchyNetwork H hH).graph
  root := (hierarchyNetwork H hH).root
  leaf l := (hierarchyNetwork H hH).leaf (s l)

/-- The parameters of the network of a hierarchy, for lengths on the clusters. -/
def hierarchyMetric (H : Finset (Finset X)) (len : Finset X → ℝ) :
    RootedNetwork.MetricData (HierarchyArc H) :=
  ⟨fun e => len e.val.val, fun _ => 1⟩

open scoped Classical in
/-- The singleton lineages at a vertex: the first part of `arrivingForest`. -/
def leafForest {V E Y : Type*} [Fintype Y] [DecidableEq Y] (N : RootedNetwork V E Y) (v : V) : Finset (Finset Y) :=
  (univ.filter fun x => N.leaf x = v).image fun x => ({x} : Finset Y)

theorem mem_leafForest {V E Y : Type*} [Fintype Y] [DecidableEq Y] {N : RootedNetwork V E Y} {v : V}
    {C : Finset Y} : C ∈ leafForest N v ↔ ∃ x, N.leaf x = v ∧ {x} = C := by
  simp [leafForest]

/-- The arcs below a cluster. -/
def arcsUnder (H : Finset (Finset X)) (A : Finset X) : Finset (HierarchyArc H) :=
  univ.filter fun e => e.val.val ⊂ A

theorem mem_arcsUnder {A : Finset X} {e : HierarchyArc H} : e ∈ arcsUnder H A ↔ e.val.val ⊂ A := by
  simp [arcsUnder]

theorem arcsUnder_univ : arcsUnder H univ = univ := by
  ext e
  simp only [mem_arcsUnder, mem_univ, iff_true]
  exact ssubset_univ_iff.2 e.2

/-- The arc into a child of `A`. -/
def childArc {A : Finset X} (B : childClusters H A) : HierarchyArc H :=
  ⟨⟨B.1, (mem_childClusters.1 B.2).1⟩, fun e =>
    not_subset_of_ssubset (mem_childClusters.1 B.2).2.1 (e ▸ subset_univ A)⟩

theorem childArc_injective {A : Finset X} : Function.Injective (childArc (H := H) (A := A)) := by
  intro B B' h
  exact Subtype.ext (congrArg (fun e : HierarchyArc H => e.val.val) h)

theorem not_ssubset_of_mem_childClusters (hH : IsHierarchy H) {A B C : Finset X}
    (hB : B ∈ childClusters H A) (hC : C ∈ childClusters H A) : ¬ B ⊂ C := by
  intro hlt
  by_cases hBC : B = C
  · exact (ssubset_irrefl _) (hBC ▸ hlt)
  · obtain ⟨x, hx⟩ := hH.2.2.1 B (mem_childClusters.1 hB).1
    exact disjoint_left.1 (hH.disjoint_of_mem_childClusters hB hC hBC) hx (hlt.subset hx)

/-- The arcs below a cluster are the arcs into its children, and the arcs below those. -/
theorem arcsUnder_eq (hH : IsHierarchy H) (A : Finset X) :
    arcsUnder H A = univ.image (childArc (H := H) (A := A)) ∪
      univ.biUnion fun B : childClusters H A => arcsUnder H B := by
  ext e
  simp only [mem_union, mem_image, mem_univ, true_and, mem_biUnion, mem_arcsUnder]
  constructor
  · intro he
    obtain ⟨C, hC, hsub⟩ := hH.exists_mem_childClusters_superset e.val.property he
    by_cases heC : e.val.val = C
    · exact Or.inl ⟨⟨C, hC⟩, Subtype.ext (Subtype.ext heC.symm)⟩
    · exact Or.inr ⟨⟨C, hC⟩, hsub.ssubset_of_ne heC⟩
  · rintro (⟨B, rfl⟩ | ⟨B, hB⟩)
    · exact (mem_childClusters.1 B.2).2.1
    · exact hB.trans (mem_childClusters.1 B.2).2.1

theorem disjoint_arcsUnder (hH : IsHierarchy H) {A : Finset X} (B B' : childClusters H A)
    (hne : B ≠ B') : Disjoint (arcsUnder H B) (arcsUnder H B') := by
  refine disjoint_left.2 fun e he he' => ?_
  obtain ⟨x, hx⟩ := hH.2.2.1 _ e.val.property
  exact disjoint_left.1 (hH.disjoint_of_mem_childClusters B.2 B'.2 fun h => hne (Subtype.ext h))
    ((mem_arcsUnder.1 he).subset hx) ((mem_arcsUnder.1 he').subset hx)

theorem childArc_notMem_arcsUnder (hH : IsHierarchy H) {A : Finset X} (B : childClusters H A) :
    childArc B ∉ univ.biUnion fun B : childClusters H A => arcsUnder H B := by
  intro h
  obtain ⟨B', -, hB'⟩ := mem_biUnion.1 h
  exact not_ssubset_of_mem_childClusters hH B.2 B'.2 (mem_arcsUnder.1 hB')

variable (hH : IsHierarchy H) (s : L → X)

/-- The forests arriving at a vertex depend on the forests at the tops of the arcs below it. -/
theorem arrivingForest_congr {t t' : HierarchyArc H → Finset (Finset L)} (v : HierarchyVertex H)
    (h : ∀ e ∈ arcsUnder H v.val, t e = t' e) :
    arrivingForest (sampleNetwork H hH s) t v = arrivingForest (sampleNetwork H hH s) t' v := by
  unfold arrivingForest
  refine congrArg (_ ∪ ·) (biUnion_congr rfl fun e he => h e (mem_arcsUnder.2 ?_))
  simp only [mem_filter, mem_univ, true_and] at he
  have hsrc : (⟨parentCluster H e.val.val, hH.parentCluster_mem e.val.property e.2⟩ :
      HierarchyVertex H) = v := he
  rw [← hsrc]
  exact hH.ssubset_parentCluster e.val.property e.2

/-- What arrives at a cluster: the lineages sampled there, and the forests at the tops of the arcs from its children. -/
theorem arrivingForest_eq_sup (t : HierarchyArc H → Finset (Finset L)) {A : Finset X} (hA : A ∈ H) :
    arrivingForest (sampleNetwork H hH s) t ⟨A, hA⟩ =
      leafForest (sampleNetwork H hH s) ⟨A, hA⟩ ∪ univ.sup fun B : childClusters H A => t (childArc B) := by
  refine congrArg (leafForest (sampleNetwork H hH s) ⟨A, hA⟩ ∪ ·) ?_
  ext C
  rw [mem_biUnion, Finset.mem_sup]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hC⟩
    have hsrc : parentCluster H e.val.val = A := congrArg Subtype.val he
    have hmem : e.val.val ∈ childClusters H A :=
      hsrc ▸ hH.mem_childClusters_parentCluster e.val.property e.2
    exact ⟨⟨_, hmem⟩, hC⟩
  · rintro ⟨B, hC⟩
    refine ⟨childArc B, Subtype.ext ?_, hC⟩
    exact hH.parentCluster_eq_of_mem_childClusters hA B.2

variable {s}

/-- The forests of the children contain the lineages sampled below `A`, so that it does not matter what is added to them
above the leaves. -/
theorem sup_union_sampledForest (len : Finset X → ℝ) {A : Finset X} (hA : A ∈ H)
    (f : childClusters H A → Finset (Finset L))
    (hf : ∏ B : childClusters H A, forestDist H len s B (f B) ≠ 0) :
    (univ.sup f) ∪ sampledForest s A = leafForest (sampleNetwork H hH s) ⟨A, hA⟩ ∪ univ.sup f := by
  have hne : A.Nonempty := hH.2.2.1 A hA
  by_cases h2 : 2 ≤ #A
  · have hleaf : leafForest (sampleNetwork H hH s) ⟨A, hA⟩ = ∅ := by
      refine eq_empty_of_forall_notMem fun C hC => ?_
      obtain ⟨l, hl, -⟩ := mem_leafForest.1 hC
      have : ({s l} : Finset X) = A := congrArg Subtype.val hl
      rw [← this, card_singleton] at h2
      omega
    rw [hleaf, empty_union]
    refine union_eq_left.2 fun C hC => ?_
    obtain ⟨l, hl, rfl⟩ := mem_image.1 hC
    obtain ⟨B, hB, hlB⟩ := hH.exists_mem_childClusters h2 (mem_filter.1 hl).2
    have hdist := prod_ne_zero_iff.1 hf ⟨B, hB⟩ (mem_univ _)
    have hsup := (forestDist_support hH len s (mem_childClusters.1 hB).1 hdist).2.1
    exact Finset.mem_sup.2 ⟨⟨B, hB⟩, mem_univ _, hsup (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hlB⟩))⟩
  · obtain ⟨x, rfl⟩ : ∃ x, A = {x} := card_eq_one.1 (by
      have := card_pos.2 hne
      omega)
    rw [union_comm]
    refine congrArg (· ∪ _) ?_
    ext C
    rw [mem_leafForest]
    unfold sampledForest
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, Subtype.ext (congrArg (fun y => ({y} : Finset X)) hl), rfl⟩
    · rintro ⟨l, hl, rfl⟩
      have : ({s l} : Finset X) = {x} := congrArg Subtype.val hl
      exact ⟨l, singleton_injective this, rfl⟩

variable (s)

/-- **The recursion as a sum**: the multispecies coalescent above a cluster is the sum over the forests at the tops of the
arcs below it. -/
theorem forestDist_eq_sum_box (len : Finset X → ℝ) (A : Finset X) (hA : A ∈ H) (G : Finset (Finset L)) :
    forestDist H len s A G = ∑ t ∈ box ∅ (arcsUnder H A),
      (∏ e ∈ arcsUnder H A, kingmanTransition (len e.val.val)
        (arrivingForest (sampleNetwork H hH s) t e.val) (t e)) *
        populationKernel len A (arrivingForest (sampleNetwork H hH s) t ⟨A, hA⟩) G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  set N := sampleNetwork H hH s with hNdef
  have hswap : ∀ f : childClusters H A → Finset (Finset L),
      (∏ B : childClusters H A, forestDist H len s B (f B)) *
          populationKernel len A (univ.sup f ∪ sampledForest s A) G =
        (∏ B : childClusters H A, forestDist H len s B (f B)) *
          populationKernel len A (leafForest N ⟨A, hA⟩ ∪ univ.sup f) G := by
    intro f
    by_cases hf : ∏ B : childClusters H A, forestDist H len s B (f B) = 0
    · rw [hf, zero_mul, zero_mul]
    · rw [sup_union_sampledForest hH len hA f hf]
  rw [forestDist, sum_congr rfl fun f _ => hswap f, arcsUnder_eq hH A,
    sum_box_overlay ∅ childArc_injective _ (childArc_notMem_arcsUnder hH)]
  refine sum_congr rfl fun f _ => ?_
  have hchild : ∀ B : childClusters H A, forestDist H len s B (f B) =
      ∑ t ∈ box ∅ (arcsUnder H B),
        (∏ e ∈ arcsUnder H B, kingmanTransition (len e.val.val) (arrivingForest N t e.val) (t e)) *
          kingmanTransition (len B) (arrivingForest N t (childArc B).val) (f B) := by
    intro B
    have hBA := mem_childClusters.1 B.2
    have hBu : B.1 ≠ univ := (childArc B).2
    rw [ih B.1 hBA.2.1 hBA.1 (f B)]
    refine sum_congr rfl fun t _ => ?_
    unfold populationKernel
    rw [ite_eq_right hBu]
    rfl
  rw [prod_congr rfl fun B _ => hchild B,
    prod_sum_box ∅ (fun B : childClusters H A => arcsUnder H B) (fun B B' h => disjoint_arcsUnder hH B B' h)
      (fun B t => (∏ e ∈ arcsUnder H B, kingmanTransition (len e.val.val) (arrivingForest N t e.val) (t e)) *
        kingmanTransition (len B) (arrivingForest N t (childArc B).val) (f B)) ?_, sum_mul]
  · refine sum_congr rfl fun t _ => ?_
    have hov : ∀ e ∈ univ.biUnion fun B : childClusters H A => arcsUnder H B,
        overlay childArc f t e = t e := fun e he =>
      overlay_of_ne f t fun B hB => childArc_notMem_arcsUnder hH B (hB ▸ he)
    have harr : ∀ (B : childClusters H A) (v : HierarchyVertex H), v.val ⊆ B.1 →
        arrivingForest N (overlay childArc f t) v = arrivingForest N t v := by
      intro B v hv
      refine arrivingForest_congr hH s v fun e he => hov e (mem_biUnion.2 ⟨B, mem_univ _, ?_⟩)
      exact mem_arcsUnder.2 ((mem_arcsUnder.1 he).trans_subset hv)
    have hdisj : Disjoint (univ.image (childArc (H := H) (A := A)))
        (univ.biUnion fun B : childClusters H A => arcsUnder H B) := by
      refine disjoint_left.2 fun e he he' => ?_
      obtain ⟨B, -, rfl⟩ := mem_image.1 he
      exact childArc_notMem_arcsUnder hH B he'
    have hk : arrivingForest N (overlay childArc f t) ⟨A, hA⟩ = leafForest N ⟨A, hA⟩ ∪ univ.sup f := by
      rw [hNdef, arrivingForest_eq_sup hH s _ hA]
      simp only [overlay_apply childArc_injective]
    rw [hk, prod_union hdisj, prod_image fun _ _ _ _ h => childArc_injective h, prod_biUnion]
    · congr 1
      rw [prod_mul_distrib, mul_comm]
      congr 1
      · refine prod_congr rfl fun B _ => ?_
        rw [overlay_apply childArc_injective, harr B _ subset_rfl]
        rfl
      · refine prod_congr rfl fun B _ => prod_congr rfl fun e he => ?_
        rw [hov e (mem_biUnion.2 ⟨B, mem_univ _, he⟩), harr B _ (mem_arcsUnder.1 he).subset]
    · intro B _ B' _ h
      exact disjoint_arcsUnder hH B B' h
  · intro B t t' h
    congr 1
    · refine prod_congr rfl fun e he => ?_
      rw [h e he, arrivingForest_congr hH s e.val fun e' he' =>
        h e' (mem_arcsUnder.2 ((mem_arcsUnder.1 he').trans (mem_arcsUnder.1 he)))]
    · rw [arrivingForest_congr hH s (childArc B).val fun e' he' => h e' he']

end Network

/-! ### The two coalescents -/

section Coalescent

variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L] {H : Finset (Finset X)}

theorem prod_erase_root_eq {M : Type*} [CommMonoid M] (inst : DecidableEq (HierarchyVertex H))
    {r : HierarchyVertex H} (hr : r.val = univ) (f : HierarchyVertex H → M) :
    ∏ v ∈ univ.erase r, f v = ∏ e : HierarchyArc H, f e.val := by
  refine Finset.prod_subtype _ (fun v => ?_) f
  simp only [mem_erase, mem_univ, and_true, ne_eq]
  rw [← hr]
  exact not_congr Subtype.ext_iff

open scoped Classical in
/-- On the network of a hierarchy, the sum of the weights of the histories with given forests at the tops of the arcs: the
bottoms are forced. -/
theorem sum_historyWeight_sampleNetwork (hH : IsHierarchy H) (s : L → X) (len : Finset X → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (inst : Fintype (HierarchyArc H → Finset (Finset L))) (top : HierarchyArc H → Finset (Finset L)) :
    @Finset.sum _ ℝ _ (@univ _ inst)
        (fun bot => historyWeight (sampleNetwork H hH s) (hierarchyMetric H len) ρ bot top) =
      ∏ e, kingmanTransition (len e.val.val) (arrivingForest (sampleNetwork H hH s) top e.val) (top e) := by
  set N := sampleNetwork H hH s with hNdef
  have hAF : ∀ (e : HierarchyArc H) (bot : HierarchyArc H → Finset (Finset L)),
      allocationFactor N (hierarchyMetric H len) ρ (arrivingForest N top e.val) e.val bot =
        if bot e = arrivingForest N top e.val then 1 else 0 := fun e bot =>
    NMSC.allocationFactor_of_unique_arc hρ (e := e) rfl (fun g hg => Subtype.ext hg) rfl _ bot
  have hw : ∀ bot : HierarchyArc H → Finset (Finset L),
      historyWeight N (hierarchyMetric H len) ρ bot top =
        if bot = fun e => arrivingForest N top e.val then
          ∏ e, kingmanTransition (len e.val.val) (arrivingForest N top e.val) (top e) else 0 := by
    intro bot
    unfold historyWeight
    rw [prod_erase_root_eq _ (r := N.root) rfl]
    simp only [hAF]
    split_ifs with hbot
    · subst hbot
      simp only [ite_true, prod_const_one, one_mul]
      rfl
    · obtain ⟨e, he⟩ := Function.ne_iff.1 hbot
      rw [prod_eq_zero (mem_univ e) (ite_eq_right he), zero_mul]
  simp only [hw]
  rw [Finset.sum_ite_eq' univ, ite_eq_left (mem_univ _)]

open scoped Classical in
/-- **The multispecies coalescent is the network multispecies coalescent on the network of the hierarchy**, for every
inheritance correlation `ρ ≥ 0`, which plays no role where there is no reticulation. -/
theorem forestDist_univ_eq_geneTreeDist (hH : IsHierarchy H) (s : L → X) (len : Finset X → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (G : Finset (Finset L)) :
    forestDist H len s univ G =
      geneTreeDist (sampleNetwork H hH s) (hierarchyMetric H len) ρ G := by
  rw [forestDist_eq_sum_box hH s len univ hH.1 G, arcsUnder_univ, box_univ]
  unfold geneTreeDist
  rw [sum_comm]
  simp only [← sum_mul]
  have huniv : ∀ i₁ i₂ : Fintype (HierarchyArc H → Finset (Finset L)), @univ _ i₁ = @univ _ i₂ :=
    fun i₁ i₂ => by rw [Subsingleton.elim i₁ i₂]
  refine sum_congr (huniv _ _) fun top _ => ?_
  rw [sum_historyWeight_sampleNetwork hH s len hρ _ top]
  unfold populationKernel
  rw [ite_eq_left rfl]
  rfl

end Coalescent

namespace SpeciesTree

variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]

open scoped Classical in
/-- **The multispecies coalescent on a species tree, with sampled lineages, is the network multispecies coalescent.** -/
theorem rootedDist_eq_geneTreeDist_sample (σ : SpeciesTree X) (s : L → X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (G : Finset (Finset L)) :
    σ.rootedDist s G =
      geneTreeDist (sampleNetwork σ.clusters σ.isHierarchy s) (hierarchyMetric σ.clusters σ.length) ρ G :=
  forestDist_univ_eq_geneTreeDist σ.isHierarchy s σ.length hρ G

open scoped Classical in
/-- **The multispecies coalescent on a species tree is the network multispecies coalescent on its network.** -/
theorem rootedDist_eq_geneTreeDist (σ : SpeciesTree X) {ρ : ℝ} (hρ : 0 ≤ ρ) (G : Finset (Finset X)) :
    σ.rootedDist id G =
      geneTreeDist (hierarchyNetwork σ.clusters σ.isHierarchy) (hierarchyMetric σ.clusters σ.length) ρ G :=
  σ.rootedDist_eq_geneTreeDist_sample id hρ G

open scoped Classical in
/-- The concordance factors of the network of a species tree. -/
theorem nmscCF_eq (σ : SpeciesTree X) {ρ : ℝ} (hρ : 0 ≤ ρ) (s : QuartetTree X) :
    nmscCF (hierarchyNetwork σ.clusters σ.isHierarchy) (hierarchyMetric σ.clusters σ.length) ρ s =
      ∑ G : Finset (Finset X), if Displays (unroot G) s then σ.rootedDist id G else 0 := by
  unfold nmscCF
  exact sum_congr rfl fun G _ => by rw [σ.rootedDist_eq_geneTreeDist hρ G]

/-- The lengths of a species tree are valid parameters of its network, so that the theorems on `geneTreeDist` apply to
`SpeciesTree.rootedDist` through `SpeciesTree.rootedDist_eq_geneTreeDist`. -/
theorem isMetric_hierarchyMetric (σ : SpeciesTree X) :
    (hierarchyNetwork σ.clusters σ.isHierarchy).IsMetric (hierarchyMetric σ.clusters σ.length) := by
  have hle : ∀ v, (hierarchyNetwork σ.clusters σ.isHierarchy).graph.indegree v ≤ 1 := fun v => by
    by_cases hv : v.val = univ
    · have hr : v = (hierarchyNetwork σ.clusters σ.isHierarchy).root := Subtype.ext hv
      rw [hr, hierarchyNetwork_indegree_root]
      exact zero_le_one
    · exact (hierarchyNetwork_indegree_nonroot _ _ v hv).le
  have hnot : ∀ v, ¬ 2 ≤ (hierarchyNetwork σ.clusters σ.isHierarchy).graph.indegree v := fun v h => by
    have := hle v
    omega
  exact ⟨fun e _ => σ.length_pos _ e.val.2 e.2, fun e h => absurd h (hnot _), fun _ _ => rfl,
    fun e h => absurd h (hnot _), fun v h => absurd h (hnot v)⟩

end SpeciesTree

end Phylogenetics
