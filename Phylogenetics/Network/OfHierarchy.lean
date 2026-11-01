module

public import Phylogenetics.Hierarchy.Basic
public import Phylogenetics.Network.Basic
public import Phylogenetics.Graph.CutUniqueness

/-!
# The rooted graph of a hierarchy

The vertices are the clusters. Every non-root cluster labels one arc from its parent to itself. This
construction supplies an actual graph for the split families of `Phylogenetics.Tree`.

## Main results

* `hierarchyNetwork`: the rooted network of a hierarchy; `hierarchyNetwork_isPhylogenetic`: with at least
  two taxa, it obeys the laws of a network.
* `hierarchyNetwork_isBridge`: every arc is a bridge.
* `hierarchyNetwork_reaches_iff`, `hierarchyNetwork_reaches_leaf_iff`: descendants are subclusters.
* `hierarchyNetwork_hasCutSplit_iff`: its labelled cuts are the sides of `unroot H`.

There is no bijection between arcs and unordered splits: the two arcs at a binary root can carry the same
split.
-/

@[expose] public section

namespace Phylogenetics

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (H : Finset (Finset X)) (hH : IsHierarchy H)

/-- Actual cluster vertices. -/
abbrev HierarchyVertex := {A : Finset X // A ∈ H}

/-- One incoming arc for each non-root cluster. -/
abbrev HierarchyArc := {A : HierarchyVertex H // A.val ≠ Finset.univ}

/-- The graph realization of a hierarchy, with arcs oriented away from its root. -/
def hierarchyNetwork : RootedNetwork (HierarchyVertex H) (HierarchyArc H) X where
  graph := {
    source := fun A => ⟨parentCluster H A.val.val,
      hH.parentCluster_mem A.val.property A.property⟩
    target := fun A => A.val }
  root := ⟨univ, hH.1⟩
  leaf x := ⟨{x}, hH.2.1 x⟩

/-- Cluster cardinality strictly decreases along every realized arc. -/
theorem hierarchy_arc_card_lt (e : HierarchyArc H) :
    ((hierarchyNetwork H hH).graph.target e).val.card <
      ((hierarchyNetwork H hH).graph.source e).val.card :=
  card_lt_card (hH.ssubset_parentCluster e.val.property e.property)

/-- The realized graph has no directed cycle. -/
theorem hierarchyNetwork_acyclic : (hierarchyNetwork H hH).graph.IsAcyclic := by
  let G := (hierarchyNetwork H hH).graph
  have strict : ∀ {u v}, Relation.TransGen G.Adj u v → v.val.card < u.val.card := by
    intro u v h
    induction h using Relation.TransGen.trans_induction_on with
    | single h =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact hierarchy_arc_card_lt H hH e
    | trans _ _ ih ih' => exact lt_trans ih' ih
  intro v h
  exact lt_irrefl v.val.card (strict h)

/-- Every cluster vertex is reachable from the root via successive parent arcs. -/
theorem hierarchyNetwork_root_reaches (A : HierarchyVertex H) :
    (hierarchyNetwork H hH).graph.Reaches (hierarchyNetwork H hH).root A := by
  by_cases hA : A.val = univ
  · have hr : A = (hierarchyNetwork H hH).root := Subtype.ext hA
    rw [hr]
    exact .refl
  · let P : HierarchyVertex H :=
      ⟨parentCluster H A.val, hH.parentCluster_mem A.property hA⟩
    have hreach := hierarchyNetwork_root_reaches P
    exact hreach.tail ⟨⟨A, hA⟩, rfl, rfl⟩
termination_by Fintype.card X - A.val.card
decreasing_by
  have hlt := card_lt_card (hH.ssubset_parentCluster A.property hA)
  have hb : (parentCluster H A.val).card ≤ Fintype.card X :=
    Finset.card_le_univ _
  omega

/-- No arc enters the full cluster. -/
theorem hierarchyNetwork_indegree_root :
    (hierarchyNetwork H hH).graph.indegree (hierarchyNetwork H hH).root = 0 := by
  rw [DirectedMultigraph.indegree, Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact e.property (congrArg Subtype.val he)

/-- The one arc entering a non-root cluster is the arc named by that cluster. -/
theorem hierarchyNetwork_indegree_nonroot (A : HierarchyVertex H) (hA : A.val ≠ univ) :
    (hierarchyNetwork H hH).graph.indegree A = 1 := by
  have hset : {e : HierarchyArc H | (hierarchyNetwork H hH).graph.target e = A} =
      {⟨A, hA⟩} := by
    ext e
    change e.val = A ↔ e = ⟨A, hA⟩
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [DirectedMultigraph.indegree, hset, Set.ncard_singleton]

/-- Outgoing arcs of a cluster correspond exactly to its actual child clusters. -/
def hierarchyOutgoingEquiv (A : HierarchyVertex H) :
    {e : HierarchyArc H // (hierarchyNetwork H hH).graph.source e = A} ≃
      {B : Finset X // B ∈ childClusters H A.val} where
  toFun e := ⟨e.val.val.val, by
    have hm := hH.mem_childClusters_parentCluster e.val.val.property e.val.property
    have heq : parentCluster H e.val.val.val = A.val := congrArg Subtype.val e.property
    rwa [heq] at hm⟩
  invFun B := ⟨⟨⟨B.val, (mem_childClusters.mp B.property).1⟩, by
    intro hB
    have hproper := (mem_childClusters.mp B.property).2.1
    rw [hB] at hproper
    exact not_subset_of_ssubset hproper (subset_univ _)⟩,
    Subtype.ext (hH.parentCluster_eq_of_mem_childClusters A.property B.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hierarchyNetwork_outdegree (A : HierarchyVertex H) :
    (hierarchyNetwork H hH).graph.outdegree A = (childClusters H A.val).card := by
  change {e : HierarchyArc H | (hierarchyNetwork H hH).graph.source e = A}.ncard = _
  rw [Set.ncard_congr' (hierarchyOutgoingEquiv H hH A)]
  exact Set.ncard_coe_finset _

/-- A nonsingleton hierarchy realizes all rooted phylogenetic network laws. -/
theorem hierarchyNetwork_isPhylogenetic (hX : 2 ≤ Fintype.card X) :
    (hierarchyNetwork H hH).IsPhylogenetic := by
  refine ⟨inferInstance, inferInstance, inferInstance, hierarchyNetwork_acyclic H hH,
    hierarchyNetwork_root_reaches H hH, hierarchyNetwork_indegree_root H hH, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hierarchyNetwork_indegree_nonroot H hH v
      (fun heq => hv (Subtype.ext heq))]
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Finset.singleton_injective h
  · intro x
    apply hierarchyNetwork_indegree_nonroot
    change ({x} : Finset X) ≠ univ
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, Finset.card_univ] at hc
    omega
  · intro v
    rw [hierarchyNetwork_outdegree]
    constructor
    · intro hv
      have hcard : v.val.card = 1 := by
        have hpos := Finset.card_pos.mpr (hH.2.2.1 v.val v.property)
        by_contra hne
        have htwo : 2 ≤ v.val.card := by omega
        have hchildren := hH.two_le_card_childClusters htwo
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      exact ⟨x, Subtype.ext hx.symm⟩
    · rintro ⟨x, rfl⟩
      simp only [hierarchyNetwork, hH.childClusters_singleton, Finset.card_empty]

/-- The descendants of a non-root cluster are separated by exactly its incoming arc. -/
theorem hierarchyNetwork_subtree_cut (e : HierarchyArc H) :
    ∀ f, (hierarchyNetwork H hH).graph.Crosses f {v | v.val ⊆ e.val.val} ↔ f = e := by
  intro f
  change ((parentCluster H f.val.val ⊆ e.val.val ∧ ¬ f.val.val ⊆ e.val.val) ∨
    (f.val.val ⊆ e.val.val ∧ ¬ parentCluster H f.val.val ⊆ e.val.val)) ↔ f = e
  constructor
  · rintro (⟨hp, hn⟩ | ⟨hc, hn⟩)
    · exact False.elim (hn ((hH.ssubset_parentCluster f.val.property f.property).subset.trans hp))
    · have hfe : f.val.val = e.val.val := by
        by_contra hne
        exact hn (parentCluster_subset e.val.property (lt_of_le_of_ne hc hne))
      exact Subtype.ext (Subtype.ext hfe)
  · intro hfe
    subst f
    exact Or.inr ⟨subset_refl _,
      not_subset_of_ssubset (hH.ssubset_parentCluster e.val.property e.property)⟩

/-- In the hierarchy realization, deleting an arc separates its child cluster
and all descendants from the remaining vertices. -/
theorem hierarchyNetwork_isBridge (e : HierarchyArc H) :
    (hierarchyNetwork H hH).graph.underlying.IsBridge e :=
  ((hierarchyNetwork H hH).graph.isBridge_iff e).mpr
    ⟨{v | v.val ⊆ e.val.val}, hierarchyNetwork_subtree_cut H hH e⟩

/-- The taxa in a descendant side are exactly its cluster's labels. -/
theorem hierarchyNetwork_subtree_leaf_preimage (A : HierarchyVertex H) :
    (hierarchyNetwork H hH).leaf ⁻¹' {v | v.val ⊆ A.val} = (A.val : Set X) := by
  ext x
  exact Finset.singleton_subset_iff

/-- Every non-root cluster supplies its labelled singleton cut in the actual graph. -/
theorem hierarchyNetwork_hasClusterCut (A : HierarchyVertex H) (hA : A.val ≠ univ) :
    (hierarchyNetwork H hH).HasCutSplit (A.val : Set X) :=
  ⟨⟨A, hA⟩, {v | v.val ⊆ A.val}, hierarchyNetwork_subtree_cut H hH ⟨A, hA⟩,
    hierarchyNetwork_subtree_leaf_preimage H hH A⟩

/-- Directed paths in the realization can only shrink clusters. -/
theorem hierarchyNetwork_subset_of_reaches {A B : HierarchyVertex H}
    (h : (hierarchyNetwork H hH).graph.Reaches A B) : B.val ⊆ A.val := by
  induction h with
  | refl => exact subset_refl _
  | @tail C D _ hCD ih =>
    obtain ⟨e, rfl, rfl⟩ := hCD
    exact (hH.ssubset_parentCluster e.val.property e.property).subset.trans ih

/-- Every cluster inclusion is represented by an actual directed path. -/
theorem hierarchyNetwork_reaches_of_subset (A B : HierarchyVertex H) (hBA : B.val ⊆ A.val) :
    (hierarchyNetwork H hH).graph.Reaches A B := by
  by_cases hBAeq : B = A
  · rw [hBAeq]
    exact .refl
  · have hproper : B.val ⊂ A.val := lt_of_le_of_ne hBA
      (fun h => hBAeq (Subtype.ext h))
    have hB : B.val ≠ univ := fun h =>
      not_subset_of_ssubset hproper (h ▸ subset_univ A.val)
    let P : HierarchyVertex H :=
      ⟨parentCluster H B.val, hH.parentCluster_mem B.property hB⟩
    have hPA : P.val ⊆ A.val := parentCluster_subset A.property hproper
    have hreach := hierarchyNetwork_reaches_of_subset A P hPA
    exact hreach.tail ⟨⟨B, hB⟩, rfl, rfl⟩
termination_by Fintype.card X - B.val.card
decreasing_by
  have hlt := card_lt_card (hH.ssubset_parentCluster B.property hB)
  have hb : (parentCluster H B.val).card ≤ Fintype.card X := Finset.card_le_univ _
  omega

/-- The graph's descendant relation is precisely the hierarchy's inclusion relation. -/
theorem hierarchyNetwork_reaches_iff (A B : HierarchyVertex H) :
    (hierarchyNetwork H hH).graph.Reaches A B ↔ B.val ⊆ A.val :=
  ⟨hierarchyNetwork_subset_of_reaches H hH, hierarchyNetwork_reaches_of_subset H hH A B⟩

/-- Taxa descended from a graph vertex are exactly the members of its cluster. -/
theorem hierarchyNetwork_reaches_leaf_iff (A : HierarchyVertex H) (x : X) :
    (hierarchyNetwork H hH).graph.Reaches A ((hierarchyNetwork H hH).leaf x) ↔ x ∈ A.val := by
  rw [hierarchyNetwork_reaches_iff]
  exact Finset.singleton_subset_iff

/-- The realization is connected even in the one-taxon boundary case. -/
theorem hierarchyNetwork_connected : (hierarchyNetwork H hH).graph.IsConnected := by
  intro A B
  exact ((hierarchyNetwork H hH).graph.walks_symm
    ((hierarchyNetwork H hH).graph.walks_of_reaches
      (hierarchyNetwork_root_reaches H hH A))).trans
    ((hierarchyNetwork H hH).graph.walks_of_reaches
      (hierarchyNetwork_root_reaches H hH B))

/-- The finite split-family representation is exactly the set of labelled cuts
of its actual connected graph realization. This is a set correspondence; two
arcs incident to a binary root may induce the same unordered taxon split. -/
theorem hierarchyNetwork_hasCutSplit_iff (A : Finset X) :
    (hierarchyNetwork H hH).HasCutSplit (A : Set X) ↔ A ∈ unroot H := by
  constructor
  · rintro ⟨e, S, hS, hA⟩
    have hu := (hierarchyNetwork H hH).graph.singleton_cuts_eq_or_eq_compl
      (hierarchyNetwork_connected H hH) e hS (hierarchyNetwork_subtree_cut H hH e)
    rcases hu with h | h
    · have heq : A = e.val.val := by
        apply Finset.coe_injective
        rw [← hA, h, hierarchyNetwork_subtree_leaf_preimage]
      rw [heq]
      exact mem_unroot.mpr (Or.inl ⟨e.val.property, e.property⟩)
    · have heq : A = e.val.valᶜ := by
        apply Finset.coe_injective
        rw [← hA, h, Set.preimage_compl, hierarchyNetwork_subtree_leaf_preimage]
        simp only [Finset.coe_compl]
      rw [heq]
      apply mem_unroot.mpr
      right
      simpa only [compl_compl] using And.intro e.val.property e.property
  · intro hA
    rcases mem_unroot.mp hA with ⟨hA, hne⟩ | ⟨hAc, hne⟩
    · exact hierarchyNetwork_hasClusterCut H hH ⟨A, hA⟩ hne
    · apply ((hierarchyNetwork H hH).hasCutSplit_compl (A : Set X)).mp
      simpa only [Finset.coe_compl] using
        hierarchyNetwork_hasClusterCut H hH ⟨Aᶜ, hAc⟩ hne

end Phylogenetics

