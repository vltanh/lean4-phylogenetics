module

public import Phylogenetics.Tree.Defs
public import Phylogenetics.Network.Basic

/-!
# The ancestral restriction of a network

The graph on a set of taxa that retains every ancestor of those taxa and every arc whose target is
retained, before suppression. It preserves the identity of the arcs, parallel arcs included, and the
original root. `Phylogenetics.Network.Induced` truncates it at the least stable ancestor and suppresses
vertices of degree two.

## Main results

* `AncestralVertex`, `AncestralArc`, `ancestralGraph`, `ancestralNetwork`: the restriction.
* `ancestralGraph_reaches_iff`, `ancestralGraph_isAcyclic`, `ancestralGraph_indegree`,
  `ancestralGraph_leaves`: how it relates to the original graph.
* `ancestralNetwork_isPhylogenetic`: on a nonempty set of taxa, it keeps the laws of a network.
-/

@[expose] public section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- Vertices of the unsuppressed ancestral graph. -/
abbrev AncestralVertex (Y : Set X) := N.ancestralVertices Y

/-- Arcs of the unsuppressed ancestral graph, retaining their original identities. -/
abbrev AncestralArc (Y : Set X) := N.ancestralArcs Y

/-- Every selected taxon belongs to its ancestral restriction. -/
theorem leaf_mem_ancestralVertices {Y : Set X} {x : X} (hx : x ∈ Y) :
    N.leaf x ∈ N.ancestralVertices Y :=
  ⟨x, hx, Relation.ReflTransGen.refl⟩

/-- The retained vertex set is closed under taking ancestors. -/
theorem mem_ancestralVertices_of_reaches {Y : Set X} {u v : V}
    (h : N.graph.Reaches u v) (hv : v ∈ N.ancestralVertices Y) :
    u ∈ N.ancestralVertices Y := by
  obtain ⟨x, hx, hvx⟩ := hv
  exact ⟨x, hx, h.trans hvx⟩

/-- Retaining an arc's target also retains its source. -/
theorem source_mem_ancestralVertices {Y : Set X} {e : E}
    (he : e ∈ N.ancestralArcs Y) :
    N.graph.source e ∈ N.ancestralVertices Y :=
  N.mem_ancestralVertices_of_reaches
    (Relation.ReflTransGen.single ⟨e, rfl, rfl⟩) he

/-- The actual directed graph on ancestral vertex and arc subtypes. -/
def ancestralGraph (Y : Set X) :
    DirectedMultigraph (N.AncestralVertex Y) (N.AncestralArc Y) where
  source e := ⟨N.graph.source e.val, N.source_mem_ancestralVertices e.property⟩
  target e := ⟨N.graph.target e.val, e.property⟩

@[simp] theorem ancestralGraph_source_val (Y : Set X) (e : N.AncestralArc Y) :
    ((N.ancestralGraph Y).source e).val = N.graph.source e.val := rfl

@[simp] theorem ancestralGraph_target_val (Y : Set X) (e : N.AncestralArc Y) :
    ((N.ancestralGraph Y).target e).val = N.graph.target e.val := rfl

/-- Restriction preserves precisely the original adjacencies between retained vertices. -/
theorem ancestralGraph_adj_iff (Y : Set X) (u v : N.AncestralVertex Y) :
    (N.ancestralGraph Y).Adj u v ↔ N.graph.Adj u.val v.val := by
  constructor
  · rintro ⟨e, hs, ht⟩
    exact ⟨e.val, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · rintro ⟨e, hs, ht⟩
    have he : e ∈ N.ancestralArcs Y := by
      change N.graph.target e ∈ N.ancestralVertices Y
      rw [ht]
      exact v.property
    exact ⟨⟨e, he⟩, Subtype.ext hs, Subtype.ext ht⟩

/-- A path ending at a retained vertex lies entirely in the ancestral restriction. -/
theorem ancestralGraph_lift_reaches {Y : Set X} {u v : V}
    (h : N.graph.Reaches u v) (hv : v ∈ N.ancestralVertices Y) :
    (N.ancestralGraph Y).Reaches
      ⟨u, N.mem_ancestralVertices_of_reaches h hv⟩ ⟨v, hv⟩ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head u w huw hwv ih =>
    exact ih.head ((N.ancestralGraph_adj_iff Y _ _).mpr huw)

/-- Reachability between retained vertices agrees with reachability in the original graph. -/
theorem ancestralGraph_reaches_iff (Y : Set X) (u v : N.AncestralVertex Y) :
    (N.ancestralGraph Y).Reaches u v ↔ N.graph.Reaches u.val v.val := by
  constructor
  · exact Relation.ReflTransGen.lift Subtype.val
      (fun a b h => (N.ancestralGraph_adj_iff Y a b).mp h) u v
  · intro h
    exact N.ancestralGraph_lift_reaches h v.property

/-- Restriction preserves acyclicity. -/
theorem ancestralGraph_isAcyclic (Y : Set X) (hN : N.graph.IsAcyclic) :
    (N.ancestralGraph Y).IsAcyclic := by
  intro v h
  apply hN v.val
  exact Relation.TransGen.lift Subtype.val
    (fun a b h => (N.ancestralGraph_adj_iff Y a b).mp h) v v h

/-- The original root is retained whenever some selected taxon is reachable from it. -/
theorem root_mem_ancestralVertices {Y : Set X} (hY : Y.Nonempty)
    (hroot : ∀ v, N.graph.Reaches N.root v) :
    N.root ∈ N.ancestralVertices Y := by
  obtain ⟨x, hx⟩ := hY
  exact ⟨x, hx, hroot (N.leaf x)⟩

/-- The taxon labeling in the ancestral restriction. -/
def ancestralLeaf (Y : Set X) : Y → N.AncestralVertex Y :=
  fun x => ⟨N.leaf x.val, N.leaf_mem_ancestralVertices x.property⟩

@[simp] theorem ancestralLeaf_val (Y : Set X) (x : Y) :
    (N.ancestralLeaf Y x).val = N.leaf x.val := rfl

/-- Rooted and labeled data for the unsuppressed ancestral graph.
No network validity theorem is assumed in this data structure;
`ancestralNetwork_isPhylogenetic` proves validity from the original network laws. -/
def ancestralNetwork (Y : Set X) (hY : Y.Nonempty)
    (hroot : ∀ v, N.graph.Reaches N.root v) :
    RootedNetwork (N.AncestralVertex Y) (N.AncestralArc Y) Y where
  graph := N.ancestralGraph Y
  root := ⟨N.root, N.root_mem_ancestralVertices hY hroot⟩
  leaf := N.ancestralLeaf Y

/-- The retained root reaches every retained vertex. -/
theorem ancestralNetwork_root_reaches (Y : Set X) (hY : Y.Nonempty)
    (hroot : ∀ v, N.graph.Reaches N.root v) (v : N.AncestralVertex Y) :
    (N.ancestralNetwork Y hY hroot).graph.Reaches
      (N.ancestralNetwork Y hY hroot).root v :=
  (N.ancestralGraph_reaches_iff Y _ _).mpr (hroot v.val)

/-- Restriction preserves injectivity of taxon labels. -/
theorem ancestralLeaf_injective (Y : Set X) (hN : Function.Injective N.leaf) :
    Function.Injective (N.ancestralLeaf Y) := by
  intro x y h
  exact Subtype.ext (hN (congrArg Subtype.val h))

/-- Restricting to a larger taxon set can only add ancestral vertices. -/
theorem ancestralVertices_mono {Y Z : Set X} (hYZ : Y ⊆ Z) :
    N.ancestralVertices Y ⊆ N.ancestralVertices Z := by
  rintro v ⟨x, hx, hv⟩
  exact ⟨x, hYZ hx, hv⟩

/-- Restricting to a larger taxon set can only add ancestral arcs. -/
theorem ancestralArcs_mono {Y Z : Set X} (hYZ : Y ⊆ Z) :
    N.ancestralArcs Y ⊆ N.ancestralArcs Z :=
  fun _ he => N.ancestralVertices_mono hYZ he


/-- All arcs entering a retained vertex are retained, with arc identity preserved. -/
def ancestralIncomingEquiv (Y : Set X) (v : N.AncestralVertex Y) :
    {e : N.AncestralArc Y // (N.ancestralGraph Y).target e = v} ≃
      {e : E // N.graph.target e = v.val} where
  toFun e := ⟨e.val.val, congrArg Subtype.val e.property⟩
  invFun e := ⟨⟨e.val, by
    change N.graph.target e.val ∈ N.ancestralVertices Y
    rw [e.property]
    exact v.property⟩, Subtype.ext e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ancestral restriction preserves each retained vertex's indegree. -/
theorem ancestralGraph_indegree (Y : Set X) (v : N.AncestralVertex Y) :
    (N.ancestralGraph Y).indegree v = N.graph.indegree v.val :=
  Set.ncard_congr' (N.ancestralIncomingEquiv Y v)

/-- The sinks of the unsuppressed ancestral graph are precisely its selected taxon labels. -/
theorem ancestralGraph_leaves (hN : N.IsPhylogenetic) (Y : Set X)
    (v : N.AncestralVertex Y) :
    (N.ancestralGraph Y).outdegree v = 0 ↔ ∃ x : Y, N.ancestralLeaf Y x = v := by
  let : Finite E := hN.finite_arcs
  constructor
  · intro hv
    obtain ⟨x, hx, hpath⟩ := v.property
    have hpath' : (N.ancestralGraph Y).Reaches v (N.ancestralLeaf Y ⟨x, hx⟩) :=
      (N.ancestralGraph_reaches_iff Y _ _).mpr hpath
    exact ⟨⟨x, hx⟩, (N.ancestralGraph Y).eq_of_reaches_of_outdegree_eq_zero hpath' hv⟩
  · rintro ⟨x, rfl⟩
    apply ((N.ancestralGraph Y).outdegree_eq_zero_iff _).mpr
    intro e he
    have hzero := (hN.leaves (N.leaf x.val)).mpr ⟨x.val, rfl⟩
    exact (N.graph.outdegree_eq_zero_iff _).mp hzero e.val (congrArg Subtype.val he)

/-- Keeping a nonempty set of taxa preserves all defining laws of the rooted
unsuppressed network. This retains the original root, even for one selected taxon. -/
theorem ancestralNetwork_isPhylogenetic (hN : N.IsPhylogenetic)
    (Y : Set X) (hY : Y.Nonempty) :
    (N.ancestralNetwork Y hY hN.root_reaches).IsPhylogenetic := by
  let : Finite V := hN.finite_vertices
  let : Finite E := hN.finite_arcs
  let : Finite X := hN.finite_taxa
  refine ⟨inferInstance, inferInstance, inferInstance,
    N.ancestralGraph_isAcyclic Y hN.acyclic,
    N.ancestralNetwork_root_reaches Y hY hN.root_reaches,
    ?_, ?_, N.ancestralLeaf_injective Y hN.leaf_injective, ?_, ?_⟩
  · change (N.ancestralGraph Y).indegree _ = 0
    rw [N.ancestralGraph_indegree]
    exact hN.root_indegree
  · intro v hv
    change 1 ≤ (N.ancestralGraph Y).indegree v
    rw [N.ancestralGraph_indegree]
    apply hN.nonroot_indegree v.val
    intro heq
    exact hv (Subtype.ext heq)
  · intro x
    change (N.ancestralGraph Y).indegree (N.ancestralLeaf Y x) = 1
    rw [N.ancestralGraph_indegree]
    exact hN.leaf_indegree x.val
  · exact N.ancestralGraph_leaves hN Y


end Phylogenetics.RootedNetwork
