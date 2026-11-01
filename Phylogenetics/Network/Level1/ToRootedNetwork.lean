module

public import Phylogenetics.Network.Defs
public import Phylogenetics.Network.Level1.Digraph.Correspondence
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.BigOperators

/-!
# Level-1 networks as rooted networks

The library has three descriptions of a network: the terms `Phylogenetics.Net`, the digraphs
`Phylogenetics.MetricDigraph` (the two are equivalent by
`Phylogenetics.MetricDigraph.isNetwork_iff_exists_net`), and the general
`Phylogenetics.RootedNetwork`, on arbitrary vertex and arc types. This module maps the first two to
the third, with the same vertices, arcs, edge lengths and inheritance probabilities.

* `MetricDigraph.Arc G`, `MetricDigraph.Taxon G`: the arcs of a digraph, as a type, and the taxa that
  label its leaves.
* `MetricDigraph.toMultigraph G`, `MetricDigraph.ofBinary hb`, `MetricDigraph.toRootedNetwork hG`,
  `MetricDigraph.metricData G`:
  the rooted network of a network `hG : G.IsNetwork` and its numerical parameters.
* `Net.toRootedNetwork hN h2`, `Net.metricData N`: the same for a well-formed term with at least two
  leaves.

## Main results

* `MetricDigraph.toMultigraph_adj`, `toMultigraph_indegree`, `toMultigraph_outdegree`: the multigraph
  has the adjacency and the degrees of the digraph.
* `MetricDigraph.toRootedNetwork_isPhylogenetic`, `toRootedNetwork_isBinary`,
  `toRootedNetwork_isMetric`: a rooted binary metric level-1 network is a binary phylogenetic network
  with valid parameters.
* `Net.toRootedNetwork_isPhylogenetic`, `Net.toRootedNetwork_isBinary`, `Net.toRootedNetwork_isMetric`.

`Phylogenetics.NMSC.Level1.General` proves that the network multispecies coalescent
`Phylogenetics.Net.geneTreeDist` of a term is `Phylogenetics.geneTreeDist` at inheritance correlation `0`
of its rooted network.
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v

namespace MetricDigraph

variable {V : Type u} {X : Type v} (G : MetricDigraph V X)

/-- The arcs of a digraph, as a type: the pairs of adjacent vertices. -/
abbrev Arc : Type u := {p : V × V // G.Adj p.1 p.2}

/-- The taxa of a digraph: those that label a vertex. -/
abbrev Taxon : Type v := {x : X // ∃ v, G.label v = some x}

/-- The directed multigraph of a digraph, with one arc for each edge. -/
def toMultigraph : DirectedMultigraph V G.Arc where
  source e := e.1.1
  target e := e.1.2

theorem toMultigraph_adj {u v : V} : G.toMultigraph.Adj u v ↔ G.Adj u v := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    exact e.2
  · exact fun h => ⟨⟨(u, v), h⟩, rfl, rfl⟩

theorem toMultigraph_adj_eq : G.toMultigraph.Adj = G.Adj := by
  funext u v
  exact propext G.toMultigraph_adj

/-- The arcs entering `v` are the in-neighbours of `v`. -/
theorem toMultigraph_indegree (v : V) : G.toMultigraph.indegree v = G.indeg v := by
  unfold DirectedMultigraph.indegree indeg
  refine Set.ncard_congr (fun e _ => e.1.1) (fun e he => ?_) (fun a b ha hb h => ?_) fun u hu => ?_
  · obtain rfl : e.1.2 = v := he
    exact e.2
  · obtain ⟨⟨a₁, a₂⟩, ha'⟩ := a
    obtain ⟨⟨b₁, b₂⟩, hb'⟩ := b
    obtain rfl : a₂ = v := ha
    obtain rfl : b₂ = a₂ := hb
    obtain rfl : a₁ = b₁ := h
    rfl
  · exact ⟨⟨(u, v), hu⟩, rfl, rfl⟩

/-- The arcs leaving `v` are the out-neighbours of `v`. -/
theorem toMultigraph_outdegree (v : V) : G.toMultigraph.outdegree v = G.outdeg v := by
  unfold DirectedMultigraph.outdegree outdeg
  refine Set.ncard_congr (fun e _ => e.1.2) (fun e he => ?_) (fun a b ha hb h => ?_) fun u hu => ?_
  · obtain rfl : e.1.1 = v := he
    exact e.2
  · obtain ⟨⟨a₁, a₂⟩, ha'⟩ := a
    obtain ⟨⟨b₁, b₂⟩, hb'⟩ := b
    obtain rfl : a₁ = v := ha
    obtain rfl : b₁ = a₁ := hb
    obtain rfl : a₂ = b₂ := h
    rfl
  · exact ⟨⟨(v, u), hu⟩, rfl, rfl⟩

variable {G}

/-- The rooted network of a binary digraph: its root is the vertex of in-degree zero, and a taxon labels the
leaf with its label. -/
def ofBinary (hb : G.IsBinary) : RootedNetwork V G.Arc G.Taxon where
  graph := G.toMultigraph
  root := hb.existsUnique_indeg_eq_zero.choose
  leaf x := x.2.choose

/-- The rooted network of a network. -/
def toRootedNetwork (hG : G.IsNetwork) : RootedNetwork V G.Arc G.Taxon := ofBinary hG.binary

variable (G) in
/-- The numerical parameters of the digraph, on its arcs: the lengths of the edges, and the inheritance
probabilities of the hybrid edges. A tree edge has inheritance probability one. -/
def metricData : RootedNetwork.MetricData G.Arc :=
  open Classical in
  { length := fun e => G.len e.1.1 e.1.2
    inheritance := fun e => if G.IsHybrid e.1.2 then G.inh e.1.1 e.1.2 else 1 }

theorem toRootedNetwork_root_indeg (hG : G.IsNetwork) : G.indeg (toRootedNetwork hG).root = 0 :=
  hG.binary.existsUnique_indeg_eq_zero.choose_spec.1

theorem eq_toRootedNetwork_root (hG : G.IsNetwork) {v : V} (hv : G.indeg v = 0) :
    v = (toRootedNetwork hG).root :=
  hG.binary.existsUnique_indeg_eq_zero.choose_spec.2 v hv

theorem label_toRootedNetwork_leaf (hG : G.IsNetwork) (x : G.Taxon) :
    G.label ((toRootedNetwork hG).leaf x) = some x.1 :=
  x.2.choose_spec

/-- The vertices with a label are the leaves. -/
theorem isLeaf_of_label_eq_some (hG : G.IsNetwork) {v : V} {x : X} (h : G.label v = some x) :
    G.IsLeaf v :=
  (hG.labelled.isSome_label_iff v).1 (by simp [h])

theorem ofBinary_root_indeg (hb : G.IsBinary) : G.indeg (ofBinary hb).root = 0 :=
  hb.existsUnique_indeg_eq_zero.choose_spec.1

theorem eq_ofBinary_root (hb : G.IsBinary) {v : V} (hv : G.indeg v = 0) : v = (ofBinary hb).root :=
  hb.existsUnique_indeg_eq_zero.choose_spec.2 v hv

theorem label_ofBinary_leaf (hb : G.IsBinary) (x : G.Taxon) :
    G.label ((ofBinary hb).leaf x) = some x.1 :=
  x.2.choose_spec

/-- The vertices with a label are the leaves. -/
theorem IsLabelled.isLeaf_of_label_eq_some (hl : G.IsLabelled) {v : V} {x : X} (h : G.label v = some x) :
    G.IsLeaf v :=
  (hl.isSome_label_iff v).1 (by simp [h])

/-- A binary digraph with labelled leaves is a phylogenetic network, with the same vertices and arcs. -/
theorem ofBinary_isPhylogenetic (hb : G.IsBinary) (hl : G.IsLabelled) :
    (ofBinary hb).IsPhylogenetic := by
  have hfin : Finite V := hb.finite
  have hroot := ofBinary_root_indeg hb
  refine
    { finite_vertices := hfin
      finite_arcs := Subtype.finite
      finite_taxa := ?_
      acyclic := ?_
      root_reaches := ?_
      root_indegree := ?_
      nonroot_indegree := ?_
      leaf_injective := ?_
      leaf_indegree := ?_
      leaves := ?_ }
  · refine Finite.of_injective (fun x : G.Taxon => (ofBinary hb).leaf x) fun a b h => ?_
    have ha := label_ofBinary_leaf hb a
    have hb := label_ofBinary_leaf hb b
    simp only at h
    rw [h, hb] at ha
    exact Subtype.ext (Option.some.inj ha).symm
  · intro v h
    change Relation.TransGen G.toMultigraph.Adj v v at h
    rw [toMultigraph_adj_eq] at h
    exact hb.acyclic v h
  · intro v
    change Relation.ReflTransGen G.toMultigraph.Adj _ v
    rw [toMultigraph_adj_eq]
    exact hb.reflTransGen_root hroot v
  · exact (G.toMultigraph_indegree _).trans hroot
  · intro v hv
    change 1 ≤ G.toMultigraph.indegree v
    rw [toMultigraph_indegree, Nat.one_le_iff_ne_zero]
    exact fun h => hv (eq_ofBinary_root hb h)
  · intro a b h
    have ha := label_ofBinary_leaf hb a
    have hb := label_ofBinary_leaf hb b
    rw [h, hb] at ha
    exact Subtype.ext (Option.some.inj ha).symm
  · intro x
    change G.toMultigraph.indegree _ = 1
    rw [toMultigraph_indegree]
    exact (hl.isLeaf_of_label_eq_some (label_ofBinary_leaf hb x)).1
  · intro v
    change G.toMultigraph.outdegree v = 0 ↔ _
    rw [toMultigraph_outdegree]
    constructor
    · intro h
      have hleaf : G.IsLeaf v := by
        rcases hb.degrees v with hv | hv | hv | hv
        · have := hv.2
          omega
        · exact hv
        · have := hv.2
          omega
        · have := hv.2
          omega
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((hl.isSome_label_iff v).2 hleaf)
      refine ⟨⟨x, v, hx⟩, ?_⟩
      exact hl.label_injective _ _ x (label_ofBinary_leaf hb ⟨x, v, hx⟩) hx
    · rintro ⟨x, rfl⟩
      exact (hl.isLeaf_of_label_eq_some (label_ofBinary_leaf hb x)).2

/-- A rooted binary metric level-1 network is binary as a rooted network. -/
theorem ofBinary_isBinary (hb : G.IsBinary) : (ofBinary hb).IsBinary := by
  have hroot := ofBinary_root_indeg hb
  constructor
  · change G.toMultigraph.outdegree _ = 2
    rw [toMultigraph_outdegree]
    rcases hb.degrees (ofBinary hb).root with h | h | h | h
    · exact h.2
    · have := h.1; omega
    · have := h.1; omega
    · have := h.1; omega
  · intro v hv hout
    change G.toMultigraph.indegree v + G.toMultigraph.outdegree v = 3
    change G.toMultigraph.outdegree v ≠ 0 at hout
    rw [toMultigraph_outdegree] at hout
    rw [toMultigraph_indegree, toMultigraph_outdegree]
    rcases hb.degrees v with h | h | h | h
    · exact absurd (eq_ofBinary_root hb h.1) hv
    · exact absurd h.2 hout
    · rw [h.1, h.2]
    · rw [h.1, h.2]

/-- A rooted binary metric level-1 network is a phylogenetic network, with the same vertices and
arcs. -/
theorem toRootedNetwork_isPhylogenetic (hG : G.IsNetwork) :
    (toRootedNetwork hG).IsPhylogenetic :=
  ofBinary_isPhylogenetic hG.binary hG.labelled

theorem toRootedNetwork_isBinary (hG : G.IsNetwork) : (toRootedNetwork hG).IsBinary :=
  ofBinary_isBinary hG.binary

/-- In a network, in-degree at least two means a hybrid node. -/
theorem isHybrid_of_two_le_indeg (hG : G.IsNetwork) {v : V} (h : 2 ≤ G.indeg v) : G.IsHybrid v := by
  rcases hG.binary.degrees v with hv | hv | hv | hv
  · have := hv.1; omega
  · have := hv.1; omega
  · have := hv.1; omega
  · exact hv

/-- The numerical parameters of a rooted binary metric level-1 network are valid parameters of its
rooted network. -/
theorem toRootedNetwork_isMetric [Fintype G.Arc] (hG : G.IsNetwork) :
    (toRootedNetwork hG).IsMetric G.metricData := by
  classical
  have hhyb : ∀ e : G.Arc, (toRootedNetwork hG).IsHybridArc e → G.IsHybrid e.1.2 := fun e he => by
    have he' : 2 ≤ G.toMultigraph.indegree e.1.2 := he
    rw [toMultigraph_indegree] at he'
    exact isHybrid_of_two_le_indeg hG he'
  refine ⟨fun e _ => hG.metric.len_pos _ _ e.2, fun e _ => (hG.metric.len_pos _ _ e.2).le,
    fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · have he' : G.toMultigraph.indegree e.1.2 = 1 := he
    rw [toMultigraph_indegree] at he'
    have hne : ¬ G.IsHybrid e.1.2 := fun h => by
      have := h.1
      omega
    simp [metricData, hne]
  · have h := hhyb e he
    simp only [metricData, h, ↓reduceIte]
    exact (hG.metric.inh_mem_Ioo _ _ e.2 h).1
  · have hv' : 2 ≤ G.toMultigraph.indegree v := hv
    rw [toMultigraph_indegree] at hv'
    have hh := isHybrid_of_two_le_indeg hG hv'
    obtain ⟨u, u', huu', hu⟩ := indeg_eq_two_iff.1 hh.1
    have hau : G.Adj u v := (hu u).2 (Or.inl rfl)
    have hau' : G.Adj u' v := (hu u').2 (Or.inr rfl)
    have hne : (⟨(u, v), hau⟩ : G.Arc) ≠ ⟨(u', v), hau'⟩ := fun h => huu' (by
      simpa using congrArg (fun e : G.Arc => e.1.1) h)
    have hf : (Finset.univ.filter fun e : G.Arc => e.1.2 = v) =
        {⟨(u, v), hau⟩, ⟨(u', v), hau'⟩} := by
      ext ⟨⟨a, b⟩, hab⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
      constructor
      · rintro rfl
        rcases (hu a).1 hab with rfl | rfl
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rintro (⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rfl
    have heq : (∑ e : G.Arc, if (toRootedNetwork hG).graph.target e = v then
        G.metricData.inheritance e else 0) =
        ∑ e ∈ Finset.univ.filter fun e : G.Arc => e.1.2 = v, G.metricData.inheritance e := by
      rw [Finset.sum_filter]
      rfl
    rw [heq, hf, Finset.sum_pair hne]
    simp only [metricData, hh, ↓reduceIte]
    exact hG.metric.inh_add_inh u u' v hau hau' huu' hh

end MetricDigraph

namespace Net

variable {X : Type u} {N : Net X}

/-- The rooted network of a well-formed network term with at least two leaves. -/
def toRootedNetwork (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) :
    RootedNetwork N.Vert N.toGraph.Arc N.toGraph.Taxon :=
  MetricDigraph.toRootedNetwork (Net.isNetwork_toGraph hN h2)

variable (N) in
/-- The numerical parameters of a network term, on the arcs of its graph. -/
def metricData : RootedNetwork.MetricData N.toGraph.Arc := N.toGraph.metricData

theorem toRootedNetwork_isPhylogenetic (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) :
    (toRootedNetwork hN h2).IsPhylogenetic :=
  MetricDigraph.toRootedNetwork_isPhylogenetic _

theorem toRootedNetwork_isBinary (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) :
    (toRootedNetwork hN h2).IsBinary :=
  MetricDigraph.toRootedNetwork_isBinary _

theorem toRootedNetwork_isMetric [Fintype N.toGraph.Arc] (hN : N.WellFormed)
    (h2 : 2 ≤ N.leaves.length) :
    (toRootedNetwork hN h2).IsMetric N.metricData :=
  MetricDigraph.toRootedNetwork_isMetric _

/-- A taxon of the rooted network of a term is a leaf of the term. -/
theorem taxon_iff {x : X} : (∃ v, N.toGraph.label v = some x) ↔ x ∈ N.leaves :=
  N.exists_label_eq_some_iff x

end Net

end Phylogenetics
