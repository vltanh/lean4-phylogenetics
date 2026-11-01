module

public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.Network.Level1.Digraph.CycleHybrid
public import Phylogenetics.Network.Level1.ToRootedNetwork
public import Phylogenetics.Network.Quartets

/-!
# Binary digraphs with edge-disjoint cycles have blobs of level one

The library has two definitions of level-1. `MetricDigraph.IsLevel1` says of a digraph that no two cycles of its undirected
graph share an edge (after Huson et al. 2010). `RootedNetwork.IsLevelOne` says of a rooted network that every blob has at most
one more reticulation arc than reticulation vertices. On a binary digraph with labelled leaves the first implies the second
(`isLevelOne_ofBinary`). Off binary networks this fails, as two cycles through one vertex share no edge and are one blob with two
reticulations.

The bridges of the digraph and of the rooted network are the same (`isBridge_iff_undirected_isBridge`). A cycle through a
reticulation contains its blob, as the other edges at the vertices of a cycle are bridges (`IsBinary.isBridge_of_isCycle`). A cycle
has one hybrid node (`IsBinary.existsUnique_isHybrid`), so a blob has one reticulation, with its two arcs.

## Main results

* `isBridge_iff_undirected_isBridge`: the bridges of the two graphs.
* `isLevelOne_ofBinary`: the implication.
* `IsNetwork.isLevelOne_toRootedNetwork`, `Net.isLevelOne_toRootedNetwork`: the rooted network of a network, and of a
  well-formed term, is level-1.

## References

* D. H. Huson, R. Rupp, C. Scornavacca, *Phylogenetic networks: concepts, algorithms and applications*, Cambridge University
  Press (2010).
-/

@[expose] public noncomputable section

open Finset Phylogenetics.RootedNetwork
open scoped Classical

namespace Phylogenetics.MetricDigraph

variable {V : Type*} {X : Type*} {G : MetricDigraph V X}

/-- A step off the arc `e` is a step of the undirected graph without the edge of `e`. -/
theorem adjOn_compl_iff (hb : G.IsBinary) (e : G.Arc) {a b : V} :
    G.toMultigraph.AdjOn {e}ᶜ a b ↔ (G.undirected.deleteEdges {s(e.1.1, e.1.2)}).Adj a b := by
  have hnot : ∀ {u w : V}, G.Adj u w → ¬ G.Adj w u := @fun u _ huw hwu =>
    hb.acyclic u (Relation.TransGen.tail (Relation.TransGen.single huw) hwu)
  rw [SimpleGraph.deleteEdges_adj, hb.undirected_adj_iff]
  constructor
  · rintro ⟨f, hf, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨Or.inl f.2, fun hmem => hf ?_⟩
      rcases Sym2.eq_iff.1 hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Subtype.ext (Prod.ext h1 h2)
      · exact absurd (h1 ▸ h2 ▸ f.2 : G.Adj e.1.2 e.1.1) (hnot e.2)
    · refine ⟨Or.inr f.2, fun hmem => hf ?_⟩
      rcases Sym2.eq_iff.1 hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1 ▸ h2 ▸ f.2 : G.Adj e.1.2 e.1.1) (hnot e.2)
      · exact Subtype.ext (Prod.ext h2 h1)
  · rintro ⟨hab | hba, hmem⟩
    · refine ⟨⟨(a, b), hab⟩, fun h => hmem ?_, Or.inl ⟨rfl, rfl⟩⟩
      rw [Set.mem_singleton_iff] at h
      subst h
      exact Set.mem_singleton _
    · refine ⟨⟨(b, a), hba⟩, fun h => hmem ?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [Set.mem_singleton_iff] at h
      subst h
      exact Set.mem_singleton_iff.2 (Sym2.eq_swap)

/-- **The bridges of the digraph and of its directed multigraph are the same.** -/
theorem isBridge_iff_undirected_isBridge (hb : G.IsBinary) (e : G.Arc) :
    G.toMultigraph.underlying.IsBridge e ↔ G.undirected.IsBridge s(e.1.1, e.1.2) := by
  rw [SimpleGraph.isBridge_iff, G.toMultigraph.isBridge_iff_not_walks_delete,
    SimpleGraph.reachable_iff_reflTransGen]
  refine not_congr ?_
  change Relation.ReflTransGen _ e.1.1 e.1.2 ↔ _
  exact ⟨Relation.ReflTransGen.mono (fun a b h => (adjOn_compl_iff hb e).1 h) _ _,
    Relation.ReflTransGen.mono (fun a b h => (adjOn_compl_iff hb e).2 h) _ _⟩

theorem indegree_ofBinary (hb : G.IsBinary) (v : V) : (ofBinary hb).graph.indegree v = G.indeg v :=
  G.toMultigraph_indegree v

theorem isHybrid_of_two_le_indegree (hb : G.IsBinary) {v : V} (h : 2 ≤ (ofBinary hb).graph.indegree v) :
    G.IsHybrid v := by
  rw [indegree_ofBinary] at h
  rcases hb.degrees v with hv | hv | hv | hv
  · have := hv.1
    omega
  · have := hv.1
    omega
  · have := hv.1
    omega
  · exact hv

/-- A walk of arcs that are not bridges, from a vertex of a cycle, stays on the cycle. -/
theorem mem_support_of_blobSetoid (hb : G.IsBinary) (h1 : G.IsLevel1) {u : V} {c : G.undirected.Walk u u}
    (hc : c.IsCycle) {a b : V} (ha : a ∈ c.support) (hab : G.toMultigraph.blobSetoid a b) : b ∈ c.support := by
  change Relation.ReflTransGen _ a b at hab
  induction hab with
  | refl => exact ha
  | @tail x y _ hstep ih =>
    obtain ⟨e, hnb, he⟩ := hstep
    have hnb' : ¬ G.undirected.IsBridge s(e.1.1, e.1.2) := fun h =>
      hnb ((isBridge_iff_undirected_isBridge hb e).2 h)
    have hedge : s(e.1.1, e.1.2) = s(x, y) := by
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have h₁' : e.1.1 = x := h₁
        have h₂' : e.1.2 = y := h₂
        rw [h₁', h₂']
      · have h₁' : e.1.1 = y := h₁
        have h₂' : e.1.2 = x := h₂
        rw [h₁', h₂']
        exact Sym2.eq_swap
    have hadj : G.undirected.Adj x y := by
      rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have h₁' : e.1.1 = x := h₁
        have h₂' : e.1.2 = y := h₂
        exact hb.undirected_adj_of_adj (h₁' ▸ h₂' ▸ e.2)
      · have h₁' : e.1.1 = y := h₁
        have h₂' : e.1.2 = x := h₂
        exact (hb.undirected_adj_of_adj (h₁' ▸ h₂' ▸ e.2)).symm
    rw [hedge] at hnb'
    by_contra hy
    refine hnb' (hb.isBridge_of_isCycle h1 hc ih hadj fun hmem => hy ?_)
    exact c.snd_mem_support_of_mem_edges hmem

variable [Fintype V] [Fintype G.Arc]

/-- **A binary digraph in which no two cycles share an edge is level-1 in the sense of its blobs**: a blob with a reticulation
is on a cycle, which has one hybrid node, with its two arcs. -/
theorem isLevelOne_ofBinary (hb : G.IsBinary) (hl : G.IsLabelled) (h1 : G.IsLevel1) : (ofBinary hb).IsLevelOne := by
  have hN := ofBinary_isPhylogenetic hb hl
  intro v
  set N := ofBinary hb with hNdef
  have hsymm : ∀ {a b : V}, N.graph.blobSetoid a b → N.graph.blobSetoid b a := fun h =>
    N.graph.blobSetoid.iseqv.symm h
  have htrans : ∀ {a b c : V}, N.graph.blobSetoid a b → N.graph.blobSetoid b c → N.graph.blobSetoid a c := fun h h' =>
    N.graph.blobSetoid.iseqv.trans h h'
  by_cases hex : ∃ h, 2 ≤ N.graph.indegree h ∧ N.graph.blobSetoid v h
  · obtain ⟨h, hh₂, hvh⟩ := hex
    have hhy := isHybrid_of_two_le_indegree hb hh₂
    have hin : N.graph.indegree h = 2 := (indegree_ofBinary hb h).trans hhy.1
    obtain ⟨k, k', hne, hset⟩ := Set.ncard_eq_two.1 hin
    have hk : N.graph.target k = h := by
      have : k ∈ {e | N.graph.target e = h} := hset ▸ Set.mem_insert _ _
      exact this
    have hk' : N.graph.target k' = h := by
      have : k' ∈ {e | N.graph.target e = h} := hset ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
      exact this
    have hknb := N.not_isBridge_of_two_parents hN hne (hk.trans hk'.symm)
    have hknb' : ¬ G.undirected.IsBridge s(k.1.1, k.1.2) := fun hbr =>
      hknb ((isBridge_iff_undirected_isBridge hb k).2 hbr)
    have hadj : G.undirected.Adj k.1.1 k.1.2 := hb.undirected_adj_of_adj k.2
    rw [SimpleGraph.isBridge_iff_forall_cycle_notMem hadj] at hknb'
    simp only [not_forall, not_not, exists_prop] at hknb'
    obtain ⟨u, c, hc, hmem⟩ := hknb'
    have hhc : h ∈ c.support := by
      have : k.1.2 = h := hk
      exact this ▸ c.snd_mem_support_of_mem_edges hmem
    have huniq := hb.existsUnique_isHybrid h1 hc
    have heq : ∀ w, 2 ≤ N.graph.indegree w → N.graph.blobSetoid v w → w = h := by
      intro w hw₂ hvw
      have hwc := mem_support_of_blobSetoid hb h1 hc hhc (htrans (hsymm hvh) hvw)
      exact huniq.unique ⟨hwc, isHybrid_of_two_le_indegree hb hw₂⟩ ⟨hhc, hhy⟩
    have hB : (univ.filter fun w => 2 ≤ N.graph.indegree w ∧ N.graph.blobSetoid v w).card = 1 := by
      refine card_eq_one.2 ⟨h, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨mem_univ _, hh₂, hvh⟩, fun w hw => ?_⟩⟩
      obtain ⟨-, hw₂, hvw⟩ := mem_filter.1 hw
      exact heq w hw₂ hvw
    have hA : (univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
        N.graph.blobSetoid v (N.graph.target e)).card ≤ 2 := by
      have hsub : ((univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
          N.graph.blobSetoid v (N.graph.target e) : Finset G.Arc) : Set G.Arc).ncard ≤ N.graph.indegree h := by
        unfold DirectedMultigraph.indegree
        refine Set.ncard_le_ncard (fun e he => ?_) (Set.toFinite _)
        obtain ⟨-, hhya, -, hvt⟩ := mem_filter.1 he
        exact heq _ hhya hvt
      rw [Set.ncard_coe_finset, hin] at hsub
      exact hsub
    rw [hB]
    have : ((univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
        N.graph.blobSetoid v (N.graph.target e)).card : ℤ) ≤ 2 := by exact_mod_cast hA
    push_cast
    omega
  · have hA : (univ.filter fun e => N.IsHybridArc e ∧ N.graph.blobSetoid v (N.graph.source e) ∧
        N.graph.blobSetoid v (N.graph.target e)).card = 0 := by
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun e _ he => ?_)
      exact hex ⟨_, he.1, he.2.2⟩
    rw [hA]
    have : (0 : ℤ) ≤ ((univ.filter fun w => 2 ≤ N.graph.indegree w ∧ N.graph.blobSetoid v w).card : ℤ) :=
      Int.natCast_nonneg _
    push_cast
    omega

/-- The rooted network of a network is level-1. -/
theorem IsNetwork.isLevelOne_toRootedNetwork (hG : G.IsNetwork) : (toRootedNetwork hG).IsLevelOne :=
  isLevelOne_ofBinary hG.binary hG.labelled hG.level1

end Phylogenetics.MetricDigraph

namespace Phylogenetics.Net

variable {X : Type*} {N : Net X}

/-- The rooted network of a well-formed term is level-1. -/
theorem isLevelOne_toRootedNetwork [Fintype N.Vert] [Fintype N.toGraph.Arc] (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) :
    (toRootedNetwork hN h2).IsLevelOne :=
  MetricDigraph.IsNetwork.isLevelOne_toRootedNetwork _

end Phylogenetics.Net
