module

public import Phylogenetics.Graph.Basic
/-!
# The definitions of networks are invariant under isomorphisms

An isomorphism of metric digraphs (`Phylogenetics.MetricDigraph.Iso`) preserves the edges, the leaf
labels, the edge lengths and the inheritance probabilities of the hybrid edges; so isomorphic
graphs are networks together (`Phylogenetics.MetricDigraph.Iso.isNetwork_iff`).
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph

variable {X : Type u}

namespace MetricDigraph

variable {V W : Type*} {G : MetricDigraph V X} {H : MetricDigraph W X}

/-- An isomorphism preserves the directed paths. -/
theorem Iso.transGen_apply (e : G.Iso H) {u v : V} :
    Relation.TransGen H.Adj (e u) (e v) → Relation.TransGen G.Adj u v := by
  suffices ∀ w w', Relation.TransGen H.Adj w w' → Relation.TransGen G.Adj (e.symm w) (e.symm w') by
    simpa using this (e u) (e v)
  intro w w' h
  induction h with
  | single h =>
    refine .single ?_
    rw [← e.adj_apply]
    simpa using h
  | tail _ h ih =>
    refine ih.tail ?_
    rw [← e.adj_apply]
    simpa using h

private theorem p8g_label_apply (e : G.Iso H) (v : V) : H.label (e v) = G.label v := e.label_eq v

private theorem p8g_len_apply (e : G.Iso H) {u v : V} (h : G.Adj u v) :
    H.len (e u) (e v) = G.len u v := e.len_eq u v h

private theorem p8g_inh_apply (e : G.Iso H) {u v : V} (h : G.Adj u v) (hv : G.IsHybrid v) :
    H.inh (e u) (e v) = G.inh u v := e.inh_eq u v h hv

/-- A graph isomorphic to a network is a network. -/
theorem IsNetwork.of_iso (hG : G.IsNetwork) (e : G.Iso H) : H.IsNetwork := by
  obtain ⟨hb, h1, hm, hl⟩ := hG
  have := hb.finite
  have hsurj : ∀ w, ∃ v, e v = w := fun w => ⟨e.symm w, e.apply_symm_apply w⟩
  refine ⟨⟨Finite.of_equiv V e.toEquiv, fun w hw => ?_, ?_, fun w => ?_⟩, ?_, ⟨?_, ?_, ?_⟩,
    ⟨fun w => ?_, ?_⟩⟩
  · obtain ⟨v, rfl⟩ := hsurj w
    exact hb.acyclic v (e.transGen_apply hw)
  · obtain ⟨r, hr, huniq⟩ := hb.existsUnique_indeg_eq_zero
    refine ⟨e r, show H.indeg (e r) = 0 by rw [e.indeg_eq]; exact hr, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := hsurj w
    rw [e.indeg_eq] at hw
    rw [huniq v hw]
  · obtain ⟨v, rfl⟩ := hsurj w
    rw [e.isRoot_iff, e.isLeaf_iff, e.isTreeNode_iff, e.isHybrid_iff]
    exact hb.degrees v
  · -- the cycles of `H` are the images of the cycles of `G`
    intro u v c c' hc hc' hcc'
    let f : H.undirected →g G.undirected := e.symm.undirectedIso.toHom
    have hf : Function.Injective f := e.symm.undirectedIso.injective
    have hmap := h1 (c.map f) (c'.map f) ((Walk.isCycle_map_iff_of_injective hf).2 hc)
      ((Walk.isCycle_map_iff_of_injective hf).2 hc') (by
        obtain ⟨x, hx, hx'⟩ := hcc'
        exact ⟨Sym2.map f x, by rw [Walk.edgeSet_map]; exact ⟨x, hx, rfl⟩,
          by rw [Walk.edgeSet_map]; exact ⟨x, hx', rfl⟩⟩)
    rw [Walk.edgeSet_map, Walk.edgeSet_map] at hmap
    exact (Set.image_injective.2 (Sym2.map.injective hf)) hmap
  · intro w w' hww'
    obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨v', rfl⟩ := hsurj w'
    rw [e.adj_apply] at hww'
    rw [p8g_len_apply e hww']
    exact hm.len_pos v v' hww'
  · intro w w' hww' hw'
    obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨v', rfl⟩ := hsurj w'
    rw [e.adj_apply] at hww'
    rw [e.isHybrid_iff] at hw'
    rw [p8g_inh_apply e hww' hw']
    exact hm.inh_mem_Ioo v v' hww' hw'
  · intro w₁ w₂ w hw₁ hw₂ hne hw
    obtain ⟨v₁, rfl⟩ := hsurj w₁
    obtain ⟨v₂, rfl⟩ := hsurj w₂
    obtain ⟨v, rfl⟩ := hsurj w
    rw [e.adj_apply] at hw₁ hw₂
    rw [e.isHybrid_iff] at hw
    rw [p8g_inh_apply e hw₁ hw, p8g_inh_apply e hw₂ hw]
    exact hm.inh_add_inh v₁ v₂ v hw₁ hw₂ (fun h => hne (by rw [h])) hw
  · obtain ⟨v, rfl⟩ := hsurj w
    rw [p8g_label_apply, e.isLeaf_iff]
    exact hl.isSome_label_iff v
  · intro w w' x hw hw'
    obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨v', rfl⟩ := hsurj w'
    rw [p8g_label_apply] at hw hw'
    rw [hl.label_injective v v' x hw hw']

/-- **Isomorphic graphs are networks together.** The definitions of `Phylogenetics.Graph.Defs`
depend only on the edges, the leaf labels, the edge lengths and the inheritance probabilities of
the hybrid edges, which an isomorphism preserves. -/
theorem Iso.isNetwork_iff (e : G.Iso H) : G.IsNetwork ↔ H.IsNetwork :=
  ⟨fun hG => hG.of_iso e, fun hH => hH.of_iso e.symm⟩

end MetricDigraph

end Phylogenetics
