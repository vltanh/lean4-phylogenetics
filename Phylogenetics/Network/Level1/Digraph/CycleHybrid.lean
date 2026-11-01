module

public import Phylogenetics.Network.Level1.Digraph.Basic
/-!
# Every cycle of a level-1 network contains exactly one hybrid node

In a rooted binary level-1 network, every cycle contains exactly one hybrid node
(`Phylogenetics.MetricDigraph.IsNetwork.existsUnique_isHybrid`).

The proof looks at the directions of the edges along a cycle `c`. A *sink* of `c` is a vertex
whose two neighbours along `c` are its parents, a *source* one whose two neighbours along `c` are
its children.
* A vertex of `c` with no descendant on `c` is a sink, and a sink has two parents: a hybrid node.
* A hybrid node of `c` is a sink: otherwise one of its two parents is not a neighbour along `c`;
  by `Phylogenetics.MetricDigraph.IsBinary.isBridge_of_isCycle` the edge from that parent would be
  a bridge, while a path from the root to the other parent avoids it.
* Between two sinks, each of the two arcs of `c` has a highest vertex, which is a source; so two
  sinks give two sources.
* A cycle has at most one source: the parent edge of a source that is not an ancestor of another
  source would be a bridge (`isBridge_of_isCycle` again), while a path from the root to the other
  source, followed by an arc of `c`, avoids it.
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph

namespace MetricDigraph

variable {V : Type*} {X : Type u} {G : MetricDigraph V X}

/-- In a binary network, the edge from a vertex `a` to its parent `p` is not a bridge when a walk
avoiding it leads from `a` to a vertex `b` that is not a descendant of `a`: going up from `b`
to the root and down to `p` avoids it too. -/
private theorem p8g_not_isBridge (hb : G.IsBinary) {a p b : V} (hpa : G.Adj p a)
    (hab : ¬ Relation.ReflTransGen G.Adj a b) (W : G.undirected.Walk a b)
    (hW : s(a, p) ∉ W.edges) : ¬ G.undirected.IsBridge s(a, p) := by
  obtain ⟨r, hr, -⟩ := hb.exists_isRoot
  obtain ⟨Pb, -, -, hPb⟩ := hb.exists_isPath_of_reflTransGen (hb.reflTransGen_root hr.1 b)
  obtain ⟨Pp, -, -, hPp⟩ := hb.exists_isPath_of_reflTransGen (hb.reflTransGen_root hr.1 p)
  intro hbr
  have := isBridge_iff_forall_walk_mem_edges.1 hbr (W.append (Pb.reverse.append Pp))
  simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at this
  rcases this with h | h | h
  · exact hW h
  · exact hab (hPb a (Pb.fst_mem_support_of_mem_edges h)).2
  · exact hb.acyclic a (Relation.TransGen.tail' (hPp a (Pp.fst_mem_support_of_mem_edges h)).2 hpa)

variable {u : V} {c : G.undirected.Walk u u}

/-- The neighbours of a vertex along a cycle are neighbours in the undirected graph. -/
private theorem p8g_adj_of_mem_neighborSet {v w : V} (hw : w ∈ c.toSubgraph.neighborSet v) :
    G.undirected.Adj v w := c.toSubgraph.adj_sub hw

/-- **A hybrid node of a cycle is a sink**: both its neighbours along the cycle are its parents. -/
private theorem p8g_isSink_of_isHybrid (hb : G.IsBinary) (h1 : G.IsLevel1) (hc : c.IsCycle) {v : V}
    (hv : v ∈ c.support) (hh : G.IsHybrid v) : ∀ w ∈ c.toSubgraph.neighborSet v, G.Adj w v := by
  have := hb.finite
  intro w hw
  by_contra hwv
  have hvw : G.Adj v w :=
    (hb.undirected_adj_iff.1 (p8g_adj_of_mem_neighborSet hw)).resolve_right hwv
  obtain ⟨p, q, hpq, hpar⟩ := indeg_eq_two_iff.1 hh.1
  have hp : G.Adj p v := (hpar p).2 (Or.inl rfl)
  have hq : G.Adj q v := (hpar q).2 (Or.inr rfl)
  have hwp : w ≠ p := fun h => hb.not_adj_of_adj hvw (h ▸ hp)
  have hwq : w ≠ q := fun h => hb.not_adj_of_adj hvw (h ▸ hq)
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  -- one of the parents, `x`, is not a neighbour along the cycle; `y` is the other
  obtain ⟨x, y, hx, hy, hxy, hxc⟩ : ∃ x y, G.Adj x v ∧ G.Adj y v ∧ x ≠ y ∧
      x ∉ c.toSubgraph.neighborSet v := by
    by_cases hpc : p ∈ c.toSubgraph.neighborSet v
    · by_cases hqc : q ∈ c.toSubgraph.neighborSet v
      · exfalso
        have h3 : ({w, p, q} : Set V) ⊆ c.toSubgraph.neighborSet v := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · exact hw
          · exact hpc
          · exact hqc
        have := Set.ncard_le_ncard h3 (Walk.finite_neighborSet_toSubgraph c)
        rw [Set.ncard_insert_of_notMem (by simp [hwp, hwq]), Set.ncard_pair hpq, h2] at this
        omega
      · exact ⟨q, p, hq, hp, hpq.symm, hqc⟩
    · exact ⟨p, q, hp, hq, hpq, hpc⟩
  have hbr := hb.isBridge_of_isCycle h1 hc hv (hb.undirected_adj_iff.2 (Or.inr hx))
    (fun h => hxc (Walk.adj_toSubgraph_iff_mem_edges.2 h))
  refine p8g_not_isBridge hb hx (b := y) (fun h => hb.acyclic v (Relation.TransGen.tail' h hy))
    (hb.undirected_adj_iff.2 (Or.inr hy)).toWalk ?_ hbr
  intro h
  rw [Walk.edges_cons, Walk.edges_nil, List.mem_singleton, Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact hxy h
  · exact hb.not_adj_self y (by rwa [h] at hy)

/-- **A cycle has at most one source**: a vertex both of whose neighbours along the cycle are its
children. -/
private theorem p8g_source_unique (hb : G.IsBinary) (h1 : G.IsLevel1) (hc : c.IsCycle) {s₁ s₂ : V}
    (h₁ : s₁ ∈ c.support) (h₁' : ∀ w ∈ c.toSubgraph.neighborSet s₁, G.Adj s₁ w)
    (h₂ : s₂ ∈ c.support) (h₂' : ∀ w ∈ c.toSubgraph.neighborSet s₂, G.Adj s₂ w) :
    s₁ = s₂ := by
  classical
  have := hb.finite
  obtain ⟨r, hr, -⟩ := hb.exists_isRoot
  -- a source `a` that is not an ancestor of another source `b` is impossible
  have key : ∀ a b, a ∈ c.support → (∀ w ∈ c.toSubgraph.neighborSet a, G.Adj a w) →
      b ∈ c.support → ¬ Relation.ReflTransGen G.Adj a b → False := by
    intro a b ha ha' hb' hab
    have har : a ≠ r := fun h => hab (h ▸ hb.reflTransGen_root hr.1 b)
    obtain ⟨p, hp⟩ : ∃ p, G.Adj p a := by
      by_contra! h
      exact har ((hb.existsUnique_indeg_eq_zero).unique (indeg_eq_zero_iff.2 h) hr.1)
    have hpc : s(a, p) ∉ c.edges := fun h =>
      hb.not_adj_of_adj hp (ha' p (Walk.adj_toSubgraph_iff_mem_edges.2 h))
    have hbr := hb.isBridge_of_isCycle h1 hc ha (hb.undirected_adj_iff.2 (Or.inr hp)) hpc
    let W : G.undirected.Walk a b := (c.dropUntil a ha).append (c.takeUntil b hb')
    refine p8g_not_isBridge hb hp hab W (fun h => hpc ?_) hbr
    simp only [W, Walk.edges_append, List.mem_append] at h
    rcases h with h | h
    · exact c.edges_dropUntil_subset_edges ha h
    · exact c.edges_takeUntil_subset_edges hb' h
  by_contra hne
  by_cases h12 : Relation.ReflTransGen G.Adj s₁ s₂
  · refine key s₂ s₁ h₂ h₂' h₁ fun h21 => ?_
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h12 with h | h
    · exact hne h.symm
    · exact hb.acyclic s₁ (h.trans_left h21)
  · exact key s₁ s₂ h₁ h₁' h₂ h12

/-- A vertex of a cycle with no descendant on the cycle is a sink with two parents: a hybrid
node. -/
private theorem p8g_exists_isHybrid (hb : G.IsBinary) (hc : c.IsCycle) :
    ∃ h, h ∈ c.support ∧ G.IsHybrid h := by
  have := hb.finite
  let R : V → V → Prop := fun w v => Relation.TransGen G.Adj v w
  have : IsTrans V R := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  have : Std.Irrefl R := ⟨hb.acyclic⟩
  obtain ⟨h, hh, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl R).has_min
    {v | v ∈ c.support} ⟨u, c.start_mem_support⟩
  refine ⟨h, hh, ?_⟩
  -- the neighbours of `h` along the cycle are its parents
  have hpar : ∀ w ∈ c.toSubgraph.neighborSet h, G.Adj w h := by
    intro w hw
    refine (hb.undirected_adj_iff.1 (p8g_adj_of_mem_neighborSet hw)).resolve_left fun hhw => ?_
    exact hmin w (Walk.mem_support_of_adj_toSubgraph (Subgraph.adj_symm _ hw)) (.single hhw)
  obtain ⟨a, b, hab, hnb⟩ := Set.ncard_eq_two.1 (hc.ncard_neighborSet_toSubgraph_eq_two hh)
  have ha : G.Adj a h := hpar a (by rw [hnb]; simp)
  have hb' : G.Adj b h := hpar b (by rw [hnb]; simp)
  have h2 : 2 ≤ G.indeg h := by
    rw [indeg, ← Set.ncard_pair hab]
    exact Set.ncard_le_ncard (fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb') (Set.toFinite _)
  rcases hb.degrees h with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | hhy
  · omega
  · omega
  · omega
  · exact hhy

/-- **Two sinks give two sources**: between two sinks, each arc of the cycle has a highest
vertex, which is a source. -/
private theorem p8g_two_sources (hb : G.IsBinary) (hc : c.IsCycle) {h₁ h₂ : V}
    (hne : h₁ ≠ h₂) (hh₁ : h₁ ∈ c.support) (hs₁ : ∀ w ∈ c.toSubgraph.neighborSet h₁, G.Adj w h₁)
    (hh₂ : h₂ ∈ c.support) (hs₂ : ∀ w ∈ c.toSubgraph.neighborSet h₂, G.Adj w h₂) :
    ∃ s₁ s₂, s₁ ≠ s₂ ∧ s₁ ∈ c.support ∧ (∀ w ∈ c.toSubgraph.neighborSet s₁, G.Adj s₁ w) ∧
      s₂ ∈ c.support ∧ ∀ w ∈ c.toSubgraph.neighborSet s₂, G.Adj s₂ w := by
  classical
  have := hb.finite
  -- the cycle from `h₁`
  set d := c.rotate h₁ hh₁ with hd
  have hdc : d.IsCycle := hc.rotate hh₁
  have hdt : d.toSubgraph = c.toSubgraph := Walk.toSubgraph_rotate c hh₁
  have hds : ∀ v, v ∈ d.support ↔ v ∈ c.support := fun v => by
    rw [hd]
    exact c.mem_support_rotate_iff h₁ hh₁
  rw [← hdt] at hs₁ hs₂ ⊢
  simp only [← hds] at hh₂ ⊢
  have hk := hdc.three_le_length
  set k := d.length
  obtain ⟨j, hj, hjk⟩ := Walk.mem_support_iff_exists_getVert.1 hh₂
  have hj0 : j ≠ 0 := fun h => hne (by rw [← hj, h, Walk.getVert_zero])
  have hjk' : j ≠ k := fun h => hne (by rw [← hj, h, Walk.getVert_length])
  -- the neighbours along the cycle of the vertices at the positions `0` and `j`
  have hn0 := hdc.neighborSet_toSubgraph_endpoint
  have hnj := hdc.neighborSet_toSubgraph_internal hj0 (by omega : j < k)
  rw [hj] at hnj
  have hpar0 : G.Adj (d.getVert 1) (d.getVert 0) := by
    rw [Walk.getVert_zero]
    exact hs₁ _ (by rw [hn0]; exact Set.mem_insert _ _)
  have hparK : G.Adj (d.getVert (k - 1)) (d.getVert k) := by
    rw [Walk.getVert_length]
    exact hs₁ _ (by rw [hn0]; exact Set.mem_insert_of_mem _ rfl)
  have hparj₁ : G.Adj (d.getVert (j - 1)) (d.getVert j) := by
    rw [hj]
    exact hs₂ _ (by rw [hnj]; exact Set.mem_insert _ _)
  have hparj₂ : G.Adj (d.getVert (j + 1)) (d.getVert j) := by
    rw [hj]
    exact hs₂ _ (by rw [hnj]; exact Set.mem_insert_of_mem _ rfl)
  -- the highest vertex of an arc between two sinks is a source
  let R : ℕ → ℕ → Prop := fun i i' => Relation.TransGen G.Adj (d.getVert i) (d.getVert i')
  have hR : WellFounded R := by
    have : IsTrans V (Relation.TransGen G.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    have : Std.Irrefl (Relation.TransGen G.Adj) := ⟨hb.acyclic⟩
    exact InvImage.wf d.getVert (Finite.wellFounded_of_trans_of_irrefl _)
  have hsource : ∀ lo hi, lo < hi → hi ≤ k → G.Adj (d.getVert (lo + 1)) (d.getVert lo) →
      G.Adj (d.getVert (hi - 1)) (d.getVert hi) → ∃ i, lo < i ∧ i < hi ∧
        ∀ w ∈ d.toSubgraph.neighborSet (d.getVert i), G.Adj (d.getVert i) w := by
    intro lo hi hlh hhk hlo hhi
    obtain ⟨i, ⟨hi1, hi2⟩, hmin⟩ := hR.has_min {i | lo ≤ i ∧ i ≤ hi} ⟨lo, le_rfl, hlh.le⟩
    have hilo : i ≠ lo := fun h => hmin (lo + 1) ⟨by omega, by omega⟩ (by
      rw [h]
      exact .single hlo)
    have hihi : i ≠ hi := fun h => hmin (hi - 1) ⟨by omega, by omega⟩ (by
      rw [h]
      exact .single hhi)
    refine ⟨i, by omega, by omega, fun w hw => ?_⟩
    have hU := p8g_adj_of_mem_neighborSet hw
    rw [hdc.neighborSet_toSubgraph_internal (i := i) (by omega) (by omega)] at hw
    refine (hb.undirected_adj_iff.1 hU).resolve_right fun hwi => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hmin (i - 1) ⟨by omega, by omega⟩ (.single hwi)
    · exact hmin (i + 1) ⟨by omega, by omega⟩ (.single hwi)
  obtain ⟨i₁, hi₁, hi₁', hsrc₁⟩ := hsource 0 j (by omega) (by omega) hpar0 hparj₁
  obtain ⟨i₂, hi₂, hi₂', hsrc₂⟩ := hsource j k (by omega) le_rfl hparj₂ hparK
  refine ⟨d.getVert i₁, d.getVert i₂, fun h => ?_, d.getVert_mem_support _, hsrc₁,
    d.getVert_mem_support _, hsrc₂⟩
  have := hdc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) h
  omega

/-- **In a level-1 network, every cycle contains exactly one hybrid node.** -/
theorem IsBinary.existsUnique_isHybrid (hb : G.IsBinary) (h1 : G.IsLevel1) (hc : c.IsCycle) :
    ∃! h, h ∈ c.support ∧ G.IsHybrid h := by
  obtain ⟨h, hh, hhy⟩ := p8g_exists_isHybrid hb hc
  refine ⟨h, ⟨hh, hhy⟩, fun h' ⟨hh', hhy'⟩ => ?_⟩
  by_contra hne
  obtain ⟨s₁, s₂, hs, hs₁, hs₁', hs₂, hs₂'⟩ := p8g_two_sources hb hc hne hh'
    (p8g_isSink_of_isHybrid hb h1 hc hh' hhy') hh (p8g_isSink_of_isHybrid hb h1 hc hh hhy)
  exact hs (p8g_source_unique hb h1 hc hs₁ hs₁' hs₂ hs₂')

/-- **One hybrid node per cycle**, for a network. -/
theorem IsNetwork.existsUnique_isHybrid (hG : G.IsNetwork) (hc : c.IsCycle) :
    ∃! h, h ∈ c.support ∧ G.IsHybrid h :=
  hG.binary.existsUnique_isHybrid hG.level1 hc

end MetricDigraph

end Phylogenetics
