module

public import Phylogenetics.Graph.Basic
/-!
# Descendants, subnetworks and cut edges in a binary network

Tools for `Phylogenetics.Graph.Complete`, which describes a rooted binary metric level-1 network by
a network term, going down from its root.

* The descendants `Phylogenetics.MetricDigraph.desc G v` of a vertex `v` (the vertices reachable
  from `v` along directed edges), and their decomposition along the children of `v`
  (`Phylogenetics.MetricDigraph.mem_desc_iff`).
* Subnetworks: `Phylogenetics.MetricDigraph.EntersOnly G a b` says that the edge `(a, b)` is the
  only edge entering the descendants of `b` from outside them;
  `Phylogenetics.MetricDigraph.IsSubnetRoot G v`, that the descendants of `v` form a subnetwork
  rooted at `v`. In a binary network, below a cut edge (a bridge of the undirected graph) `(a, b)`,
  the descendants of `b` are entered only through `(a, b)`
  (`Phylogenetics.MetricDigraph.IsBinary.entersOnly_of_isBridge`).
* Directed walks: along a walk whose darts are edges of `G`, the successor and the predecessor of
  a vertex (`Phylogenetics.MetricDigraph.exists_adj_mem_edges_of_ne_end` and
  `Phylogenetics.MetricDigraph.exists_adj_mem_edges_of_ne_start`).
* Cycles: a vertex of a cycle has exactly two neighbours along it
  (`Phylogenetics.eq_or_eq_of_mem_edges_of_isCycle`).
-/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v

open SimpleGraph

/-- A vertex of a cycle has exactly two neighbours along the cycle: if `s(x, a)` and `s(x, b)` are
edges of the cycle `c` with `a ≠ b`, every edge `s(x, y)` of `c` has `y = a` or `y = b`. -/
theorem eq_or_eq_of_mem_edges_of_isCycle {W : Type*} {H : SimpleGraph W} {w : W}
    {c : H.Walk w w} (hc : c.IsCycle) {x a b y : W} (ha : s(x, a) ∈ c.edges)
    (hb : s(x, b) ∈ c.edges) (hab : a ≠ b) (hy : s(x, y) ∈ c.edges) : y = a ∨ y = b := by
  have hx : x ∈ c.support := c.fst_mem_support_of_mem_edges ha
  obtain ⟨p, q, -, hpq⟩ := Set.ncard_eq_two.1 (hc.ncard_neighborSet_toSubgraph_eq_two hx)
  have hmem : ∀ z, s(x, z) ∈ c.edges → z = p ∨ z = q := by
    intro z hz
    have : z ∈ c.toSubgraph.neighborSet x := Walk.adj_toSubgraph_iff_mem_edges.2 hz
    rw [hpq] at this
    simpa using this
  rcases hmem a ha with rfl | rfl <;> rcases hmem b hb with rfl | rfl <;>
    rcases hmem y hy with rfl | rfl <;> simp_all

namespace MetricDigraph

variable {V : Type u} {X : Type v} {G : MetricDigraph V X}

/-! ### Descendants -/

/-- The descendants of `v`: the vertices reachable from `v` along directed edges, `v`
included. -/
def desc (G : MetricDigraph V X) (v : V) : Set V := {w | Relation.ReflTransGen G.Adj v w}

/-- The descendants of `v` are the vertices reachable from `v` along directed edges. -/
theorem mem_desc {v w : V} : w ∈ G.desc v ↔ Relation.ReflTransGen G.Adj v w := Iff.rfl

/-- A vertex is one of its descendants. -/
theorem self_mem_desc (v : V) : v ∈ G.desc v := Relation.ReflTransGen.refl

/-- A child is a descendant. -/
theorem mem_desc_of_adj {v w : V} (h : G.Adj v w) : w ∈ G.desc v :=
  Relation.ReflTransGen.single h

/-- A descendant of a descendant is a descendant. -/
theorem mem_desc_trans {u v w : V} (h₁ : v ∈ G.desc u) (h₂ : w ∈ G.desc v) : w ∈ G.desc u :=
  Relation.ReflTransGen.trans h₁ h₂

/-- The descendants of a descendant of `u` are descendants of `u`. -/
theorem desc_subset {u v : V} (h : v ∈ G.desc u) : G.desc v ⊆ G.desc u :=
  fun _ hw => mem_desc_trans h hw

/-- A child of a descendant is a descendant. -/
theorem mem_desc_of_mem_of_adj {u v w : V} (hv : v ∈ G.desc u) (h : G.Adj v w) :
    w ∈ G.desc u :=
  Relation.ReflTransGen.tail hv h

/-- The descendants of `v` are `v` and the descendants of its children. -/
theorem mem_desc_iff {v w : V} : w ∈ G.desc v ↔ w = v ∨ ∃ x, G.Adj v x ∧ w ∈ G.desc x := by
  rw [mem_desc, Relation.ReflTransGen.cases_head_iff]
  simp only [mem_desc, eq_comm]

/-- The descendants of a vertex whose children are `c₁` and `c₂`. -/
theorem mem_desc_iff_of_adj_iff {v c₁ c₂ w : V} (hc : ∀ x, G.Adj v x ↔ x = c₁ ∨ x = c₂) :
    w ∈ G.desc v ↔ w = v ∨ w ∈ G.desc c₁ ∨ w ∈ G.desc c₂ := by
  rw [mem_desc_iff]
  simp only [hc]
  constructor
  · rintro (h | ⟨x, rfl | rfl, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨c₁, Or.inl rfl, h⟩
    · exact Or.inr ⟨c₂, Or.inr rfl, h⟩

/-- The descendants of a vertex whose only child is `c`. -/
theorem mem_desc_iff_of_adj_iff_eq {v c w : V} (hc : ∀ x, G.Adj v x ↔ x = c) :
    w ∈ G.desc v ↔ w = v ∨ w ∈ G.desc c := by
  rw [mem_desc_iff]
  simp only [hc]
  constructor
  · rintro (h | ⟨x, rfl, hx⟩)
    · exact Or.inl h
    · exact Or.inr hx
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨c, rfl, h⟩

/-- A vertex without children is its only descendant. -/
theorem mem_desc_iff_of_forall_not_adj {v w : V} (hc : ∀ x, ¬ G.Adj v x) :
    w ∈ G.desc v ↔ w = v := by
  rw [mem_desc_iff]
  simp [hc]

/-! ### Subnetworks -/

/-- The edge `(a, b)` is the only edge that enters the descendants of `b` from outside them: the
parents of a descendant `w` of `b` are descendants of `b`, except `a` when `w = b`. -/
def EntersOnly (G : MetricDigraph V X) (a b : V) : Prop :=
  ∀ w ∈ G.desc b, ∀ x, G.Adj x w → x ∈ G.desc b ∨ (x = a ∧ w = b)

/-- The descendants of `v` form a subnetwork rooted at `v`: `v` has out-degree zero or two, and
the parents of the descendants of `v` other than `v` are descendants of `v`. -/
structure IsSubnetRoot (G : MetricDigraph V X) (v : V) : Prop where
  /-- The vertex `v` is a leaf, a tree node or the root. -/
  outdeg : G.outdeg v = 0 ∨ G.outdeg v = 2
  /-- The descendants of `v` other than `v` have their parents among the descendants of `v`. -/
  closed : ∀ w ∈ G.desc v, w ≠ v → ∀ x, G.Adj x w → x ∈ G.desc v

/-- A path from outside the descendants of `b` into them passes through `a`, when the
descendants of `b` are entered only through the edge `(a, b)`. -/
theorem EntersOnly.reflTransGen {a b : V} (he : G.EntersOnly a b) {y w : V} (hy : y ∉ G.desc b)
    (hyw : Relation.ReflTransGen G.Adj y w) (hw : w ∈ G.desc b) :
    Relation.ReflTransGen G.Adj y a := by
  induction hyw with
  | refl => exact absurd hw hy
  | @tail s t hys hst ih =>
    rcases he t hw s hst with h | ⟨h, -⟩
    · exact ih h
    · exact h ▸ hys

/-- A vertex of in-degree one is not a hybrid node. -/
theorem not_isHybrid_of_indeg_eq_one {b : V} (h : G.indeg b = 1) : ¬ G.IsHybrid b :=
  fun hb => by have := hb.1; omega

/-- A hybrid node carries no label, in a labelled network. -/
theorem IsLabelled.label_eq_none_of_isHybrid (hl : G.IsLabelled) {v : V} (h : G.IsHybrid v) :
    G.label v = none := by
  rw [← Option.not_isSome_iff_eq_none, hl.isSome_label_iff]
  intro hv
  have := hv.1
  have := h.1
  omega

namespace IsBinary

variable (hG : G.IsBinary)
include hG

/-- No edge enters a vertex from one of its descendants. -/
theorem not_adj_of_mem_desc {v w : V} (hw : w ∈ G.desc v) : ¬ G.Adj w v :=
  fun h => hG.acyclic v (Relation.TransGen.tail' hw h)

/-- A vertex is not a descendant of its children. -/
theorem notMem_desc_of_adj {v w : V} (h : G.Adj v w) : v ∉ G.desc w :=
  fun hw => hG.acyclic v (Relation.TransGen.head' h hw)

/-- Two vertices that are descendants of each other are equal. -/
theorem eq_of_mem_desc_of_mem_desc {v w : V} (h₁ : w ∈ G.desc v) (h₂ : v ∈ G.desc w) :
    w = v := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h₁ with h | h
  · exact h
  · exact absurd (h.trans_left h₂) (hG.acyclic v)

/-- The two ends of an edge are distinct. -/
theorem ne_of_adj {v w : V} (h : G.Adj v w) : v ≠ w := by
  rintro rfl
  exact hG.not_adj_self v h

/-- A descendant other than `v` has fewer descendants than `v`. -/
theorem ncard_desc_lt {v w : V} (hw : w ∈ G.desc v) (hne : w ≠ v) :
    (G.desc w).ncard < (G.desc v).ncard := by
  have := hG.finite
  refine Set.ncard_lt_ncard ⟨desc_subset hw, fun hsub => hne ?_⟩
  exact hG.eq_of_mem_desc_of_mem_desc hw (hsub (self_mem_desc v))

/-- When the descendants of `b` are entered only through `(a, b)`, `a` is the only parent of
`b`. -/
theorem adj_iff_of_entersOnly {a b : V} (he : G.EntersOnly a b) (hab : G.Adj a b) (x : V) :
    G.Adj x b ↔ x = a := by
  refine ⟨fun hx => ?_, fun h => h ▸ hab⟩
  rcases he b (self_mem_desc b) x hx with h | ⟨h, -⟩
  · exact absurd hx (hG.not_adj_of_mem_desc h)
  · exact h

/-- When the descendants of `b` are entered only through `(a, b)`, `b` has in-degree one. -/
theorem indeg_eq_one_of_entersOnly {a b : V} (he : G.EntersOnly a b) (hab : G.Adj a b) :
    G.indeg b = 1 :=
  indeg_eq_one_iff.2 ⟨a, hG.adj_iff_of_entersOnly he hab⟩

/-- A vertex of in-degree one has out-degree zero or two: it is a leaf or a tree node. -/
theorem outdeg_of_indeg_eq_one {b : V} (h : G.indeg b = 1) : G.outdeg b = 0 ∨ G.outdeg b = 2 := by
  rcases hG.degrees b with hb | hb | hb | hb
  · have := hb.1; omega
  · exact Or.inl hb.2
  · exact Or.inr hb.2
  · have := hb.1; omega

/-- A vertex whose descendants are entered only through the edge `(a, b)` roots a
subnetwork. -/
theorem isSubnetRoot_of_entersOnly {a b : V} (he : G.EntersOnly a b) (hab : G.Adj a b) :
    G.IsSubnetRoot b where
  outdeg := hG.outdeg_of_indeg_eq_one (hG.indeg_eq_one_of_entersOnly he hab)
  closed w hw hwb x hx := by
    rcases he w hw x hx with h | ⟨-, h⟩
    · exact h
    · exact absurd h hwb

/-- A vertex with a child carries no label, in a labelled network. -/
theorem label_eq_none_of_adj (hl : G.IsLabelled) {v w : V} (h : G.Adj v w) : G.label v = none := by
  have := hG.finite
  rw [← Option.not_isSome_iff_eq_none, hl.isSome_label_iff]
  intro hv
  exact (outdeg_eq_zero_iff.1 hv.2) w h

/-- **Below a cut edge.** In a binary network, if `(a, b)` is an edge and a bridge of the
undirected graph, the descendants of `b` are entered only through `(a, b)`: an edge `(x, w)` into
a descendant `w` of `b` from outside would give a walk from `a` to `b` avoiding `(a, b)`, through
the root, `x` and `w`. -/
theorem entersOnly_of_isBridge {a b : V} (hab : G.Adj a b)
    (hbr : G.undirected.IsBridge s(a, b)) : G.EntersOnly a b := by
  intro w hw x hxw
  by_contra hcon
  rw [not_or, not_and] at hcon
  obtain ⟨hx, hxa⟩ := hcon
  have ha : a ∉ G.desc b := hG.notMem_desc_of_adj hab
  -- the edges of a directed path towards a vertex outside `desc b` are not `s(a, b)`
  have hR1 : ∀ y z, Relation.ReflTransGen G.Adj y z → z ∉ G.desc b →
      (G.undirected.deleteEdges {s(a, b)}).Reachable y z := by
    intro y z hyz
    induction hyz with
    | refl => exact fun _ => Reachable.refl _
    | @tail s t _ hst ih =>
      intro ht
      have hs : s ∉ G.desc b := fun hs => ht (mem_desc_of_mem_of_adj hs hst)
      refine (ih hs).trans (Adj.reachable ?_)
      rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      refine ⟨hG.undirected_adj_of_adj hst, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ht (by rw [h]; exact self_mem_desc b)
      · exact hs (by rw [h]; exact self_mem_desc b)
  -- the edges of a directed path inside `desc b` are not `s(a, b)`
  have hR2 : ∀ z, Relation.ReflTransGen G.Adj b z →
      (G.undirected.deleteEdges {s(a, b)}).Reachable b z := by
    intro z hbz
    induction hbz with
    | refl => exact Reachable.refl _
    | @tail s t hbs hst ih =>
      refine ih.trans (Adj.reachable ?_)
      have ht : t ∈ G.desc b := mem_desc_of_mem_of_adj hbs hst
      rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      refine ⟨hG.undirected_adj_of_adj hst, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact ha (h ▸ hbs)
      · exact ha (h ▸ ht)
  obtain ⟨r, hr, -⟩ := hG.exists_isRoot
  have hra := hR1 r a (hG.reflTransGen_root hr.1 a) ha
  have hrx := hR1 r x (hG.reflTransGen_root hr.1 x) hx
  have hxw' : (G.undirected.deleteEdges {s(a, b)}).Reachable x w := by
    refine Adj.reachable ?_
    rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    refine ⟨hG.undirected_adj_of_adj hxw, ?_⟩
    rintro (⟨h₁, h₂⟩ | ⟨h, -⟩)
    · exact hxa h₁ h₂
    · exact hx (by rw [h]; exact self_mem_desc b)
  exact (isBridge_iff.1 hbr) (hra.symm.trans (hrx.trans (hxw'.trans (hR2 w hw).symm)))

end IsBinary

/-! ### Directed walks -/

/-- Along a walk whose darts are edges of `G`, a vertex `x` other than the end has a successor: an
edge `(x, y)` of `G` such that `s(x, y)` is an edge of the walk. -/
theorem exists_adj_mem_edges_of_ne_end {u w : V} (p : G.undirected.Walk u w)
    (hp : ∀ d ∈ p.darts, G.Adj d.fst d.snd) {x : V} (hx : x ∈ p.support) (hxw : x ≠ w) :
    ∃ y, G.Adj x y ∧ s(x, y) ∈ p.edges := by
  induction p with
  | nil =>
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hxw
  | @cons a b c hab q ih =>
    rw [Walk.support_cons, List.mem_cons] at hx
    rw [Walk.darts_cons] at hp
    rcases hx with rfl | hx
    · exact ⟨b, hp _ List.mem_cons_self, by simp⟩
    · obtain ⟨y, hy, hy'⟩ := ih (fun d hd => hp d (List.mem_cons_of_mem _ hd)) hx hxw
      exact ⟨y, hy, by simp [hy']⟩

/-- Along a walk whose darts are edges of `G`, a vertex `x` other than the start has a
predecessor: an edge `(y, x)` of `G` such that `s(y, x)` is an edge of the walk. -/
theorem exists_adj_mem_edges_of_ne_start {u w : V} (p : G.undirected.Walk u w)
    (hp : ∀ d ∈ p.darts, G.Adj d.fst d.snd) {x : V} (hx : x ∈ p.support) (hxu : x ≠ u) :
    ∃ y, G.Adj y x ∧ s(y, x) ∈ p.edges := by
  induction p with
  | nil =>
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hxu
  | @cons a b c hab q ih =>
    rw [Walk.support_cons, List.mem_cons] at hx
    rw [Walk.darts_cons] at hp
    rcases hx with rfl | hx
    · exact absurd rfl hxu
    · by_cases hxb : x = b
      · subst hxb
        exact ⟨a, hp _ List.mem_cons_self, by simp⟩
      · obtain ⟨y, hy, hy'⟩ := ih (fun d hd => hp d (List.mem_cons_of_mem _ hd)) hx hxb
        exact ⟨y, hy, by simp [hy']⟩

end MetricDigraph

end Phylogenetics
