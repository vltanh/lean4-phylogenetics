module

public import Phylogenetics.Graph.Defs
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
/-!
# Basic facts about the graphs of networks

Facts used both to show that the graph of a network term is a network
(`Phylogenetics.Graph.Sound`) and to describe a network by a term (`Phylogenetics.Graph.Complete`).

* Degrees from the sets of neighbours: `Phylogenetics.MetricDigraph.indeg_eq_two_iff` and its
  companions.
* Binary networks: no loops, no two opposite edges, the undirected adjacency, at most three
  neighbours (`Phylogenetics.MetricDigraph.IsBinary.ncard_neighborSet_le`), the root, and directed
  paths from the root to every vertex (`Phylogenetics.MetricDigraph.IsBinary.reflTransGen_root`),
  which are paths of the undirected graph
  (`Phylogenetics.MetricDigraph.IsBinary.exists_isPath_of_reflTransGen`).
* Isomorphisms: identity, inverse, composition, and the preserved degrees and kinds of vertices;
  the isomorphism of undirected graphs (`Phylogenetics.MetricDigraph.Iso.undirectedIso`).
* Bridges: an edge that is the only edge leaving a set of vertices is a bridge
  (`Phylogenetics.isBridge_of_forall_crossing`).
* A criterion for level-1 (`Phylogenetics.MetricDigraph.isLevel1_of_isCycles`): if the edges that
  are not bridges form a graph whose vertices have degree zero or two, no two cycles share an edge.
* Edges at a cycle (`Phylogenetics.MetricDigraph.IsBinary.isBridge_of_isCycle`): in a binary
  level-1 network, an edge at a vertex of a cycle that is not an edge of the cycle is a bridge. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v w w'

open SimpleGraph

/-! ### Bridges -/

/-- An edge `s(a, b)` that is the only edge between a set `S ∋ a` of vertices and its complement
`∌ b` is a bridge: every walk from `a` to `b` leaves `S` along it. -/
theorem isBridge_of_forall_crossing {V : Type u} {H : SimpleGraph V} {S : Set V} {a b : V}
    (ha : a ∈ S) (hb : b ∉ S) (h : ∀ x y, x ∈ S → y ∉ S → H.Adj x y → s(x, y) = s(a, b)) :
    H.IsBridge s(a, b) := by
  refine isBridge_iff_forall_walk_mem_edges.2 fun p => ?_
  obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart S ha hb
  rw [← h _ _ hd1 hd2 d.adj]
  exact List.mem_map_of_mem hd

/-- A set of vertices closed under adjacency contains every vertex reachable from one of its
vertices. -/
theorem mem_of_walk_of_closed {V : Type u} {K : SimpleGraph V} {S : Set V}
    (hS : ∀ x y, x ∈ S → K.Adj x y → y ∈ S) {a z : V} (p : K.Walk a z) (ha : a ∈ S) : z ∈ S := by
  induction p with
  | nil => exact ha
  | cons h _ ih => exact ih (hS _ _ ha h)

/-- **A criterion for level-1, for simple graphs.** If the edges of `H` that are not bridges lie
in a subgraph `K` whose vertices have degree zero or two (`K.IsCycles`), then two cycles of `H`
that share an edge have the same edges. -/
theorem edgeSet_eq_of_isCycles {V : Type u} [Finite V] {H K : SimpleGraph V} (hKc : K.IsCycles)
    (hbr : ∀ ⦃x y : V⦄, H.Adj x y → ¬ K.Adj x y → H.IsBridge s(x, y)) {u v : V}
    {c : H.Walk u u} {c' : H.Walk v v} (hc : c.IsCycle) (hc' : c'.IsCycle)
    (hcc' : (c.edgeSet ∩ c'.edgeSet).Nonempty) : c.edgeSet = c'.edgeSet := by
  classical
  have : K.LocallyFinite := fun _ => Fintype.ofFinite _
  -- the edges of a cycle are edges of `K`
  have hcK : ∀ {w} {c : H.Walk w w}, c.IsCycle → ∀ e ∈ c.edges, e ∈ K.edgeSet := by
    intro w c hc e he
    induction e using Sym2.ind with
    | h x y =>
      by_contra hK
      exact (hbr (c.adj_of_mem_edges he) hK).notMem_edges_of_isCycle hc he
  -- at a vertex of a cycle, the edges of `K` are the edges of the cycle
  have hloc : ∀ {w} {c : H.Walk w w} (hc : c.IsCycle), ∀ x ∈ c.support, ∀ y,
      K.Adj x y ↔ s(x, y) ∈ c.edges := by
    intro w c hc x hx y
    have hcK' := hc.transfer (hcK hc)
    rw [← (hcK'.adj_toSubgraph_iff_of_isCycles hKc (by simpa using hx) y),
      Walk.adj_toSubgraph_iff_mem_edges, Walk.edges_transfer]
  -- the edges of `c` are edges of `c'`, when they share an edge
  have hsub : ∀ {w w'} {c : H.Walk w w} {c' : H.Walk w' w'}, c.IsCycle → c'.IsCycle →
      (c.edgeSet ∩ c'.edgeSet).Nonempty → c.edgeSet ⊆ c'.edgeSet := by
    intro w w' c c' hc hc' ⟨e, he, he'⟩
    induction e using Sym2.ind with
    | h a b =>
      have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges he
      have ha' : a ∈ c'.support := c'.fst_mem_support_of_mem_edges he'
      -- the support of `c'` is closed under `K`, and contains that of `c`
      have hclosed : ∀ x y, x ∈ {z | z ∈ c'.support} → K.Adj x y → y ∈ {z | z ∈ c'.support} :=
        fun x y hx hxy => c'.snd_mem_support_of_mem_edges ((hloc hc' x hx y).1 hxy)
      have hsupp : ∀ z ∈ c.support, z ∈ c'.support := by
        intro z hz
        let cK := c.transfer K (hcK hc)
        have hza : a ∈ cK.support := by simpa [cK] using ha
        have hzz : z ∈ cK.support := by simpa [cK] using hz
        exact mem_of_walk_of_closed hclosed
          ((cK.dropUntil a hza).append (cK.takeUntil z hzz)) ha'
      intro e' he'
      induction e' using Sym2.ind with
      | h x y =>
        have hx : x ∈ c.support := c.fst_mem_support_of_mem_edges he'
        exact (hloc hc' x (hsupp x hx) y).1 (hcK hc _ he')
  exact (hsub hc hc' hcc').antisymm (hsub hc' hc (by rwa [Set.inter_comm]))

namespace MetricDigraph

variable {V : Type u} {W : Type w} {W' : Type w'} {X : Type v} {G : MetricDigraph V X}

/-! ### Degrees -/

/-- In-degree zero: no edge enters the vertex. -/
theorem indeg_eq_zero_iff [Finite V] {v : V} : G.indeg v = 0 ↔ ∀ u, ¬ G.Adj u v := by
  rw [indeg, Set.ncard_eq_zero]
  simp [Set.eq_empty_iff_forall_notMem]

/-- Out-degree zero: no edge leaves the vertex. -/
theorem outdeg_eq_zero_iff [Finite V] {v : V} : G.outdeg v = 0 ↔ ∀ w, ¬ G.Adj v w := by
  rw [outdeg, Set.ncard_eq_zero]
  simp [Set.eq_empty_iff_forall_notMem]

/-- In-degree one: exactly one edge, from `u`, enters the vertex. -/
theorem indeg_eq_one_iff {v : V} : G.indeg v = 1 ↔ ∃ u, ∀ x, G.Adj x v ↔ x = u := by
  rw [indeg, Set.ncard_eq_one]
  simp [Set.ext_iff]

/-- Out-degree one: exactly one edge, to `w`, leaves the vertex. -/
theorem outdeg_eq_one_iff {v : V} : G.outdeg v = 1 ↔ ∃ w, ∀ x, G.Adj v x ↔ x = w := by
  rw [outdeg, Set.ncard_eq_one]
  simp [Set.ext_iff]

/-- In-degree two: exactly two edges, from distinct `u` and `u'`, enter the vertex. -/
theorem indeg_eq_two_iff {v : V} :
    G.indeg v = 2 ↔ ∃ u u', u ≠ u' ∧ ∀ x, G.Adj x v ↔ x = u ∨ x = u' := by
  rw [indeg, Set.ncard_eq_two]
  simp [Set.ext_iff]

/-- Out-degree two: exactly two edges, to distinct `w` and `w'`, leave the vertex. -/
theorem outdeg_eq_two_iff {v : V} :
    G.outdeg v = 2 ↔ ∃ w w', w ≠ w' ∧ ∀ x, G.Adj v x ↔ x = w ∨ x = w' := by
  rw [outdeg, Set.ncard_eq_two]
  simp [Set.ext_iff]

/-! ### Binary networks -/

/-- The undirected adjacency: an edge in one direction or the other, between distinct
vertices. -/
theorem undirected_adj {u v : V} : G.undirected.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ G.Adj v u) :=
  SimpleGraph.fromRel_adj _ _ _

namespace IsBinary

variable (hG : G.IsBinary)
include hG

/-- No edge is a loop. -/
theorem not_adj_self (v : V) : ¬ G.Adj v v := fun h => hG.acyclic v (.single h)

/-- No two edges join the same two vertices in opposite directions. -/
theorem not_adj_of_adj {u v : V} (h : G.Adj u v) : ¬ G.Adj v u :=
  fun h' => hG.acyclic u (.tail (.single h) h')

/-- The undirected adjacency of a binary network: an edge in one direction or the other. -/
theorem undirected_adj_iff {u v : V} : G.undirected.Adj u v ↔ G.Adj u v ∨ G.Adj v u := by
  rw [undirected_adj]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  exact h.elim (hG.not_adj_self u) (hG.not_adj_self u)

/-- An edge of a binary network is an edge of its undirected graph. -/
theorem undirected_adj_of_adj {u v : V} (h : G.Adj u v) : G.undirected.Adj u v :=
  hG.undirected_adj_iff.2 (Or.inl h)

/-- Every vertex has in-degree plus out-degree at most three. -/
theorem indeg_add_outdeg_le (v : V) : G.indeg v + G.outdeg v ≤ 3 := by
  rcases hG.degrees v with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Every vertex has at most three neighbours in the undirected graph. -/
theorem ncard_neighborSet_le (v : V) : (G.undirected.neighborSet v).ncard ≤ 3 := by
  have := hG.finite
  have hsub : G.undirected.neighborSet v ⊆ {w | G.Adj v w} ∪ {u | G.Adj u v} := by
    intro w hw
    rcases hG.undirected_adj_iff.1 hw with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc (G.undirected.neighborSet v).ncard
      ≤ ({w | G.Adj v w} ∪ {u | G.Adj u v}).ncard := Set.ncard_le_ncard hsub
    _ ≤ G.outdeg v + G.indeg v := Set.ncard_union_le _ _
    _ ≤ 3 := by have := hG.indeg_add_outdeg_le v; omega

/-- The root: the vertex of in-degree zero, of out-degree two. -/
theorem exists_isRoot : ∃ r, G.IsRoot r ∧ ∀ v, G.indeg v = 0 → v = r := by
  obtain ⟨r, hr, huniq⟩ := hG.existsUnique_indeg_eq_zero
  refine ⟨r, ?_, huniq⟩
  rcases hG.degrees r with h | h | h | h
  · exact h
  all_goals simp_all [IsLeaf, IsTreeNode, IsHybrid]

/-- Every vertex is reachable from the root by a directed path: going up from a vertex, the
parents end at a vertex of in-degree zero, the root. -/
theorem reflTransGen_root {r : V} (hr : G.indeg r = 0) (v : V) :
    Relation.ReflTransGen G.Adj r v := by
  have := hG.finite
  have : IsTrans V (Relation.TransGen G.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen G.Adj) := ⟨hG.acyclic⟩
  refine (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen G.Adj)).induction v ?_
  intro v ih
  by_cases hv : G.indeg v = 0
  · obtain ⟨_, _, huniq⟩ := hG.existsUnique_indeg_eq_zero
    rw [huniq v hv, huniq r hr]
  · obtain ⟨p, hp⟩ : ∃ p, G.Adj p v := by
      by_contra! h
      exact hv (indeg_eq_zero_iff.2 h)
    exact (ih p (.single hp)).tail hp

/-- A directed path from `u` to `v` is a path of the undirected graph whose darts follow the
edges, through vertices between `u` and `v`. -/
theorem exists_isPath_of_reflTransGen {u v : V} (h : Relation.ReflTransGen G.Adj u v) :
    ∃ p : G.undirected.Walk u v, p.IsPath ∧ (∀ d ∈ p.darts, G.Adj d.fst d.snd) ∧
      ∀ x ∈ p.support, Relation.ReflTransGen G.Adj u x ∧ Relation.ReflTransGen G.Adj x v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨.nil, .nil, by simp, fun x hx => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨.refl, .refl⟩
  | @head a b hab _ ih =>
    obtain ⟨p, hp, hd, hs⟩ := ih
    refine ⟨.cons (hG.undirected_adj_of_adj hab) p, ?_, ?_, ?_⟩
    · refine (Walk.cons_isPath_iff _ _).2 ⟨hp, fun ha => ?_⟩
      exact hG.acyclic a (Relation.TransGen.head' hab (hs a ha).1)
    · simp only [Walk.darts_cons, List.mem_cons]
      rintro d (rfl | hd')
      · exact hab
      · exact hd d hd'
    · simp only [Walk.support_cons, List.mem_cons]
      rintro x (rfl | hx)
      · exact ⟨.refl, .head hab (hs b p.start_mem_support).2⟩
      · exact ⟨.head hab (hs x hx).1, (hs x hx).2⟩

/-- **Edges at a cycle.** In a binary level-1 network, an edge `s(v, x)` at a vertex `v` of a
cycle `c` that is not an edge of `c` is a bridge. Otherwise it lies on a cycle `c'`, which leaves
`v` along a second edge; `v` has at most three neighbours, two of them along `c`, so that second
edge is an edge of `c`, and `c` and `c'` would share an edge without being the same cycle. -/
theorem isBridge_of_isCycle (h1 : G.IsLevel1) {u : V} {c : G.undirected.Walk u u}
    (hc : c.IsCycle) {v x : V} (hv : v ∈ c.support) (hvx : G.undirected.Adj v x)
    (hx : s(v, x) ∉ c.edges) : G.undirected.IsBridge s(v, x) := by
  have := hG.finite
  by_contra hnb
  rw [isBridge_iff_forall_cycle_notMem (by exact hvx)] at hnb
  simp only [not_forall, not_not, exists_prop] at hnb
  obtain ⟨w, c', hc', hvx'⟩ := hnb
  -- the second neighbour `y` of `v` along `c'`
  have hv' : v ∈ c'.support := c'.fst_mem_support_of_mem_edges hvx'
  obtain ⟨y, hy, hyx⟩ := (c'.toSubgraph.neighborSet v).exists_ne_of_one_lt_ncard
    (by rw [hc'.ncard_neighborSet_toSubgraph_eq_two hv']; omega) x
  have hvy' : s(v, y) ∈ c'.edges := Walk.adj_toSubgraph_iff_mem_edges.1 hy
  -- the two neighbours `a`, `b` of `v` along `c`
  obtain ⟨a, b, hab, hnc⟩ := Set.ncard_eq_two.1 (hc.ncard_neighborSet_toSubgraph_eq_two hv)
  have hmem : ∀ z, s(v, z) ∈ c.edges ↔ z = a ∨ z = b := by
    intro z
    rw [← Walk.adj_toSubgraph_iff_mem_edges, ← Subgraph.mem_neighborSet, hnc]
    simp
  have hxa : x ≠ a := fun h => hx ((hmem x).2 (Or.inl h))
  have hxb : x ≠ b := fun h => hx ((hmem x).2 (Or.inr h))
  -- `y` is `a` or `b`, as `v` has at most three neighbours
  have hya : y = a ∨ y = b := by
    by_contra! hy'
    have hadj : ∀ z, s(v, z) ∈ c.edges ∨ s(v, z) ∈ c'.edges → z ∈ G.undirected.neighborSet v :=
      fun z hz => hz.elim (c.adj_of_mem_edges) (c'.adj_of_mem_edges)
    have h4 : ({a, b, x, y} : Set V) ⊆ G.undirected.neighborSet v := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact hadj _ (Or.inl ((hmem _).2 (Or.inl rfl)))
      · exact hadj _ (Or.inl ((hmem _).2 (Or.inr rfl)))
      · exact hadj _ (Or.inr hvx')
      · exact hadj _ (Or.inr hvy')
    have hcard : ({a, b, x, y} : Set V).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hab, hxa.symm, hy'.1.symm]),
        Set.ncard_insert_of_notMem (by simp [hxb.symm, hy'.2.symm]),
        Set.ncard_pair hyx.symm]
    have := (Set.ncard_le_ncard h4).trans (hG.ncard_neighborSet_le v)
    omega
  have hshare : (c.edgeSet ∩ c'.edgeSet).Nonempty :=
    ⟨s(v, y), (hmem y).2 hya, hvy'⟩
  have hvx'' : s(v, x) ∈ c'.edgeSet := hvx'
  rw [← h1 c c' hc hc' hshare] at hvx''
  exact hx hvx''

end IsBinary

/-- **A criterion for level-1.** If the edges of the undirected graph of `G` that are not bridges
lie in a subgraph `K` whose vertices have degree zero or two, `G` is level-1. -/
theorem isLevel1_of_isCycles [Finite V] {K : SimpleGraph V} (hKc : K.IsCycles)
    (hbr : ∀ ⦃x y : V⦄, G.undirected.Adj x y → ¬ K.Adj x y → G.undirected.IsBridge s(x, y)) :
    G.IsLevel1 :=
  fun _ _ _ _ hc hc' hcc' => edgeSet_eq_of_isCycles hKc hbr hc hc' hcc'

/-! ### Isomorphisms -/

namespace Iso

variable {H : MetricDigraph W X} {K : MetricDigraph W' X}

/-- An isomorphism is a bijection of the vertices. -/
instance : EquivLike (G.Iso H) V W where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e f h _ := by
    cases e
    cases f
    congr
    exact Equiv.ext (congrFun h)

/-- The function of an isomorphism. -/
@[simp]
theorem toFun_eq_coe (e : G.Iso H) : e.toFun = e := rfl

/-- The bijection of an isomorphism, as a function. -/
@[simp]
theorem coe_toEquiv (e : G.Iso H) : ⇑e.toEquiv = e := rfl

/-- The edges are preserved in both directions. -/
@[simp]
theorem adj_apply (e : G.Iso H) {u v : V} : H.Adj (e u) (e v) ↔ G.Adj u v := e.adj_iff u v

/-- The in-degrees are preserved. -/
theorem indeg_eq (e : G.Iso H) (v : V) : H.indeg (e v) = G.indeg v := by
  have : {u | H.Adj u (e v)} = e.toEquiv '' {u | G.Adj u v} := by
    ext u
    obtain ⟨u, rfl⟩ := e.toEquiv.surjective u
    simp
  rw [indeg, indeg, this, Set.ncard_image_of_injective _ e.toEquiv.injective]

/-- The out-degrees are preserved. -/
theorem outdeg_eq (e : G.Iso H) (v : V) : H.outdeg (e v) = G.outdeg v := by
  have : {w | H.Adj (e v) w} = e.toEquiv '' {w | G.Adj v w} := by
    ext w
    obtain ⟨w, rfl⟩ := e.toEquiv.surjective w
    simp
  rw [outdeg, outdeg, this, Set.ncard_image_of_injective _ e.toEquiv.injective]

/-- Roots are mapped to roots. -/
theorem isRoot_iff (e : G.Iso H) (v : V) : H.IsRoot (e v) ↔ G.IsRoot v := by
  simp [IsRoot, e.indeg_eq, e.outdeg_eq]

/-- Leaves are mapped to leaves. -/
theorem isLeaf_iff (e : G.Iso H) (v : V) : H.IsLeaf (e v) ↔ G.IsLeaf v := by
  simp [IsLeaf, e.indeg_eq, e.outdeg_eq]

/-- Tree nodes are mapped to tree nodes. -/
theorem isTreeNode_iff (e : G.Iso H) (v : V) : H.IsTreeNode (e v) ↔ G.IsTreeNode v := by
  simp [IsTreeNode, e.indeg_eq, e.outdeg_eq]

/-- Hybrid nodes are mapped to hybrid nodes. -/
theorem isHybrid_iff (e : G.Iso H) (v : V) : H.IsHybrid (e v) ↔ G.IsHybrid v := by
  simp [IsHybrid, e.indeg_eq, e.outdeg_eq]

/-- The identity isomorphism. -/
protected def refl (G : MetricDigraph V X) : G.Iso G where
  toEquiv := Equiv.refl V
  adj_iff _ _ := Iff.rfl
  label_eq _ := rfl
  len_eq _ _ _ := rfl
  inh_eq _ _ _ _ := rfl

/-- The inverse of an isomorphism. -/
protected def symm (e : G.Iso H) : H.Iso G where
  toEquiv := e.toEquiv.symm
  adj_iff u v := by
    obtain ⟨u, rfl⟩ := e.toEquiv.surjective u
    obtain ⟨v, rfl⟩ := e.toEquiv.surjective v
    show G.Adj (e.toEquiv.symm (e.toEquiv u)) (e.toEquiv.symm (e.toEquiv v)) ↔
      H.Adj (e.toEquiv u) (e.toEquiv v)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (e.adj_iff u v).symm
  label_eq v := by
    obtain ⟨v, rfl⟩ := e.toEquiv.surjective v
    show G.label (e.toEquiv.symm (e.toEquiv v)) = H.label (e.toEquiv v)
    rw [Equiv.symm_apply_apply]
    exact (e.label_eq v).symm
  len_eq u v huv := by
    obtain ⟨u, rfl⟩ := e.toEquiv.surjective u
    obtain ⟨v, rfl⟩ := e.toEquiv.surjective v
    show G.len (e.toEquiv.symm (e.toEquiv u)) (e.toEquiv.symm (e.toEquiv v)) =
      H.len (e.toEquiv u) (e.toEquiv v)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (e.len_eq u v ((e.adj_iff u v).1 huv)).symm
  inh_eq u v huv hv := by
    obtain ⟨u, rfl⟩ := e.toEquiv.surjective u
    obtain ⟨v, rfl⟩ := e.toEquiv.surjective v
    show G.inh (e.toEquiv.symm (e.toEquiv u)) (e.toEquiv.symm (e.toEquiv v)) =
      H.inh (e.toEquiv u) (e.toEquiv v)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (e.inh_eq u v ((e.adj_iff u v).1 huv) ((e.isHybrid_iff v).1 hv)).symm

/-- The composition of two isomorphisms. -/
protected def trans (e : G.Iso H) (f : H.Iso K) : G.Iso K where
  toEquiv := e.toEquiv.trans f.toEquiv
  adj_iff u v := (f.adj_iff (e u) (e v)).trans (e.adj_iff u v)
  label_eq v := (f.label_eq (e v)).trans (e.label_eq v)
  len_eq u v huv := (f.len_eq (e u) (e v) ((e.adj_iff u v).2 huv)).trans (e.len_eq u v huv)
  inh_eq u v huv hv := (f.inh_eq (e u) (e v) ((e.adj_iff u v).2 huv)
    ((e.isHybrid_iff v).2 hv)).trans (e.inh_eq u v huv hv)

/-- The identity isomorphism fixes every vertex. -/
@[simp]
theorem refl_apply (v : V) : Iso.refl G v = v := rfl

/-- The inverse undoes an isomorphism. -/
@[simp]
theorem symm_apply_apply (e : G.Iso H) (v : V) : e.symm (e v) = v := e.toEquiv.symm_apply_apply v

/-- An isomorphism undoes its inverse. -/
@[simp]
theorem apply_symm_apply (e : G.Iso H) (w : W) : e (e.symm w) = w := e.toEquiv.apply_symm_apply w

/-- The composition applies the first isomorphism, then the second. -/
@[simp]
theorem trans_apply (e : G.Iso H) (f : H.Iso K) (v : V) : e.trans f v = f (e v) := rfl

/-- An isomorphism of metric digraphs is an isomorphism of their undirected graphs. -/
def undirectedIso (e : G.Iso H) : G.undirected ≃g H.undirected where
  toEquiv := e.toEquiv
  map_rel_iff' {u v} := by
    simp only [coe_toEquiv, undirected_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq, adj_apply]

/-- The isomorphism of the undirected graphs maps each vertex as the isomorphism does. -/
@[simp]
theorem undirectedIso_apply (e : G.Iso H) (v : V) : e.undirectedIso v = e v := rfl

end Iso

end MetricDigraph

end Phylogenetics
