module

public import Phylogenetics.Graph.Basic
public import Phylogenetics.Graph.OfNet
/-!
# The invariant of the graphs of network terms

The graph of a well-formed network term is a network (`Phylogenetics.Graph.Sound`). The proof
follows the term: the facts below hold for the graph of a leaf, and pass from the graphs of the
parts to the graph of a tree node, of a node of a side, and of a cycle.

* `Phylogenetics.MetricDigraph.IsSubnet G r`: the facts for the graph `G` of a network term with
  root `r` (possibly a single leaf): a height that grows along the edges (so no directed cycle), the
  degrees, the metric, the labels, and, for level-1, a graph `K` of cycle edges in which every
  vertex has degree zero or two, every other edge being the only edge leaving a set of vertices
  without the root.
* `Phylogenetics.SideGraph.IsSide S`: the same facts for the graph of a side of a cycle, counting
  the edges of its first node from the top node and of its last node to the hybrid node.
* `Phylogenetics.MetricDigraph.IsSubnet.isNetwork`: a graph with these facts whose root has
  out-degree two is a network (`Phylogenetics.MetricDigraph.IsNetwork`); level-1 follows from the
  criterion `Phylogenetics.MetricDigraph.isLevel1_of_isCycles`. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph

/-! ### Counting -/

open Classical in
/-- `1` if `o` is `some a`, `0` otherwise: the edge that the vertex `a` of a side has to the top
node of its cycle (`o` the first node of the side) or to its hybrid node (`o` its last node). -/
def optInd {A : Type*} (o : Option A) (a : A) : ℕ := if o = some a then 1 else 0

/-- `optInd none a = 0`. -/
@[simp]
theorem optInd_none {A : Type*} (a : A) : optInd none a = 0 := by
  simp [optInd]

/-- `optInd (some a) a = 1`. -/
@[simp]
theorem optInd_some_self {A : Type*} (a : A) : optInd (some a) a = 1 := by
  simp [optInd]

/-- `optInd (some b) a = 0` for `b ≠ a`. -/
theorem optInd_some_of_ne {A : Type*} {a b : A} (h : b ≠ a) : optInd (some b) a = 0 := by
  simp [optInd, h]

/-- `optInd o a = 0` unless `o = some a`. -/
theorem optInd_of_ne {A : Type*} {o : Option A} {a : A} (h : o ≠ some a) : optInd o a = 0 := by
  simp [optInd, h]

/-- `optInd o a` is `0` or `1`. -/
theorem optInd_le_one {A : Type*} (o : Option A) (a : A) : optInd o a ≤ 1 := by
  unfold optInd
  split_ifs <;> omega

/-- The degrees of a vertex other than the root of a binary network: a leaf `(1, 0)`, a tree node
`(1, 2)` or a hybrid node `(2, 1)`. -/
def DegOK (i o : ℕ) : Prop := (i = 1 ∧ o = 0) ∨ (i = 1 ∧ o = 2) ∨ (i = 2 ∧ o = 1)

/-- The number of elements of a set `s`, the image of `t` by an injective map together with a
set `E` outside the image. -/
theorem ncard_lift {A B : Type*} [Finite B] {ι : A → B} (hι : Function.Injective ι) {s : Set B}
    {t : Set A} {E : Set B} (h1 : ∀ a, ι a ∈ s ↔ a ∈ t) (h2 : ∀ x, (∀ a, ι a ≠ x) → (x ∈ s ↔ x ∈ E))
    (h3 : ∀ x ∈ E, ∀ a, ι a ≠ x) : s.ncard = t.ncard + E.ncard := by
  have hs : s = ι '' t ∪ E := by
    ext x
    by_cases hx : ∃ a, ι a = x
    · obtain ⟨a, rfl⟩ := hx
      simp only [Set.mem_union, Set.mem_image, hι.eq_iff, exists_eq_right, h1]
      exact ⟨Or.inl, fun h => h.elim id fun h' => (h3 _ h' a rfl).elim⟩
    · simp only [not_exists] at hx
      rw [h2 x hx]
      simp only [Set.mem_union, Set.mem_image]
      exact ⟨Or.inr, fun h => h.elim (fun ⟨a, _, ha⟩ => (hx a ha).elim) id⟩
  have hdisj : Disjoint (ι '' t) E := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, _, rfl⟩ hE
    exact h3 _ hE a rfl
  rw [hs, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hι]

/-- The number of elements of a set `s`, the image of `t` by an injective map. -/
theorem ncard_lift_of_forall_notMem {A B : Type*} [Finite B] {ι : A → B}
    (hι : Function.Injective ι) {s : Set B} {t : Set A} (h1 : ∀ a, ι a ∈ s ↔ a ∈ t)
    (h2 : ∀ x, (∀ a, ι a ≠ x) → x ∉ s) : s.ncard = t.ncard := by
  have := ncard_lift hι h1 (E := ∅) (fun x hx => by simp [h2 x hx])
    (fun _ hx => (Set.notMem_empty _ hx).elim)
  rwa [Set.ncard_empty, add_zero] at this

/-- The set of the vertices `p` if `o = some a` and `q` if `o' = some a`, for distinct `p` and
`q`. -/
theorem ncard_optInd {A B : Type*} {p q : B} (hpq : p ≠ q) (o o' : Option A) (a : A) :
    {x | (x = p ∧ o = some a) ∨ (x = q ∧ o' = some a)}.ncard = optInd o a + optInd o' a := by
  by_cases h₁ : o = some a <;> by_cases h₂ : o' = some a
  · have : {x | (x = p ∧ o = some a) ∨ (x = q ∧ o' = some a)} = {p, q} := by
      ext x
      simp [h₁, h₂]
    rw [this, Set.ncard_pair hpq]
    simp [optInd, h₁, h₂]
  · have : {x | (x = p ∧ o = some a) ∨ (x = q ∧ o' = some a)} = {p} := by
      ext x
      simp [h₁, h₂]
    rw [this, Set.ncard_singleton]
    simp [optInd, h₁, h₂]
  · have : {x | (x = p ∧ o = some a) ∨ (x = q ∧ o' = some a)} = {q} := by
      ext x
      simp [h₁, h₂]
    rw [this, Set.ncard_singleton]
    simp [optInd, h₁, h₂]
  · have : {x | (x = p ∧ o = some a) ∨ (x = q ∧ o' = some a)} = ∅ := by
      ext x
      simp [h₁, h₂]
    rw [this, Set.ncard_empty]
    simp [optInd, h₁, h₂]

/-- The set of the vertex `p` if `o = some a`. -/
theorem ncard_optInd_one {A B : Type*} (p : B) (o : Option A) (a : A) :
    {x | x = p ∧ o = some a}.ncard = optInd o a := by
  by_cases h : o = some a
  · have : {x | x = p ∧ o = some a} = {p} := by
      ext x
      simp [h]
    rw [this, Set.ncard_singleton]
    simp [optInd, h]
  · have : {x | x = p ∧ o = some a} = ∅ := by
      ext x
      simp [h]
    rw [this, Set.ncard_empty]
    simp [optInd, h]

/-- An edge that is the only edge leaving the set `T` stays the only edge leaving its image, by a
map onto the vertices of a graph whose edges between images are the images of edges, when the
other edges at images leave from points `P` outside `T`. -/
theorem crossing_lift {A B : Type*} {UA : SimpleGraph A} {UB : SimpleGraph B} {ι : A → B}
    (hadj : ∀ a a', UB.Adj (ι a) (ι a') ↔ UA.Adj a a') {P : Set A}
    (hP : ∀ a y, UB.Adj (ι a) y → (∀ a', ι a' ≠ y) → a ∈ P) {T : Set A} (hT : ∀ a ∈ T, a ∉ P)
    {x y : A} (hcross : ∀ x' y', x' ∈ T → y' ∉ T → UA.Adj x' y' → s(x', y') = s(x, y)) :
    ∀ x' y', x' ∈ ι '' T → y' ∉ ι '' T → UB.Adj x' y' → s(x', y') = s(ι x, ι y) := by
  rintro _ y' ⟨a, ha, rfl⟩ hy' hadj'
  by_cases hy : ∃ a', ι a' = y'
  · obtain ⟨a', rfl⟩ := hy
    have ha' : a' ∉ T := fun h => hy' ⟨a', h, rfl⟩
    exact congrArg (Sym2.map ι) (hcross a a' ha ha' ((hadj a a').1 hadj'))
  · simp only [not_exists] at hy
    exact (hT a ha (hP a y' hadj' hy)).elim

namespace MetricDigraph

variable {X : Type u}

/-- A height that grows along the edges excludes directed cycles. -/
theorem not_transGen_of_height {A : Type*} {G : MetricDigraph A X} {f : A → ℕ}
    (hf : ∀ u v, G.Adj u v → f u < f v) (v : A) : ¬ Relation.TransGen G.Adj v v := by
  have : ∀ u w, Relation.TransGen G.Adj u w → f u < f w := by
    intro u w h
    induction h with
    | single h => exact hf _ _ h
    | tail _ h ih => exact ih.trans (hf _ _ h)
  exact fun h => lt_irrefl _ (this v v h)

/-- The undirected edges between images, by an injective map whose edges between images are the
images of edges. -/
theorem undirected_adj_lift {A B : Type*} {G : MetricDigraph A X} {H : MetricDigraph B X}
    {ι : A → B} (hι : Function.Injective ι) (hadj : ∀ a a', H.Adj (ι a) (ι a') ↔ G.Adj a a')
    (a a' : A) : H.undirected.Adj (ι a) (ι a') ↔ G.undirected.Adj a a' := by
  simp only [undirected_adj, hadj, ne_eq, hι.eq_iff]

end MetricDigraph

/-! ### Finiteness of the vertex types -/

/-- A tree node with finitely many vertices below it has finitely many vertices. -/
instance {A B : Type} [Finite A] [Finite B] : Finite (TreeVert A B) := by
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  infer_instance

/-- A side with finitely many vertices has finitely many vertices after a new node. -/
instance {A B : Type} [Finite A] [Finite B] : Finite (NodeVert A B) := by
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  infer_instance

/-- A cycle with finitely many vertices in its sides and below it has finitely many vertices. -/
instance {A B C : Type} [Finite A] [Finite B] [Finite C] : Finite (CycleVert A B C) := by
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  have := Fintype.ofFinite C
  infer_instance

/-! ### The invariants -/

variable {X : Type u}

/-- The facts that the graph `G` of a well-formed network term with root `r` has (a single leaf
included), in the form in which they pass from subnetworks to networks
(`Phylogenetics.Net.isSubnet_toGraph`). The edges of the cycles form a graph `K` whose vertices have
degree zero or two; every other edge is the only edge leaving a set of vertices without the
root. -/
structure MetricDigraph.IsSubnet {A : Type*} (G : MetricDigraph A X) (r : A) : Prop where
  /-- The graph is finite. -/
  finite : Finite A
  /-- A height grows along the edges. -/
  height : ∃ f : A → ℕ, ∀ u v, G.Adj u v → f u < f v
  /-- No edge enters the root. -/
  not_adj_root : ∀ u, ¬ G.Adj u r
  /-- The root is a leaf or has two children. -/
  outdeg_root : G.outdeg r = 0 ∨ G.outdeg r = 2
  /-- The other vertices are leaves, tree nodes and hybrid nodes. -/
  degrees : ∀ v, v ≠ r → DegOK (G.indeg v) (G.outdeg v)
  /-- The edges have positive lengths. -/
  len_pos : ∀ u v, G.Adj u v → 0 < G.len u v
  /-- The hybrid edges have inheritance probabilities in `(0, 1)`. -/
  inh_mem_Ioo : ∀ u v, G.Adj u v → G.IsHybrid v → G.inh u v ∈ Set.Ioo 0 1
  /-- The inheritance probabilities of the two hybrid edges of a hybrid node add to one. -/
  inh_add_inh : ∀ u u' v, G.Adj u v → G.Adj u' v → u ≠ u' → G.IsHybrid v →
    G.inh u v + G.inh u' v = 1
  /-- Exactly the vertices without children carry a label. -/
  isSome_label_iff : ∀ v, (G.label v).isSome ↔ G.outdeg v = 0
  /-- Distinct vertices carry distinct labels. -/
  label_injective : ∀ u v x, G.label u = some x → G.label v = some x → u = v
  /-- The cycle edges, and the cuts of the other edges. -/
  cycles : ∃ K : SimpleGraph A,
    (∀ v, (K.neighborSet v).ncard = 0 ∨ (K.neighborSet v).ncard = 2) ∧
    ∀ x y, G.undirected.Adj x y → ¬ K.Adj x y → ∃ S : Set A, r ∉ S ∧ (x ∈ S ↔ y ∉ S) ∧
      ∀ x' y', x' ∈ S → y' ∉ S → G.undirected.Adj x' y' → s(x', y') = s(x, y)

/-- The facts that the graph `S` of a side of a cycle of a well-formed network term has, counting
the edge from the top node of the cycle to its first node and the edge from its last node to the
hybrid node (`Phylogenetics.Side.isSide_toGraph`). -/
structure SideGraph.IsSide {A : Type} (S : SideGraph A X) : Prop where
  /-- The graph is finite. -/
  finite : Finite A
  /-- A height grows along the edges. -/
  height : ∃ f : A → ℕ, ∀ u v, S.graph.Adj u v → f u < f v
  /-- The side has a first node exactly when it has a last node. -/
  first_eq_none_iff : S.first = none ↔ S.last = none
  /-- No edge of the side enters its first node. -/
  not_adj_first : ∀ a, S.first = some a → ∀ u, ¬ S.graph.Adj u a
  /-- The last node has one child in the side (its pendant subnetwork). -/
  outdeg_last : ∀ a, S.last = some a → S.graph.outdeg a = 1
  /-- With the edges to the top and hybrid nodes, the vertices are leaves, tree nodes and hybrid
  nodes. -/
  degrees : ∀ a, DegOK (S.graph.indeg a + optInd S.first a) (S.graph.outdeg a + optInd S.last a)
  /-- The edge from the top node has positive length. -/
  topLen_pos : 0 < S.topLen
  /-- The hybrid edge has positive length. -/
  hybLen_pos : 0 < S.hybLen
  /-- The edges have positive lengths. -/
  len_pos : ∀ u v, S.graph.Adj u v → 0 < S.graph.len u v
  /-- The hybrid edges have inheritance probabilities in `(0, 1)`. -/
  inh_mem_Ioo : ∀ u v, S.graph.Adj u v → S.graph.IsHybrid v → S.graph.inh u v ∈ Set.Ioo 0 1
  /-- The inheritance probabilities of the two hybrid edges of a hybrid node add to one. -/
  inh_add_inh : ∀ u u' v, S.graph.Adj u v → S.graph.Adj u' v → u ≠ u' → S.graph.IsHybrid v →
    S.graph.inh u v + S.graph.inh u' v = 1
  /-- Exactly the vertices without children carry a label. -/
  isSome_label_iff : ∀ a, (S.graph.label a).isSome ↔ S.graph.outdeg a + optInd S.last a = 0
  /-- Distinct vertices carry distinct labels. -/
  label_injective : ∀ u v x, S.graph.label u = some x → S.graph.label v = some x → u = v
  /-- The cycle edges, and the cuts of the other edges. -/
  cycles : ∃ K : SimpleGraph A,
    (∀ a, (K.neighborSet a).ncard + optInd S.first a + optInd S.last a = 0 ∨
      (K.neighborSet a).ncard + optInd S.first a + optInd S.last a = 2) ∧
    ∀ x y, S.graph.undirected.Adj x y → ¬ K.Adj x y → ∃ T : Set A,
      (∀ a, S.first = some a → a ∉ T) ∧ (∀ a, S.last = some a → a ∉ T) ∧ (x ∈ T ↔ y ∉ T) ∧
      ∀ x' y', x' ∈ T → y' ∉ T → S.graph.undirected.Adj x' y' → s(x', y') = s(x, y)

/-! ### From the invariant to a network -/

namespace MetricDigraph

/-- A graph with the invariant whose root has two children is a network. -/
theorem IsSubnet.isNetwork {A : Type*} {G : MetricDigraph A X} {r : A} (h : G.IsSubnet r)
    (hr : G.outdeg r = 2) : G.IsNetwork := by
  have := h.finite
  have hin : G.indeg r = 0 := indeg_eq_zero_iff.2 h.not_adj_root
  have hne : ∀ v, G.indeg v = 0 → v = r := by
    intro v hv
    by_contra hvr
    rcases h.degrees v hvr with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hbin : G.IsBinary :=
    { finite := h.finite
      acyclic := by
        obtain ⟨f, hf⟩ := h.height
        exact not_transGen_of_height hf
      existsUnique_indeg_eq_zero := ⟨r, hin, hne⟩
      degrees := by
        intro v
        by_cases hv : v = r
        · subst hv
          exact Or.inl ⟨hin, hr⟩
        · rcases h.degrees v hv with h' | h' | h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr h')) }
  obtain ⟨K, hK, hcut⟩ := h.cycles
  refine ⟨hbin, ?_, ⟨h.len_pos, h.inh_mem_Ioo, h.inh_add_inh⟩, ⟨?_, h.label_injective⟩⟩
  · refine isLevel1_of_isCycles (K := K) ?_ ?_
    · intro v hv
      rcases hK v with h0 | h2
      · exact absurd h0 (Set.ncard_pos (Set.toFinite _) |>.2 hv).ne'
      · exact h2
    · intro x y hxy hK'
      obtain ⟨S, -, hS, hcross⟩ := hcut x y hxy hK'
      by_cases hx : x ∈ S
      · exact isBridge_of_forall_crossing hx (hS.1 hx) hcross
      · have hy : y ∈ S := by by_contra hy; exact hx (hS.2 hy)
        rw [Sym2.eq_swap]
        refine isBridge_of_forall_crossing hy hx fun x' y' hx' hy' hadj => ?_
        rw [hcross x' y' hx' hy' hadj, Sym2.eq_swap]
  · intro v
    rw [h.isSome_label_iff v, IsLeaf]
    by_cases hv : v = r
    · subst hv
      simp [hr]
    · rcases h.degrees v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

end MetricDigraph

/-! ### A leaf and a side without nodes -/

/-- The graph of a leaf has the invariant. -/
theorem MetricDigraph.isSubnet_leaf (x : X) : (MetricDigraph.leaf x).IsSubnet () where
  finite := inferInstance
  height := ⟨fun _ => 0, fun _ _ h => h.elim⟩
  not_adj_root _ h := h
  outdeg_root := Or.inl (MetricDigraph.outdeg_eq_zero_iff.2 fun _ h => h)
  degrees v hv := (hv rfl).elim
  len_pos _ _ h := h.elim
  inh_mem_Ioo _ _ h := h.elim
  inh_add_inh _ _ _ h := h.elim
  isSome_label_iff _ := by
    simp only [MetricDigraph.leaf, Option.isSome_some, true_iff]
    exact MetricDigraph.outdeg_eq_zero_iff.2 fun _ h => h
  label_injective _ _ _ _ _ := rfl
  cycles := ⟨⊥, fun _ => Or.inl (by simp), fun _ _ h => by
    simp [MetricDigraph.leaf] at h⟩

/-- The graph of a side without nodes, a single hybrid edge of positive length, has the
invariant. -/
theorem SideGraph.isSide_hyb {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (SideGraph.hyb ℓ : SideGraph Empty X).IsSide where
  finite := inferInstance
  height := ⟨fun _ => 0, fun u => u.elim⟩
  first_eq_none_iff := by simp [SideGraph.hyb]
  not_adj_first a := a.elim
  outdeg_last a := a.elim
  degrees a := a.elim
  topLen_pos := hℓ
  hybLen_pos := hℓ
  len_pos u := u.elim
  inh_mem_Ioo u := u.elim
  inh_add_inh u := u.elim
  isSome_label_iff a := a.elim
  label_injective u := u.elim
  cycles := ⟨⊥, fun a => a.elim, fun x => x.elim⟩

end Phylogenetics
