module

public import Phylogenetics.Graph.Invariant
/-!
# The invariant for a node of a side of a cycle

`Phylogenetics.SideGraph.isSide_node`: the graph of `Side.node ℓ b N S` has the invariant
`Phylogenetics.SideGraph.IsSide` when the graph of the network `N` hanging from the node has the
invariant `Phylogenetics.MetricDigraph.IsSubnet` and the graph of the rest `S` of the side has the
invariant `Phylogenetics.SideGraph.IsSide`. The pendant edge is a cut edge; the edge from the node
to the rest of the side is an edge of the cycle. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph MetricDigraph

variable {X : Type u}

namespace SideGraph

variable {A B : Type} {ℓ b : ℝ} {G : MetricDigraph A X} {r : A} {S : SideGraph B X}

/-- The edges into a vertex of the pendant subnetwork. -/
theorem node_adj_pendant_iff (x : NodeVert A B) (a : A) :
    (node ℓ b G r S).graph.Adj x (.pendant a) ↔
      (x = .node ∧ a = r) ∨ ∃ u, x = .pendant u ∧ G.Adj u a := by
  cases x <;> simp [node]

/-- The edges into a vertex of the rest of the side. -/
theorem node_adj_rest_iff (x : NodeVert A B) (c : B) :
    (node ℓ b G r S).graph.Adj x (.rest c) ↔
      (x = .node ∧ S.first = some c) ∨ ∃ u, x = .rest u ∧ S.graph.Adj u c := by
  cases x <;> simp [node]

/-- No edge of the side enters its first node. -/
theorem node_not_adj_node (x : NodeVert A B) : ¬ (node ℓ b G r S).graph.Adj x .node := by
  cases x <;> simp [node]

/-- The undirected edges of the graph of a side. -/
theorem node_undirected_adj_iff {x y : NodeVert A B} :
    (node ℓ b G r S).graph.undirected.Adj x y ↔
      (x = .node ∧ y = .pendant r) ∨ (x = .pendant r ∧ y = .node) ∨
      (∃ c, S.first = some c ∧ ((x = .node ∧ y = .rest c) ∨ (x = .rest c ∧ y = .node))) ∨
      (∃ a a', x = .pendant a ∧ y = .pendant a' ∧ G.undirected.Adj a a') ∨
      (∃ c c', x = .rest c ∧ y = .rest c' ∧ S.graph.undirected.Adj c c') := by
  cases x <;> cases y <;> simp [undirected_adj, node, eq_comm]

/-- The in-degree of a vertex of the pendant subnetwork: one more at its root, for the pendant
edge. -/
theorem node_indeg_pendant [Finite A] [Finite B] (a : A) :
    (node ℓ b G r S).graph.indeg (.pendant a) = G.indeg a + optInd (some r) a := by
  rw [indeg, indeg, ← ncard_optInd_one (.node : NodeVert A B)]
  refine ncard_lift (ι := (NodeVert.pendant : A → NodeVert A B))
    (fun _ _ h => NodeVert.pendant.inj h) (fun a' => ?_) (fun x hx => ?_) (fun x hx a' => ?_)
  · simp [node]
  · cases x with
    | node => simp [node, eq_comm]
    | pendant a' => exact (hx a' rfl).elim
    | rest c => simp [node]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The in-degree of a vertex of the rest of the side: one more at its first node, for the edge
from the new node. -/
theorem node_indeg_rest [Finite A] [Finite B] (c : B) :
    (node ℓ b G r S).graph.indeg (.rest c) = S.graph.indeg c + optInd S.first c := by
  rw [indeg, indeg, ← ncard_optInd_one (.node : NodeVert A B)]
  refine ncard_lift (ι := (NodeVert.rest : B → NodeVert A B))
    (fun _ _ h => NodeVert.rest.inj h) (fun c' => ?_) (fun x hx => ?_) (fun x hx c' => ?_)
  · simp [node]
  · cases x with
    | node => simp [node]
    | pendant a => simp [node]
    | rest c' => exact (hx c' rfl).elim
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The out-degree of a vertex of the pendant subnetwork. -/
theorem node_outdeg_pendant [Finite A] [Finite B] (a : A) :
    (node ℓ b G r S).graph.outdeg (.pendant a) = G.outdeg a := by
  rw [outdeg, outdeg]
  refine ncard_lift_of_forall_notMem (ι := (NodeVert.pendant : A → NodeVert A B))
    (fun _ _ h => NodeVert.pendant.inj h) (fun a' => ?_) (fun x hx => ?_)
  · simp [node]
  · cases x with
    | node => simp [node]
    | pendant a' => exact (hx a' rfl).elim
    | rest c => simp [node]

/-- The out-degree of a vertex of the rest of the side. -/
theorem node_outdeg_rest [Finite A] [Finite B] (c : B) :
    (node ℓ b G r S).graph.outdeg (.rest c) = S.graph.outdeg c := by
  rw [outdeg, outdeg]
  refine ncard_lift_of_forall_notMem (ι := (NodeVert.rest : B → NodeVert A B))
    (fun _ _ h => NodeVert.rest.inj h) (fun c' => ?_) (fun x hx => ?_)
  · simp [node]
  · cases x with
    | node => simp [node]
    | pendant a => simp [node]
    | rest c' => exact (hx c' rfl).elim

/-- The node has two children, counting the edge to the hybrid node when it is the last node. -/
theorem node_outdeg_node (hS : S.first = none ↔ S.last = none) :
    (node ℓ b G r S).graph.outdeg .node + optInd (node ℓ b G r S).last .node = 2 := by
  rcases hf : S.first with _ | f
  · have hl : S.last = none := hS.1 hf
    have : {w | (node ℓ b G r S).graph.Adj .node w} = {.pendant r} := by
      ext w
      cases w <;> simp [node, hf]
    rw [outdeg, this, Set.ncard_singleton]
    simp [node, hl]
  · have hl : S.last ≠ none := fun h => by rw [hS.2 h] at hf; cases hf
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hl
    have : {w | (node ℓ b G r S).graph.Adj .node w} = {.pendant r, .rest f} := by
      ext w
      cases w <;> simp [node, hf, eq_comm]
    rw [outdeg, this, Set.ncard_pair (by simp)]
    simp [node, hl, optInd]

/-- The last node of the side: that of the rest, or the new node if the rest has no node. -/
theorem node_last : (node ℓ b G r S).last = some ((S.last.map .rest).getD .node) := rfl

/-- The new node is the first node of the side. -/
@[simp]
theorem node_optInd_first_node : optInd (node ℓ b G r S).first .node = 1 := by
  simp [node]

/-- A vertex of the pendant subnetwork is not the first node of the side. -/
@[simp]
theorem node_optInd_first_pendant (a : A) :
    optInd (node ℓ b G r S).first (.pendant a) = 0 := by
  simp [node, optInd]

/-- A vertex of the rest is not the first node of the side. -/
@[simp]
theorem node_optInd_first_rest (c : B) : optInd (node ℓ b G r S).first (.rest c) = 0 := by
  simp [node, optInd]

/-- A vertex of the rest is the last node of the side when it is the last node of the rest. -/
theorem node_optInd_last_rest (c : B) :
    optInd (node ℓ b G r S).last (.rest c) = optInd S.last c := by
  rw [node_last]
  rcases S.last with _ | l
  · simp [optInd]
  · unfold optInd
    by_cases h : l = c
    · subst h
      simp
    · rw [ite_eq_right (by simpa using h), ite_eq_right (by simpa using h)]

/-- A vertex of the pendant subnetwork is not the last node of the side. -/
theorem node_optInd_last_pendant (a : A) : optInd (node ℓ b G r S).last (.pendant a) = 0 := by
  rw [node_last]
  rcases S.last with _ | l
  · simp [optInd]
  · simp [optInd]

/-- The only undirected edge leaving the pendant subnetwork is the pendant edge. -/
theorem node_cut_pendant (x' y' : NodeVert A B) (hx' : x' ∈ Set.range (NodeVert.pendant : A → _))
    (hy' : y' ∉ Set.range (NodeVert.pendant : A → NodeVert A B))
    (h : (node ℓ b G r S).graph.undirected.Adj x' y') : s(x', y') = s(.node, .pendant r) := by
  obtain ⟨a, rfl⟩ := hx'
  rw [node_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h1, rfl⟩ | ⟨c, -, ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨a₁, a', h1, rfl, -⟩ |
    ⟨c, c', h, -⟩
  · cases h
  · rw [h1, Sym2.eq_swap]
  · cases h
  · cases h
  · exact (hy' (Set.mem_range_self a')).elim
  · cases h

/-- The pendant subnetwork is attached at its root only. -/
theorem node_attach_pendant (a : A) (y : NodeVert A B)
    (h : (node ℓ b G r S).graph.undirected.Adj (.pendant a) y)
    (hy : ∀ a', NodeVert.pendant a' ≠ y) : a ∈ ({r} : Set A) := by
  rw [node_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h1, -⟩ | ⟨c, -, ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨a₁, a', h1, rfl, -⟩ |
    ⟨c, c', h, -⟩
  · cases h
  · exact NodeVert.pendant.inj h1
  · cases h
  · cases h
  · exact (hy a' rfl).elim
  · cases h

/-- The rest of the side is attached at its first node only. -/
theorem node_attach_rest (c : B) (y : NodeVert A B)
    (h : (node ℓ b G r S).graph.undirected.Adj (.rest c) y)
    (hy : ∀ c', NodeVert.rest c' ≠ y) : c ∈ {c | S.first = some c} := by
  rw [node_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨c₁, hc₁, ⟨h, -⟩ | ⟨h1, -⟩⟩ | ⟨a, a', h, -⟩ |
    ⟨c₁, c', h1, rfl, -⟩
  · cases h
  · cases h
  · cases h
  · rw [Set.mem_ofPred_eq, NodeVert.rest.inj h1]
    exact hc₁
  · cases h
  · exact (hy c' rfl).elim

/-- The cycle edges of the graph of a side: the edge from the node to the rest of the side, and
those of the pendant subnetwork and of the rest; the pendant edge, and the cut edges of the
parts, are cut edges. -/
theorem node_cycles [Finite A] [Finite B] (hG : G.IsSubnet r) (hS : S.IsSide) :
    ∃ K : SimpleGraph (NodeVert A B),
      (∀ x, (K.neighborSet x).ncard + optInd (node ℓ b G r S).first x +
          optInd (node ℓ b G r S).last x = 0 ∨
        (K.neighborSet x).ncard + optInd (node ℓ b G r S).first x +
          optInd (node ℓ b G r S).last x = 2) ∧
      ∀ x y, (node ℓ b G r S).graph.undirected.Adj x y → ¬ K.Adj x y →
        ∃ T : Set (NodeVert A B), (∀ a, (node ℓ b G r S).first = some a → a ∉ T) ∧
          (∀ a, (node ℓ b G r S).last = some a → a ∉ T) ∧ (x ∈ T ↔ y ∉ T) ∧
          ∀ x' y', x' ∈ T → y' ∉ T → (node ℓ b G r S).graph.undirected.Adj x' y' →
            s(x', y') = s(x, y) := by
  obtain ⟨KG, hKG, hcutG⟩ := hG.cycles
  obtain ⟨KS, hKS, hcutS⟩ := hS.cycles
  let K : SimpleGraph (NodeVert A B) := SimpleGraph.fromRel fun x y => match x, y with
    | .node, .rest c => S.first = some c
    | .pendant a, .pendant a' => KG.Adj a a'
    | .rest c, .rest c' => KS.Adj c c'
    | _, _ => False
  have hKP : ∀ a y, K.Adj (.pendant a) y ↔ ∃ a', y = .pendant a' ∧ KG.Adj a a' := by
    intro a y
    cases y with
    | node => simp [K]
    | pendant a' =>
      simp only [K, SimpleGraph.fromRel_adj, ne_eq, NodeVert.pendant.injEq, exists_eq_left']
      exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
    | rest c => simp [K]
  have hKR : ∀ c y, K.Adj (.rest c) y ↔
      (y = .node ∧ S.first = some c) ∨ ∃ c', y = .rest c' ∧ KS.Adj c c' := by
    intro c y
    cases y with
    | node => simp [K]
    | pendant a => simp [K]
    | rest c' =>
      simp only [K, SimpleGraph.fromRel_adj, ne_eq, NodeVert.rest.injEq, reduceCtorEq,
        false_and, exists_eq_left', false_or]
      exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
  have hKN : ∀ y, K.Adj .node y ↔ ∃ c, y = .rest c ∧ S.first = some c := by
    intro y
    cases y <;> simp [K]
  have hUP := undirected_adj_lift (G := G) (H := (node ℓ b G r S).graph)
    (ι := NodeVert.pendant) (fun _ _ h => NodeVert.pendant.inj h) (fun _ _ => Iff.rfl)
  have hUR := undirected_adj_lift (G := S.graph) (H := (node ℓ b G r S).graph)
    (ι := NodeVert.rest) (fun _ _ h => NodeVert.rest.inj h) (fun _ _ => Iff.rfl)
  refine ⟨K, fun x => ?_, fun x y hxy hxyK => ?_⟩
  · cases x with
    | node =>
      right
      rw [node_optInd_first_node]
      rcases hf : S.first with _ | f
      · have hl := hS.first_eq_none_iff.1 hf
        have : K.neighborSet .node = ∅ := by
          ext y
          simp [hKN, hf]
        rw [this, Set.ncard_empty]
        simp [node, hl, optInd]
      · have hl : S.last ≠ none := fun h => by rw [hS.first_eq_none_iff.2 h] at hf; cases hf
        have : K.neighborSet .node = {.rest f} := by
          ext y
          simp [hKN, hf]
        rw [this, Set.ncard_singleton]
        obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hl
        simp [node, hl, optInd]
    | pendant a =>
      rw [node_optInd_first_pendant, node_optInd_last_pendant, add_zero, add_zero,
        ncard_lift_of_forall_notMem (ι := (NodeVert.pendant : A → NodeVert A B))
          (t := KG.neighborSet a) (fun _ _ h => NodeVert.pendant.inj h)
          (fun a' => by simp [hKP])
          (fun y hy => by
            simp only [SimpleGraph.mem_neighborSet, hKP, not_exists, not_and]
            exact fun a' h => (hy a' h.symm).elim)]
      exact hKG a
    | rest c =>
      rw [node_optInd_first_rest, node_optInd_last_rest, add_zero,
        ncard_lift (ι := (NodeVert.rest : B → NodeVert A B)) (t := KS.neighborSet c)
          (E := {y | y = .node ∧ S.first = some c}) (fun _ _ h => NodeVert.rest.inj h)
          (fun c' => by simp [hKR])
          (fun y hy => by
            cases y with
            | node => simp [hKR]
            | pendant a => simp [hKR]
            | rest c' => exact (hy c' rfl).elim)
          (fun y hy c' => by rw [hy.1]; simp),
        ncard_optInd_one]
      exact hKS c
  · rw [node_undirected_adj_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨a, a', rfl, rfl, hU⟩ | ⟨c, c', rfl, rfl, hU⟩
    · refine ⟨Set.range NodeVert.pendant, by simp [node], ?_, by simp, node_cut_pendant⟩
      rintro a ha ⟨a', rfl⟩
      rcases h : S.last with _ | l <;> simp [node, h] at ha
    · refine ⟨Set.range NodeVert.pendant, by simp [node], ?_, by simp,
        fun x' y' hx' hy' h => ?_⟩
      · rintro a ha ⟨a', rfl⟩
        rcases h : S.last with _ | l <;> simp [node, h] at ha
      · rw [node_cut_pendant x' y' hx' hy' h, Sym2.eq_swap]
    · exact (hxyK ((hKN _).2 ⟨c, rfl, hc⟩)).elim
    · exact (hxyK ((hKR c _).2 (Or.inl ⟨rfl, hc⟩))).elim
    · have hK' : ¬ KG.Adj a a' := fun h => hxyK ((hKP a _).2 ⟨a', rfl, h⟩)
      obtain ⟨SG, hrSG, hSG, hcG⟩ := hcutG a a' hU hK'
      refine ⟨NodeVert.pendant '' SG, by simp [node], ?_, ?_, crossing_lift
        (fun _ _ => hUP _ _) (P := {r}) node_attach_pendant
        (fun a ha h => hrSG (by rw [Set.mem_singleton_iff] at h; rwa [← h])) hcG⟩
      · rintro x hx ⟨a₁, -, rfl⟩
        rcases h : S.last with _ | l <;> simp [node, h] at hx
      · simp only [Set.mem_image, NodeVert.pendant.injEq, exists_eq_right]
        exact hSG
    · have hK' : ¬ KS.Adj c c' := fun h => hxyK ((hKR c _).2 (Or.inr ⟨c', rfl, h⟩))
      obtain ⟨TS, hfTS, hlTS, hTS, hcS⟩ := hcutS c c' hU hK'
      refine ⟨NodeVert.rest '' TS, by simp [node], ?_, ?_, crossing_lift
        (fun _ _ => hUR _ _) (P := {c | S.first = some c}) node_attach_rest
        (fun c hc h => hfTS c h hc) hcS⟩
      · rintro x hx ⟨c₁, hc₁, rfl⟩
        rcases h : S.last with _ | l
        · simp [node, h] at hx
        · simp only [node, h, Option.map_some, Option.getD_some, Option.some.injEq,
            NodeVert.rest.injEq] at hx
          exact hlTS l h (hx ▸ hc₁)
      · simp only [Set.mem_image, NodeVert.rest.injEq, exists_eq_right]
        exact hTS

/-- The graph of a side `Side.node ℓ b N S` has the invariant when the graph of the network `N`
hanging from its first node and the graph of the rest `S` have theirs, with distinct labels, and
its two new edges have positive lengths. -/
theorem isSide_node (hℓ : 0 < ℓ) (hb : 0 < b) (hG : G.IsSubnet r) (hS : S.IsSide)
    (hdisj : ∀ a c x, G.label a = some x → S.graph.label c = some x → False) :
    (node ℓ b G r S).IsSide := by
  have := hG.finite
  have := hS.finite
  have hr : G.indeg r = 0 := indeg_eq_zero_iff.2 hG.not_adj_root
  have hfirst : ∀ c, S.first = some c → S.graph.indeg c = 0 :=
    fun c hc => indeg_eq_zero_iff.2 (hS.not_adj_first c hc)
  -- the hybrid nodes are those of the parts
  have hhybP : ∀ a, (node ℓ b G r S).graph.IsHybrid (.pendant a) ↔ G.IsHybrid a := by
    intro a
    rw [IsHybrid, IsHybrid, node_indeg_pendant, node_outdeg_pendant]
    by_cases ha : a = r
    · subst ha
      simp [hr]
    · rw [optInd_some_of_ne (Ne.symm ha), add_zero]
  have hhybR : ∀ c, (node ℓ b G r S).graph.IsHybrid (.rest c) ↔ S.graph.IsHybrid c := by
    intro c
    rw [IsHybrid, IsHybrid, node_indeg_rest, node_outdeg_rest]
    by_cases hc : S.first = some c
    · rw [hfirst c hc, hc, optInd_some_self]
      simp
    · rw [optInd_of_ne hc, add_zero]
  have hhybN : ¬ (node ℓ b G r S).graph.IsHybrid .node := by
    rintro ⟨h, -⟩
    rw [indeg_eq_two_iff] at h
    obtain ⟨u, _, _, hu⟩ := h
    exact node_not_adj_node u ((hu u).2 (Or.inl rfl))
  have hneG : ∀ a, G.IsHybrid a → a ≠ r := fun a ha h => by rw [h, IsHybrid, hr] at ha; omega
  have hneS : ∀ c, S.graph.IsHybrid c → S.first ≠ some c :=
    fun c hc h => by rw [IsHybrid, hfirst c h] at hc; omega
  obtain ⟨fG, hfG⟩ := hG.height
  obtain ⟨fS, hfS⟩ := hS.height
  refine
    { finite := inferInstance
      height := ⟨fun | .node => 0 | .pendant a => fG a + 1 | .rest c => fS c + 1, ?_⟩
      first_eq_none_iff := by simp [node]
      not_adj_first := by
        intro x hx u
        simp only [node, Option.some.injEq] at hx
        subst hx
        exact node_not_adj_node u
      outdeg_last := ?_
      degrees := ?_
      topLen_pos := hℓ
      hybLen_pos := hS.hybLen_pos
      len_pos := ?_
      inh_mem_Ioo := ?_
      inh_add_inh := ?_
      isSome_label_iff := ?_
      label_injective := ?_
      cycles := node_cycles hG hS }
  · intro u v huv
    cases u <;> cases v <;> simp_all [node]
  · intro x hx
    rw [node_last] at hx
    rcases hl : S.last with _ | l
    · rw [hl] at hx
      simp only [Option.map_none, Option.getD_none, Option.some.injEq] at hx
      subst hx
      have h2 := node_outdeg_node (ℓ := ℓ) (b := b) (G := G) (r := r) hS.first_eq_none_iff
      rw [node_last, hl] at h2
      simp only [Option.map_none, Option.getD_none, optInd_some_self] at h2
      omega
    · rw [hl] at hx
      simp only [Option.map_some, Option.getD_some, Option.some.injEq] at hx
      subst hx
      rw [node_outdeg_rest]
      exact hS.outdeg_last l hl
  · intro x
    cases x with
    | node =>
      rw [node_optInd_first_node, node_outdeg_node hS.first_eq_none_iff]
      have : (node ℓ b G r S).graph.indeg .node = 0 :=
        indeg_eq_zero_iff.2 node_not_adj_node
      rw [this]
      simp [DegOK]
    | pendant a =>
      rw [node_optInd_first_pendant, node_optInd_last_pendant, add_zero, add_zero,
        node_indeg_pendant, node_outdeg_pendant]
      by_cases ha : a = r
      · subst ha
        rw [hr, optInd_some_self]
        rcases hG.outdeg_root with h | h <;> simp [DegOK, h]
      · rw [optInd_some_of_ne (Ne.symm ha), add_zero]
        exact hG.degrees a ha
    | rest c =>
      rw [node_optInd_first_rest, node_optInd_last_rest, add_zero,
        node_indeg_rest, node_outdeg_rest]
      exact hS.degrees c
  · intro u v huv
    cases u <;> cases v <;> simp_all [node, hG.len_pos, hS.len_pos, hS.topLen_pos]
  · intro u v huv hv
    cases v with
    | node => exact (hhybN hv).elim
    | pendant a =>
      rw [hhybP] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (node_adj_pendant_iff u a).1 huv
      · exact (hneG a hv h0).elim
      · exact hG.inh_mem_Ioo u a hu hv
    | rest c =>
      rw [hhybR] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (node_adj_rest_iff u c).1 huv
      · exact (hneS c hv h0).elim
      · exact hS.inh_mem_Ioo u c hu hv
  · intro u u' v huv hu'v huu' hv
    cases v with
    | node => exact (hhybN hv).elim
    | pendant a =>
      rw [hhybP] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (node_adj_pendant_iff u a).1 huv
      · exact (hneG a hv h0).elim
      obtain ⟨-, h0⟩ | ⟨u', rfl, hu'⟩ := (node_adj_pendant_iff u' a).1 hu'v
      · exact (hneG a hv h0).elim
      exact hG.inh_add_inh u u' a hu hu' (fun h => huu' (by rw [h])) hv
    | rest c =>
      rw [hhybR] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (node_adj_rest_iff u c).1 huv
      · exact (hneS c hv h0).elim
      obtain ⟨-, h0⟩ | ⟨u', rfl, hu'⟩ := (node_adj_rest_iff u' c).1 hu'v
      · exact (hneS c hv h0).elim
      exact hS.inh_add_inh u u' c hu hu' (fun h => huu' (by rw [h])) hv
  · intro x
    cases x with
    | node =>
      rw [node_outdeg_node hS.first_eq_none_iff]
      simp [node]
    | pendant a =>
      rw [node_optInd_last_pendant, add_zero, node_outdeg_pendant]
      exact hG.isSome_label_iff a
    | rest c =>
      rw [node_optInd_last_rest, node_outdeg_rest]
      exact hS.isSome_label_iff c
  · intro u v x hu hv
    cases u with
    | node => simp [node] at hu
    | pendant a =>
      cases v with
      | node => simp [node] at hv
      | pendant a' => exact congrArg _ (hG.label_injective a a' x hu hv)
      | rest c => exact (hdisj a c x hu hv).elim
    | rest c =>
      cases v with
      | node => simp [node] at hv
      | pendant a => exact (hdisj a c x hv hu).elim
      | rest c' => exact congrArg _ (hS.label_injective c c' x hu hv)

end SideGraph

end Phylogenetics
