module

public import Phylogenetics.Network.Level1.Digraph.Invariant
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
/-!
# The invariant for a cycle

`Phylogenetics.MetricDigraph.isSubnet_cycle`: the graph of `Net.cycle γ S₁ S₂ ℓ N` has the invariant
`Phylogenetics.MetricDigraph.IsSubnet` when the graphs of its sides have the invariant
`Phylogenetics.SideGraph.IsSide`, the graph of `N` has the invariant, and the two sides do not both
lack nodes. The cycle edges are those of the parts together with the edges at the top node and at
the hybrid node; the edge below the hybrid node is a cut edge. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph

variable {X : Type u}

namespace MetricDigraph

variable {A B C : Type} {γ ℓ : ℝ} {S₁ : SideGraph A X} {S₂ : SideGraph B X}
  {G : MetricDigraph C X} {r : C}

/-! ### The edges -/

/-- No edge enters the top node of a cycle. -/
theorem cycle_not_adj_top (x : CycleVert A B C) : ¬ (cycle γ S₁ S₂ ℓ G r).Adj x .top := by
  cases x <;> simp [cycle]

/-- The edges into a vertex of the first side. -/
theorem cycle_adj_side₁_iff (x : CycleVert A B C) (a : A) :
    (cycle γ S₁ S₂ ℓ G r).Adj x (.side₁ a) ↔
      (x = .top ∧ S₁.first = some a) ∨ ∃ u, x = .side₁ u ∧ S₁.graph.Adj u a := by
  cases x <;> simp [cycle]

/-- The edges into a vertex of the second side. -/
theorem cycle_adj_side₂_iff (x : CycleVert A B C) (b : B) :
    (cycle γ S₁ S₂ ℓ G r).Adj x (.side₂ b) ↔
      (x = .top ∧ S₂.first = some b) ∨ ∃ u, x = .side₂ u ∧ S₂.graph.Adj u b := by
  cases x <;> simp [cycle]

/-- The edges into a vertex of the network below the hybrid node. -/
theorem cycle_adj_below_iff (x : CycleVert A B C) (c : C) :
    (cycle γ S₁ S₂ ℓ G r).Adj x (.below c) ↔
      (x = .hyb ∧ c = r) ∨ ∃ u, x = .below u ∧ G.Adj u c := by
  cases x <;> simp [cycle]

/-- The edges into the hybrid node: the two hybrid edges. -/
theorem cycle_adj_hyb_iff (x : CycleVert A B C) :
    (cycle γ S₁ S₂ ℓ G r).Adj x .hyb ↔
      (x = .top ∧ (S₁.first = none ∨ S₂.first = none)) ∨
      (∃ a, x = .side₁ a ∧ S₁.last = some a) ∨ ∃ b, x = .side₂ b ∧ S₂.last = some b := by
  cases x <;> simp [cycle]

/-! ### The degrees -/

/-- The in-degree of a vertex of the first side: one more at the first node, for the edge from
the top node. -/
theorem cycle_indeg_side₁ [Finite A] [Finite B] [Finite C] (a : A) :
    (cycle γ S₁ S₂ ℓ G r).indeg (.side₁ a) = S₁.graph.indeg a + optInd S₁.first a := by
  rw [indeg, indeg, ← ncard_optInd_one (.top : CycleVert A B C)]
  refine ncard_lift (ι := (CycleVert.side₁ : A → CycleVert A B C))
    (fun _ _ h => CycleVert.side₁.inj h) (fun a' => ?_) (fun x hx => ?_) (fun x hx a' => ?_)
  · simp [cycle]
  · cases x with
    | side₁ a' => exact (hx a' rfl).elim
    | _ => simp [cycle]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The in-degree of a vertex of the second side: one more at the first node, for the edge from
the top node. -/
theorem cycle_indeg_side₂ [Finite A] [Finite B] [Finite C] (b : B) :
    (cycle γ S₁ S₂ ℓ G r).indeg (.side₂ b) = S₂.graph.indeg b + optInd S₂.first b := by
  rw [indeg, indeg, ← ncard_optInd_one (.top : CycleVert A B C)]
  refine ncard_lift (ι := (CycleVert.side₂ : B → CycleVert A B C))
    (fun _ _ h => CycleVert.side₂.inj h) (fun b' => ?_) (fun x hx => ?_) (fun x hx b' => ?_)
  · simp [cycle]
  · cases x with
    | side₂ b' => exact (hx b' rfl).elim
    | _ => simp [cycle]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The in-degree of a vertex below the hybrid node: one more at the root of the network below,
for the edge from the hybrid node. -/
theorem cycle_indeg_below [Finite A] [Finite B] [Finite C] (c : C) :
    (cycle γ S₁ S₂ ℓ G r).indeg (.below c) = G.indeg c + optInd (some r) c := by
  rw [indeg, indeg, ← ncard_optInd_one (.hyb : CycleVert A B C)]
  refine ncard_lift (ι := (CycleVert.below : C → CycleVert A B C))
    (fun _ _ h => CycleVert.below.inj h) (fun c' => ?_) (fun x hx => ?_) (fun x hx c' => ?_)
  · simp [cycle]
  · cases x with
    | below c' => exact (hx c' rfl).elim
    | hyb => simp [cycle, eq_comm]
    | _ => simp [cycle]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The out-degree of a vertex of the first side: one more at the last node, for its hybrid
edge. -/
theorem cycle_outdeg_side₁ [Finite A] [Finite B] [Finite C] (a : A) :
    (cycle γ S₁ S₂ ℓ G r).outdeg (.side₁ a) = S₁.graph.outdeg a + optInd S₁.last a := by
  rw [outdeg, outdeg, ← ncard_optInd_one (.hyb : CycleVert A B C)]
  refine ncard_lift (ι := (CycleVert.side₁ : A → CycleVert A B C))
    (fun _ _ h => CycleVert.side₁.inj h) (fun a' => ?_) (fun x hx => ?_) (fun x hx a' => ?_)
  · simp [cycle]
  · cases x with
    | side₁ a' => exact (hx a' rfl).elim
    | _ => simp [cycle]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The out-degree of a vertex of the second side: one more at the last node, for its hybrid
edge. -/
theorem cycle_outdeg_side₂ [Finite A] [Finite B] [Finite C] (b : B) :
    (cycle γ S₁ S₂ ℓ G r).outdeg (.side₂ b) = S₂.graph.outdeg b + optInd S₂.last b := by
  rw [outdeg, outdeg, ← ncard_optInd_one (.hyb : CycleVert A B C)]
  refine ncard_lift (ι := (CycleVert.side₂ : B → CycleVert A B C))
    (fun _ _ h => CycleVert.side₂.inj h) (fun b' => ?_) (fun x hx => ?_) (fun x hx b' => ?_)
  · simp [cycle]
  · cases x with
    | side₂ b' => exact (hx b' rfl).elim
    | _ => simp [cycle]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The out-degree of a vertex below the hybrid node. -/
theorem cycle_outdeg_below [Finite A] [Finite B] [Finite C] (c : C) :
    (cycle γ S₁ S₂ ℓ G r).outdeg (.below c) = G.outdeg c := by
  rw [outdeg, outdeg]
  refine ncard_lift_of_forall_notMem (ι := (CycleVert.below : C → CycleVert A B C))
    (fun _ _ h => CycleVert.below.inj h) (fun c' => ?_) (fun x hx => ?_)
  · simp [cycle]
  · cases x with
    | below c' => exact (hx c' rfl).elim
    | _ => simp [cycle]

/-- The top node of a cycle has two children, the first nodes of the sides (or the hybrid
node, for a side without nodes). -/
theorem cycle_outdeg_top (hne : S₁.first ≠ none ∨ S₂.first ≠ none) :
    (cycle γ S₁ S₂ ℓ G r).outdeg .top = 2 := by
  rw [outdeg, Set.ncard_eq_two]
  rcases h₁ : S₁.first with _ | a <;> rcases h₂ : S₂.first with _ | b
  · simp [h₁, h₂] at hne
  · exact ⟨.side₂ b, .hyb, by simp, by ext x; cases x <;> simp [cycle, h₁, h₂, eq_comm]⟩
  · exact ⟨.side₁ a, .hyb, by simp, by ext x; cases x <;> simp [cycle, h₁, h₂, eq_comm]⟩
  · exact ⟨.side₁ a, .side₂ b, by simp, by ext x; cases x <;> simp [cycle, h₁, h₂, eq_comm]⟩

/-- The hybrid node of a cycle has two parents, the last nodes of the sides (or the top node,
for a side without nodes). -/
theorem cycle_indeg_hyb (hne : S₁.first ≠ none ∨ S₂.first ≠ none)
    (h₁ : S₁.first = none ↔ S₁.last = none) (h₂ : S₂.first = none ↔ S₂.last = none) :
    (cycle γ S₁ S₂ ℓ G r).indeg .hyb = 2 := by
  rw [indeg, Set.ncard_eq_two]
  rcases hl₁ : S₁.last with _ | a <;> rcases hl₂ : S₂.last with _ | b
  · simp [h₁.2 hl₁, h₂.2 hl₂] at hne
  · have hf₁ := h₁.2 hl₁
    exact ⟨.top, .side₂ b, by simp,
      by ext x; cases x <;> simp [cycle, hl₁, hl₂, hf₁, eq_comm]⟩
  · have hf₂ := h₂.2 hl₂
    exact ⟨.top, .side₁ a, by simp,
      by ext x; cases x <;> simp [cycle, hl₁, hl₂, hf₂, eq_comm]⟩
  · have hf₁ : S₁.first ≠ none := fun h => by rw [h₁.1 h] at hl₁; cases hl₁
    have hf₂ : S₂.first ≠ none := fun h => by rw [h₂.1 h] at hl₂; cases hl₂
    exact ⟨.side₁ a, .side₂ b, by simp,
      by ext x; cases x <;> simp [cycle, hl₁, hl₂, hf₁, hf₂, eq_comm]⟩

/-- The hybrid node of a cycle has one child. -/
theorem cycle_outdeg_hyb : (cycle γ S₁ S₂ ℓ G r).outdeg .hyb = 1 := by
  rw [outdeg_eq_one_iff]
  exact ⟨.below r, fun x => by cases x <;> simp [cycle]⟩

/-! ### The hybrid nodes -/

/-- The hybrid nodes on the first side are those of the graph of the side. -/
theorem cycle_isHybrid_side₁ [Finite A] [Finite B] [Finite C] (hS₁ : S₁.IsSide) (a : A) :
    (cycle γ S₁ S₂ ℓ G r).IsHybrid (.side₁ a) ↔ S₁.graph.IsHybrid a := by
  rw [IsHybrid, IsHybrid, cycle_indeg_side₁, cycle_outdeg_side₁]
  have hdeg := hS₁.degrees a
  by_cases hf : S₁.first = some a
  · have h0 : S₁.graph.indeg a = 0 := indeg_eq_zero_iff.2 (hS₁.not_adj_first a hf)
    rw [hf, h0, optInd_some_self]
    simp
  · rw [optInd_of_ne hf, add_zero]
    by_cases hl : S₁.last = some a
    · have h1 := hS₁.outdeg_last a hl
      rw [hl, optInd_some_self, h1]
      rw [optInd_of_ne hf, add_zero] at hdeg
      rw [hl, optInd_some_self, h1] at hdeg
      rcases hdeg with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
    · rw [optInd_of_ne hl, add_zero]

/-- The hybrid nodes on the second side are those of the graph of the side. -/
theorem cycle_isHybrid_side₂ [Finite A] [Finite B] [Finite C] (hS₂ : S₂.IsSide) (b : B) :
    (cycle γ S₁ S₂ ℓ G r).IsHybrid (.side₂ b) ↔ S₂.graph.IsHybrid b := by
  rw [IsHybrid, IsHybrid, cycle_indeg_side₂, cycle_outdeg_side₂]
  have hdeg := hS₂.degrees b
  by_cases hf : S₂.first = some b
  · have h0 : S₂.graph.indeg b = 0 := indeg_eq_zero_iff.2 (hS₂.not_adj_first b hf)
    rw [hf, h0, optInd_some_self]
    simp
  · rw [optInd_of_ne hf, add_zero]
    by_cases hl : S₂.last = some b
    · have h1 := hS₂.outdeg_last b hl
      rw [hl, optInd_some_self, h1]
      rw [optInd_of_ne hf, add_zero] at hdeg
      rw [hl, optInd_some_self, h1] at hdeg
      rcases hdeg with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
    · rw [optInd_of_ne hl, add_zero]

/-- The hybrid nodes below the hybrid node are those of the network below it. -/
theorem cycle_isHybrid_below [Finite A] [Finite B] [Finite C] (hG : G.IsSubnet r) (c : C) :
    (cycle γ S₁ S₂ ℓ G r).IsHybrid (.below c) ↔ G.IsHybrid c := by
  rw [IsHybrid, IsHybrid, cycle_indeg_below, cycle_outdeg_below]
  by_cases hc : c = r
  · subst hc
    rw [indeg_eq_zero_iff.2 hG.not_adj_root, optInd_some_self]
    simp
  · rw [optInd_some_of_ne (Ne.symm hc), add_zero]

/-- The top node of a cycle is not a hybrid node. -/
theorem cycle_not_isHybrid_top : ¬ (cycle γ S₁ S₂ ℓ G r).IsHybrid .top := by
  rintro ⟨h, -⟩
  rw [indeg_eq_two_iff] at h
  obtain ⟨u, _, _, hu⟩ := h
  exact cycle_not_adj_top u ((hu u).2 (Or.inl rfl))

/-! ### The inheritance probabilities of the hybrid edges of the cycle -/

/-- The two hybrid edges of the cycle have inheritance probabilities `γ` and `1 - γ`. -/
theorem cycle_inh_hyb (hγ : 0 < γ) (hγ1 : γ < 1) (h₁ : S₁.first = none ↔ S₁.last = none)
    (h₂ : S₂.first = none ↔ S₂.last = none) :
    (∀ u, (cycle γ S₁ S₂ ℓ G r).Adj u .hyb → (cycle γ S₁ S₂ ℓ G r).inh u .hyb ∈ Set.Ioo 0 1) ∧
    ∀ u u', (cycle γ S₁ S₂ ℓ G r).Adj u .hyb → (cycle γ S₁ S₂ ℓ G r).Adj u' .hyb → u ≠ u' →
      (cycle γ S₁ S₂ ℓ G r).inh u .hyb + (cycle γ S₁ S₂ ℓ G r).inh u' .hyb = 1 := by
  have hmem : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ, hγ1⟩
  have hmem' : 1 - γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- the probability of the edge from the top node: `γ` if the side `S₁` has no node
  have htop : (cycle γ S₁ S₂ ℓ G r).inh .top .hyb = match S₁.first with
      | none => γ
      | some _ => 1 - γ := rfl
  refine ⟨fun u hu => ?_, fun u u' hu hu' huu' => ?_⟩
  · rw [cycle_adj_hyb_iff] at hu
    rcases hu with ⟨rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨b, rfl, -⟩
    · rw [htop]
      rcases S₁.first with _ | _
      · exact hmem
      · exact hmem'
    · exact hmem
    · exact hmem'
  · rw [cycle_adj_hyb_iff] at hu hu'
    rcases hu with ⟨rfl, hu⟩ | ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩ <;>
      rcases hu' with ⟨rfl, hu'⟩ | ⟨a', rfl, ha'⟩ | ⟨b', rfl, hb'⟩
    · exact (huu' rfl).elim
    · -- the top node and the last node of `S₁`: the side `S₂` has no node
      have hf : S₁.first ≠ none := fun h => by rw [h₁.1 h] at ha'; cases ha'
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hf
      rw [htop, hf]
      show 1 - γ + γ = 1
      ring
    · have hf : S₂.first ≠ none := fun h => by rw [h₂.1 h] at hb'; cases hb'
      have hf₁ : S₁.first = none := hu.resolve_right hf
      rw [htop, hf₁]
      show γ + (1 - γ) = 1
      ring
    · have hf : S₁.first ≠ none := fun h => by rw [h₁.1 h] at ha; cases ha
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hf
      rw [htop, hf]
      show γ + (1 - γ) = 1
      ring
    · rw [ha] at ha'
      exact (huu' (by rw [Option.some.inj ha'])).elim
    · show γ + (1 - γ) = 1
      ring
    · have hf : S₂.first ≠ none := fun h => by rw [h₂.1 h] at hb; cases hb
      have hf₁ : S₁.first = none := hu'.resolve_right hf
      rw [htop, hf₁]
      show 1 - γ + γ = 1
      ring
    · show 1 - γ + γ = 1
      ring
    · rw [hb] at hb'
      exact (huu' (by rw [Option.some.inj hb'])).elim

/-! ### The cuts -/

/-- The only undirected edge leaving the network below the hybrid node is the edge from the
hybrid node. -/
theorem cycle_cut_below (x' y' : CycleVert A B C)
    (hx' : x' ∈ Set.range (CycleVert.below : C → CycleVert A B C))
    (hy' : y' ∉ Set.range (CycleVert.below : C → CycleVert A B C))
    (h : (cycle γ S₁ S₂ ℓ G r).undirected.Adj x' y') : s(x', y') = s(.hyb, .below r) := by
  obtain ⟨c, rfl⟩ := hx'
  cases y' with
  | below c' => exact (hy' (Set.mem_range_self c')).elim
  | hyb =>
    simp only [undirected_adj, cycle, ne_eq, reduceCtorEq, not_false_eq_true, false_or,
      true_and] at h
    rw [h, Sym2.eq_swap]
  | _ => simp [undirected_adj, cycle] at h

/-- The network below the hybrid node is attached at its root only. -/
theorem cycle_attach_below (c : C) (y : CycleVert A B C)
    (h : (cycle γ S₁ S₂ ℓ G r).undirected.Adj (.below c) y)
    (hy : ∀ c', CycleVert.below c' ≠ y) : c ∈ ({r} : Set C) := by
  cases y with
  | below c' => exact (hy c' rfl).elim
  | hyb => simpa [undirected_adj, cycle] using h
  | _ => simp [undirected_adj, cycle] at h

/-- The first side is attached at its first and last nodes only. -/
theorem cycle_attach_side₁ (a : A) (y : CycleVert A B C)
    (h : (cycle γ S₁ S₂ ℓ G r).undirected.Adj (.side₁ a) y)
    (hy : ∀ a', CycleVert.side₁ a' ≠ y) : a ∈ {a | S₁.first = some a ∨ S₁.last = some a} := by
  cases y with
  | side₁ a' => exact (hy a' rfl).elim
  | top => exact Or.inl (by simpa [undirected_adj, cycle] using h)
  | hyb => exact Or.inr (by simpa [undirected_adj, cycle] using h)
  | _ => simp [undirected_adj, cycle] at h

/-- The second side is attached at its first and last nodes only. -/
theorem cycle_attach_side₂ (b : B) (y : CycleVert A B C)
    (h : (cycle γ S₁ S₂ ℓ G r).undirected.Adj (.side₂ b) y)
    (hy : ∀ b', CycleVert.side₂ b' ≠ y) : b ∈ {b | S₂.first = some b ∨ S₂.last = some b} := by
  cases y with
  | side₂ b' => exact (hy b' rfl).elim
  | top => exact Or.inl (by simpa [undirected_adj, cycle] using h)
  | hyb => exact Or.inr (by simpa [undirected_adj, cycle] using h)
  | _ => simp [undirected_adj, cycle] at h

/-- The cycle graph `K` of the graph of a cycle: the edges at the top node and at the hybrid
node, and the cycle edges of the sides and of the network below the hybrid node. -/
def cycleK (S₁ : SideGraph A X) (S₂ : SideGraph B X) (K₁ : SimpleGraph A) (K₂ : SimpleGraph B)
    (KG : SimpleGraph C) : SimpleGraph (CycleVert A B C) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | .top, .side₁ a => S₁.first = some a
    | .top, .side₂ b => S₂.first = some b
    | .top, .hyb => S₁.first = none ∨ S₂.first = none
    | .side₁ a, .side₁ a' => K₁.Adj a a'
    | .side₁ a, .hyb => S₁.last = some a
    | .side₂ b, .side₂ b' => K₂.Adj b b'
    | .side₂ b, .hyb => S₂.last = some b
    | .below c, .below c' => KG.Adj c c'
    | _, _ => False

variable {K₁ : SimpleGraph A} {K₂ : SimpleGraph B} {KG : SimpleGraph C}

/-- The cycle edges at a vertex of the first side. -/
theorem cycleK_side₁_iff (a : A) (y : CycleVert A B C) :
    (cycleK S₁ S₂ K₁ K₂ KG).Adj (.side₁ a) y ↔ (∃ a', y = .side₁ a' ∧ K₁.Adj a a') ∨
      (y = .top ∧ S₁.first = some a) ∨ (y = .hyb ∧ S₁.last = some a) := by
  cases y with
  | side₁ a' =>
    simp only [cycleK, SimpleGraph.fromRel_adj, ne_eq, CycleVert.side₁.injEq, reduceCtorEq,
      false_and, or_false, exists_eq_left']
    exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
  | _ => simp [cycleK]

/-- The cycle edges at a vertex of the second side. -/
theorem cycleK_side₂_iff (b : B) (y : CycleVert A B C) :
    (cycleK S₁ S₂ K₁ K₂ KG).Adj (.side₂ b) y ↔ (∃ b', y = .side₂ b' ∧ K₂.Adj b b') ∨
      (y = .top ∧ S₂.first = some b) ∨ (y = .hyb ∧ S₂.last = some b) := by
  cases y with
  | side₂ b' =>
    simp only [cycleK, SimpleGraph.fromRel_adj, ne_eq, CycleVert.side₂.injEq, reduceCtorEq,
      false_and, or_false, exists_eq_left']
    exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
  | _ => simp [cycleK]

/-- The cycle edges at a vertex below the hybrid node. -/
theorem cycleK_below_iff (c : C) (y : CycleVert A B C) :
    (cycleK S₁ S₂ K₁ K₂ KG).Adj (.below c) y ↔ ∃ c', y = .below c' ∧ KG.Adj c c' := by
  cases y with
  | below c' =>
    simp only [cycleK, SimpleGraph.fromRel_adj, ne_eq, CycleVert.below.injEq, exists_eq_left']
    exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
  | _ => simp [cycleK]

/-- The cycle edges at the top node. -/
theorem cycleK_top_iff (y : CycleVert A B C) :
    (cycleK S₁ S₂ K₁ K₂ KG).Adj .top y ↔ (∃ a, y = .side₁ a ∧ S₁.first = some a) ∨
      (∃ b, y = .side₂ b ∧ S₂.first = some b) ∨
      (y = .hyb ∧ (S₁.first = none ∨ S₂.first = none)) := by
  cases y <;> simp [cycleK]

/-- The cycle edges at the hybrid node. -/
theorem cycleK_hyb_iff (y : CycleVert A B C) :
    (cycleK S₁ S₂ K₁ K₂ KG).Adj .hyb y ↔ (∃ a, y = .side₁ a ∧ S₁.last = some a) ∨
      (∃ b, y = .side₂ b ∧ S₂.last = some b) ∨
      (y = .top ∧ (S₁.first = none ∨ S₂.first = none)) := by
  cases y <;> simp [cycleK]

/-- The undirected edges of the graph of a cycle that are not edges of `cycleK`: those of the
parts, and the edge below the hybrid node. -/
theorem cycle_undirected_adj_of_not_cycleK {x y : CycleVert A B C}
    (h : (cycle γ S₁ S₂ ℓ G r).undirected.Adj x y) (hK : ¬ (cycleK S₁ S₂ K₁ K₂ KG).Adj x y) :
    (∃ a a', x = .side₁ a ∧ y = .side₁ a' ∧ S₁.graph.undirected.Adj a a' ∧ ¬ K₁.Adj a a') ∨
    (∃ b b', x = .side₂ b ∧ y = .side₂ b' ∧ S₂.graph.undirected.Adj b b' ∧ ¬ K₂.Adj b b') ∨
    (x = .hyb ∧ y = .below r) ∨ (x = .below r ∧ y = .hyb) ∨
    (∃ c c', x = .below c ∧ y = .below c' ∧ G.undirected.Adj c c' ∧ ¬ KG.Adj c c') := by
  cases x with
  | top =>
    exfalso
    apply hK
    rw [cycleK_top_iff]
    cases y <;> simp_all [undirected_adj, cycle]
  | hyb =>
    cases y with
    | below c =>
      right; right; left
      simp_all [undirected_adj, cycle]
    | _ =>
      exfalso
      apply hK
      rw [cycleK_hyb_iff]
      simp_all [undirected_adj, cycle]
  | side₁ a =>
    cases y with
    | side₁ a' =>
      left
      refine ⟨a, a', rfl, rfl, (undirected_adj_lift (G := S₁.graph) (ι := CycleVert.side₁)
        (fun _ _ h => CycleVert.side₁.inj h) (fun _ _ => Iff.rfl) a a').1 h, fun h' => hK ?_⟩
      exact (cycleK_side₁_iff a _).2 (Or.inl ⟨a', rfl, h'⟩)
    | _ =>
      exfalso
      apply hK
      rw [cycleK_side₁_iff]
      simp_all [undirected_adj, cycle]
  | side₂ b =>
    cases y with
    | side₂ b' =>
      right; left
      refine ⟨b, b', rfl, rfl, (undirected_adj_lift (G := S₂.graph) (ι := CycleVert.side₂)
        (fun _ _ h => CycleVert.side₂.inj h) (fun _ _ => Iff.rfl) b b').1 h, fun h' => hK ?_⟩
      exact (cycleK_side₂_iff b _).2 (Or.inl ⟨b', rfl, h'⟩)
    | _ =>
      exfalso
      apply hK
      rw [cycleK_side₂_iff]
      simp_all [undirected_adj, cycle]
  | below c =>
    cases y with
    | below c' =>
      right; right; right; right
      refine ⟨c, c', rfl, rfl, (undirected_adj_lift (G := G) (ι := CycleVert.below)
        (fun _ _ h => CycleVert.below.inj h) (fun _ _ => Iff.rfl) c c').1 h, fun h' => hK ?_⟩
      exact (cycleK_below_iff c _).2 ⟨c', rfl, h'⟩
    | hyb =>
      right; right; right; left
      simp_all [undirected_adj, cycle]
    | _ => simp_all [undirected_adj, cycle]

/-! ### The degrees in the cycle graph -/

/-- The top node has two cycle edges. -/
theorem cycleK_ncard_top (hne : S₁.first ≠ none ∨ S₂.first ≠ none) :
    ((cycleK S₁ S₂ K₁ K₂ KG).neighborSet .top).ncard = 2 := by
  rw [Set.ncard_eq_two]
  rcases h₁ : S₁.first with _ | a <;> rcases h₂ : S₂.first with _ | b
  · simp [h₁, h₂] at hne
  · exact ⟨.side₂ b, .hyb, by simp, by ext y; simp [cycleK_top_iff, h₁, h₂, eq_comm, or_comm]⟩
  · exact ⟨.side₁ a, .hyb, by simp, by ext y; simp [cycleK_top_iff, h₁, h₂, eq_comm, or_comm]⟩
  · exact ⟨.side₁ a, .side₂ b, by simp, by ext y; simp [cycleK_top_iff, h₁, h₂, eq_comm]⟩

/-- The hybrid node has two cycle edges. -/
theorem cycleK_ncard_hyb (hne : S₁.first ≠ none ∨ S₂.first ≠ none)
    (h₁ : S₁.first = none ↔ S₁.last = none) (h₂ : S₂.first = none ↔ S₂.last = none) :
    ((cycleK S₁ S₂ K₁ K₂ KG).neighborSet .hyb).ncard = 2 := by
  rw [Set.ncard_eq_two]
  rcases hl₁ : S₁.last with _ | a <;> rcases hl₂ : S₂.last with _ | b
  · simp [h₁.2 hl₁, h₂.2 hl₂] at hne
  · have hf₁ := h₁.2 hl₁
    exact ⟨.side₂ b, .top, by simp,
      by ext y; simp [cycleK_hyb_iff, hl₁, hl₂, hf₁]⟩
  · have hf₂ := h₂.2 hl₂
    exact ⟨.side₁ a, .top, by simp,
      by ext y; simp [cycleK_hyb_iff, hl₁, hl₂, hf₂]⟩
  · have hf₁ : S₁.first ≠ none := fun h => by rw [h₁.1 h] at hl₁; cases hl₁
    have hf₂ : S₂.first ≠ none := fun h => by rw [h₂.1 h] at hl₂; cases hl₂
    exact ⟨.side₁ a, .side₂ b, by simp,
      by ext y; simp [cycleK_hyb_iff, hl₁, hl₂, hf₁, hf₂]⟩

/-- The cycle edges at a vertex of the first side: those of the side, and the edges to the top
and hybrid nodes at its first and last nodes. -/
theorem cycleK_ncard_side₁ [Finite A] [Finite B] [Finite C] (a : A) :
    ((cycleK S₁ S₂ K₁ K₂ KG).neighborSet (.side₁ a)).ncard =
      (K₁.neighborSet a).ncard + optInd S₁.first a + optInd S₁.last a := by
  rw [add_assoc, ← ncard_optInd (A := A) (p := (.top : CycleVert A B C)) (q := .hyb) (by simp)]
  refine ncard_lift (ι := (CycleVert.side₁ : A → CycleVert A B C))
    (fun _ _ h => CycleVert.side₁.inj h) (fun a' => by simp [cycleK_side₁_iff])
    (fun y hy => ?_) (fun y hy a' => ?_)
  · simp only [SimpleGraph.mem_neighborSet, cycleK_side₁_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨a', rfl, -⟩ | h | h)
      · exact (hy a' rfl).elim
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · simp only [Set.mem_ofPred_eq] at hy
    rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- The cycle edges at a vertex of the second side: those of the side, and the edges to the top
and hybrid nodes at its first and last nodes. -/
theorem cycleK_ncard_side₂ [Finite A] [Finite B] [Finite C] (b : B) :
    ((cycleK S₁ S₂ K₁ K₂ KG).neighborSet (.side₂ b)).ncard =
      (K₂.neighborSet b).ncard + optInd S₂.first b + optInd S₂.last b := by
  rw [add_assoc, ← ncard_optInd (A := B) (p := (.top : CycleVert A B C)) (q := .hyb) (by simp)]
  refine ncard_lift (ι := (CycleVert.side₂ : B → CycleVert A B C))
    (fun _ _ h => CycleVert.side₂.inj h) (fun b' => by simp [cycleK_side₂_iff])
    (fun y hy => ?_) (fun y hy b' => ?_)
  · simp only [SimpleGraph.mem_neighborSet, cycleK_side₂_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨b', rfl, -⟩ | h | h)
      · exact (hy b' rfl).elim
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · simp only [Set.mem_ofPred_eq] at hy
    rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

/-- The cycle edges at a vertex below the hybrid node are those of the network below it. -/
theorem cycleK_ncard_below [Finite A] [Finite B] [Finite C] (c : C) :
    ((cycleK S₁ S₂ K₁ K₂ KG).neighborSet (.below c)).ncard = (KG.neighborSet c).ncard := by
  refine ncard_lift_of_forall_notMem (ι := (CycleVert.below : C → CycleVert A B C))
    (fun _ _ h => CycleVert.below.inj h) (fun c' => by simp [cycleK_below_iff])
    (fun y hy => ?_)
  simp only [SimpleGraph.mem_neighborSet, cycleK_below_iff, not_exists, not_and]
  exact fun c' h => (hy c' h.symm).elim

/-- The cycle edges of the graph of a cycle: the edges at its top and hybrid nodes, and the
cycle edges of its parts. The edge below the hybrid node, and the cut edges of the parts, are cut
edges. -/
theorem cycle_cycles [Finite A] [Finite B] [Finite C] (hS₁ : S₁.IsSide) (hS₂ : S₂.IsSide)
    (hG : G.IsSubnet r) (hne : S₁.first ≠ none ∨ S₂.first ≠ none) :
    ∃ K : SimpleGraph (CycleVert A B C),
      (∀ v, (K.neighborSet v).ncard = 0 ∨ (K.neighborSet v).ncard = 2) ∧
      ∀ x y, (cycle γ S₁ S₂ ℓ G r).undirected.Adj x y → ¬ K.Adj x y →
        ∃ S : Set (CycleVert A B C), CycleVert.top ∉ S ∧ (x ∈ S ↔ y ∉ S) ∧
          ∀ x' y', x' ∈ S → y' ∉ S → (cycle γ S₁ S₂ ℓ G r).undirected.Adj x' y' →
            s(x', y') = s(x, y) := by
  obtain ⟨K₁, hK₁, hcut₁⟩ := hS₁.cycles
  obtain ⟨K₂, hK₂, hcut₂⟩ := hS₂.cycles
  obtain ⟨KG, hKG, hcutG⟩ := hG.cycles
  refine ⟨cycleK S₁ S₂ K₁ K₂ KG, fun v => ?_, fun x y hxy hxyK => ?_⟩
  · cases v with
    | top => exact Or.inr (cycleK_ncard_top hne)
    | hyb => exact Or.inr (cycleK_ncard_hyb hne hS₁.first_eq_none_iff hS₂.first_eq_none_iff)
    | side₁ a => rw [cycleK_ncard_side₁]; exact hK₁ a
    | side₂ b => rw [cycleK_ncard_side₂]; exact hK₂ b
    | below c => rw [cycleK_ncard_below]; exact hKG c
  · have hU₁ := undirected_adj_lift (G := S₁.graph) (H := cycle γ S₁ S₂ ℓ G r)
      (ι := CycleVert.side₁) (fun _ _ h => CycleVert.side₁.inj h) (fun _ _ => Iff.rfl)
    have hU₂ := undirected_adj_lift (G := S₂.graph) (H := cycle γ S₁ S₂ ℓ G r)
      (ι := CycleVert.side₂) (fun _ _ h => CycleVert.side₂.inj h) (fun _ _ => Iff.rfl)
    have hUG := undirected_adj_lift (G := G) (H := cycle γ S₁ S₂ ℓ G r)
      (ι := CycleVert.below) (fun _ _ h => CycleVert.below.inj h) (fun _ _ => Iff.rfl)
    rcases cycle_undirected_adj_of_not_cycleK hxy hxyK with
      ⟨a, a', rfl, rfl, hU, hK⟩ | ⟨b, b', rfl, rfl, hU, hK⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨c, c', rfl, rfl, hU, hK⟩
    · obtain ⟨T, hfT, hlT, hT, hc⟩ := hcut₁ a a' hU hK
      refine ⟨CycleVert.side₁ '' T, by simp, ?_, crossing_lift (fun _ _ => hU₁ _ _)
        (P := {a | S₁.first = some a ∨ S₁.last = some a}) cycle_attach_side₁
        (fun a ha h => h.elim (fun h' => hfT a h' ha) (fun h' => hlT a h' ha)) hc⟩
      simp only [Set.mem_image, CycleVert.side₁.injEq, exists_eq_right]
      exact hT
    · obtain ⟨T, hfT, hlT, hT, hc⟩ := hcut₂ b b' hU hK
      refine ⟨CycleVert.side₂ '' T, by simp, ?_, crossing_lift (fun _ _ => hU₂ _ _)
        (P := {b | S₂.first = some b ∨ S₂.last = some b}) cycle_attach_side₂
        (fun b hb h => h.elim (fun h' => hfT b h' hb) (fun h' => hlT b h' hb)) hc⟩
      simp only [Set.mem_image, CycleVert.side₂.injEq, exists_eq_right]
      exact hT
    · exact ⟨Set.range CycleVert.below, by simp, by simp, cycle_cut_below⟩
    · refine ⟨Set.range CycleVert.below, by simp, by simp, fun x' y' hx' hy' h => ?_⟩
      rw [cycle_cut_below x' y' hx' hy' h, Sym2.eq_swap]
    · obtain ⟨T, hrT, hT, hc⟩ := hcutG c c' hU hK
      refine ⟨CycleVert.below '' T, by simp, ?_, crossing_lift (fun _ _ => hUG _ _)
        (P := {r}) cycle_attach_below
        (fun c hc h => hrT (by rw [Set.mem_singleton_iff] at h; rwa [← h])) hc⟩
      simp only [Set.mem_image, CycleVert.below.injEq, exists_eq_right]
      exact hT

/-! ### The invariant -/

/-- The graph of a cycle has the invariant when the graphs of its two sides and of the network
below its hybrid node have theirs, with distinct labels, the sides do not both lack nodes, the
inheritance probability `γ` lies in `(0, 1)` and the edge below the hybrid node has positive
length. -/
theorem isSubnet_cycle (hγ : 0 < γ) (hγ1 : γ < 1) (hℓ : 0 < ℓ) (hS₁ : S₁.IsSide)
    (hS₂ : S₂.IsSide) (hG : G.IsSubnet r) (hne : S₁.first ≠ none ∨ S₂.first ≠ none)
    (hd₁₂ : ∀ a b x, S₁.graph.label a = some x → S₂.graph.label b = some x → False)
    (hd₁G : ∀ a c x, S₁.graph.label a = some x → G.label c = some x → False)
    (hd₂G : ∀ b c x, S₂.graph.label b = some x → G.label c = some x → False) :
    (cycle γ S₁ S₂ ℓ G r).IsSubnet .top := by
  have := hS₁.finite
  have := hS₂.finite
  have := hG.finite
  have hr : G.indeg r = 0 := indeg_eq_zero_iff.2 hG.not_adj_root
  obtain ⟨f₁, hf₁⟩ := hS₁.height
  obtain ⟨f₂, hf₂⟩ := hS₂.height
  obtain ⟨fG, hfG⟩ := hG.height
  have hinh := cycle_inh_hyb (ℓ := ℓ) (G := G) (r := r) hγ hγ1 hS₁.first_eq_none_iff
    hS₂.first_eq_none_iff
  have hhyb : (cycle γ S₁ S₂ ℓ G r).IsHybrid .hyb :=
    ⟨cycle_indeg_hyb hne hS₁.first_eq_none_iff hS₂.first_eq_none_iff, cycle_outdeg_hyb⟩
  have hneG : ∀ c, G.IsHybrid c → c ≠ r := fun c hc h => by rw [h, IsHybrid, hr] at hc; omega
  have hne₁ : ∀ a, S₁.graph.IsHybrid a → S₁.first ≠ some a := fun a ha h => by
    rw [IsHybrid, indeg_eq_zero_iff.2 (hS₁.not_adj_first a h)] at ha; omega
  have hne₂ : ∀ b, S₂.graph.IsHybrid b → S₂.first ≠ some b := fun b hb h => by
    rw [IsHybrid, indeg_eq_zero_iff.2 (hS₂.not_adj_first b h)] at hb; omega
  let H : ℕ := S₁.last.elim 0 f₁ + S₂.last.elim 0 f₂
  refine
    { finite := inferInstance
      height := ⟨fun
        | .top => 0
        | .side₁ a => f₁ a + 1
        | .side₂ b => f₂ b + 1
        | .hyb => H + 2
        | .below c => H + 3 + fG c, ?_⟩
      not_adj_root := cycle_not_adj_top
      outdeg_root := Or.inr (cycle_outdeg_top hne)
      degrees := ?_
      len_pos := ?_
      inh_mem_Ioo := ?_
      inh_add_inh := ?_
      isSome_label_iff := ?_
      label_injective := ?_
      cycles := cycle_cycles hS₁ hS₂ hG hne }
  · intro u v huv
    cases v with
    | top => exact (cycle_not_adj_top u huv).elim
    | side₁ a =>
      rcases (cycle_adj_side₁_iff u a).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · exact Nat.succ_pos _
      · exact Nat.succ_lt_succ (hf₁ u a hu)
    | side₂ b =>
      rcases (cycle_adj_side₂_iff u b).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · exact Nat.succ_pos _
      · exact Nat.succ_lt_succ (hf₂ u b hu)
    | hyb =>
      rcases (cycle_adj_hyb_iff u).1 huv with ⟨rfl, -⟩ | ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
      · show 0 < H + 2
        omega
      · show f₁ a + 1 < H + 2
        simp only [H, ha, Option.elim_some]
        omega
      · show f₂ b + 1 < H + 2
        simp only [H, hb, Option.elim_some]
        omega
    | below c =>
      rcases (cycle_adj_below_iff u c).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · show H + 2 < H + 3 + fG c
        omega
      · show H + 3 + fG u < H + 3 + fG c
        have := hfG u c hu
        omega
  · intro v hv
    cases v with
    | top => exact (hv rfl).elim
    | hyb => exact Or.inr (Or.inr hhyb)
    | side₁ a =>
      rw [cycle_indeg_side₁, cycle_outdeg_side₁]
      exact hS₁.degrees a
    | side₂ b =>
      rw [cycle_indeg_side₂, cycle_outdeg_side₂]
      exact hS₂.degrees b
    | below c =>
      rw [cycle_indeg_below, cycle_outdeg_below]
      by_cases hc : c = r
      · subst hc
        rw [hr, optInd_some_self]
        rcases hG.outdeg_root with h | h <;> simp [DegOK, h]
      · rw [optInd_some_of_ne (Ne.symm hc), add_zero]
        exact hG.degrees c hc
  · intro u v huv
    cases v with
    | top => exact (cycle_not_adj_top u huv).elim
    | side₁ a =>
      rcases (cycle_adj_side₁_iff u a).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · exact hS₁.topLen_pos
      · exact hS₁.len_pos u a hu
    | side₂ b =>
      rcases (cycle_adj_side₂_iff u b).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · exact hS₂.topLen_pos
      · exact hS₂.len_pos u b hu
    | hyb =>
      rcases (cycle_adj_hyb_iff u).1 huv with ⟨rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨b, rfl, -⟩
      · show 0 < (match S₁.first with | none => S₁.hybLen | some _ => S₂.hybLen)
        rcases S₁.first with _ | _
        · exact hS₁.hybLen_pos
        · exact hS₂.hybLen_pos
      · exact hS₁.hybLen_pos
      · exact hS₂.hybLen_pos
    | below c =>
      rcases (cycle_adj_below_iff u c).1 huv with ⟨rfl, -⟩ | ⟨u, rfl, hu⟩
      · exact hℓ
      · exact hG.len_pos u c hu
  · intro u v huv hv
    cases v with
    | top => exact (cycle_not_isHybrid_top hv).elim
    | hyb => exact hinh.1 u huv
    | side₁ a =>
      rw [cycle_isHybrid_side₁ hS₁] at hv
      rcases (cycle_adj_side₁_iff u a).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hne₁ a hv h).elim
      · exact hS₁.inh_mem_Ioo u a hu hv
    | side₂ b =>
      rw [cycle_isHybrid_side₂ hS₂] at hv
      rcases (cycle_adj_side₂_iff u b).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hne₂ b hv h).elim
      · exact hS₂.inh_mem_Ioo u b hu hv
    | below c =>
      rw [cycle_isHybrid_below hG] at hv
      rcases (cycle_adj_below_iff u c).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hneG c hv h).elim
      · exact hG.inh_mem_Ioo u c hu hv
  · intro u u' v huv hu'v huu' hv
    cases v with
    | top => exact (cycle_not_isHybrid_top hv).elim
    | hyb => exact hinh.2 u u' huv hu'v huu'
    | side₁ a =>
      rw [cycle_isHybrid_side₁ hS₁] at hv
      rcases (cycle_adj_side₁_iff u a).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hne₁ a hv h).elim
      rcases (cycle_adj_side₁_iff u' a).1 hu'v with ⟨-, h⟩ | ⟨u', rfl, hu'⟩
      · exact (hne₁ a hv h).elim
      exact hS₁.inh_add_inh u u' a hu hu' (fun h => huu' (by rw [h])) hv
    | side₂ b =>
      rw [cycle_isHybrid_side₂ hS₂] at hv
      rcases (cycle_adj_side₂_iff u b).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hne₂ b hv h).elim
      rcases (cycle_adj_side₂_iff u' b).1 hu'v with ⟨-, h⟩ | ⟨u', rfl, hu'⟩
      · exact (hne₂ b hv h).elim
      exact hS₂.inh_add_inh u u' b hu hu' (fun h => huu' (by rw [h])) hv
    | below c =>
      rw [cycle_isHybrid_below hG] at hv
      rcases (cycle_adj_below_iff u c).1 huv with ⟨-, h⟩ | ⟨u, rfl, hu⟩
      · exact (hneG c hv h).elim
      rcases (cycle_adj_below_iff u' c).1 hu'v with ⟨-, h⟩ | ⟨u', rfl, hu'⟩
      · exact (hneG c hv h).elim
      exact hG.inh_add_inh u u' c hu hu' (fun h => huu' (by rw [h])) hv
  · intro v
    cases v with
    | top =>
      rw [cycle_outdeg_top hne]
      simp [cycle]
    | hyb =>
      rw [cycle_outdeg_hyb]
      simp [cycle]
    | side₁ a =>
      rw [cycle_outdeg_side₁]
      exact hS₁.isSome_label_iff a
    | side₂ b =>
      rw [cycle_outdeg_side₂]
      exact hS₂.isSome_label_iff b
    | below c =>
      rw [cycle_outdeg_below]
      exact hG.isSome_label_iff c
  · intro u v x hu hv
    cases u with
    | top => simp [cycle] at hu
    | hyb => simp [cycle] at hu
    | side₁ a =>
      cases v with
      | top => simp [cycle] at hv
      | hyb => simp [cycle] at hv
      | side₁ a' => exact congrArg _ (hS₁.label_injective a a' x hu hv)
      | side₂ b => exact (hd₁₂ a b x hu hv).elim
      | below c => exact (hd₁G a c x hu hv).elim
    | side₂ b =>
      cases v with
      | top => simp [cycle] at hv
      | hyb => simp [cycle] at hv
      | side₁ a => exact (hd₁₂ a b x hv hu).elim
      | side₂ b' => exact congrArg _ (hS₂.label_injective b b' x hu hv)
      | below c => exact (hd₂G b c x hu hv).elim
    | below c =>
      cases v with
      | top => simp [cycle] at hv
      | hyb => simp [cycle] at hv
      | side₁ a => exact (hd₁G a c x hv hu).elim
      | side₂ b => exact (hd₂G b c x hv hu).elim
      | below c' => exact congrArg _ (hG.label_injective c c' x hu hv)

end MetricDigraph

end Phylogenetics
