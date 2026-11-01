module

public import Phylogenetics.Network.Level1.Digraph.Invariant
/-!
# The invariant for a tree node on no cycle

`Phylogenetics.MetricDigraph.isSubnet_tree`: the graph of `Net.tree ℓ₁ N₁ ℓ₂ N₂` has the invariant
`Phylogenetics.MetricDigraph.IsSubnet` when the graphs of `N₁` and `N₂` have it. The two new edges
are cut edges: each is the only edge leaving the vertices of its subnetwork. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

open SimpleGraph

variable {X : Type u}

namespace MetricDigraph

variable {A B : Type} {ℓ₁ ℓ₂ : ℝ} {G₁ : MetricDigraph A X} {r₁ : A} {G₂ : MetricDigraph B X}
  {r₂ : B}

/-- The edges into a vertex of the first subnetwork. -/
theorem tree_adj_left_iff (x : TreeVert A B) (a : A) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj x (.left a) ↔
      (x = .root ∧ a = r₁) ∨ ∃ u, x = .left u ∧ G₁.Adj u a := by
  cases x <;> simp [tree]

/-- The edges into a vertex of the second subnetwork. -/
theorem tree_adj_right_iff (x : TreeVert A B) (b : B) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj x (.right b) ↔
      (x = .root ∧ b = r₂) ∨ ∃ u, x = .right u ∧ G₂.Adj u b := by
  cases x <;> simp [tree]

/-- The edges out of a vertex of the first subnetwork. -/
theorem tree_left_adj_iff (a : A) (y : TreeVert A B) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj (.left a) y ↔ ∃ w, y = .left w ∧ G₁.Adj a w := by
  cases y <;> simp [tree]

/-- The edges out of a vertex of the second subnetwork. -/
theorem tree_right_adj_iff (b : B) (y : TreeVert A B) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj (.right b) y ↔ ∃ w, y = .right w ∧ G₂.Adj b w := by
  cases y <;> simp [tree]

/-- No edge enters the new root. -/
theorem tree_not_adj_root (x : TreeVert A B) : ¬ (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj x .root := by
  cases x <;> simp [tree]

/-- The in-degree of a vertex of the first subnetwork: one more at its root, for the edge from
the new root. -/
theorem tree_indeg_left [Finite A] [Finite B] (a : A) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).indeg (.left a) = G₁.indeg a + optInd (some r₁) a := by
  rw [indeg, indeg, ← ncard_optInd_one (.root : TreeVert A B)]
  refine ncard_lift (ι := (TreeVert.left : A → TreeVert A B)) (fun _ _ h => TreeVert.left.inj h)
    (fun a' => ?_) (fun x hx => ?_) (fun x hx a' => ?_)
  · simp [tree]
  · cases x with
    | root => simp [tree, eq_comm]
    | left a' => exact (hx a' rfl).elim
    | right b => simp [tree]
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The in-degree of a vertex of the second subnetwork: one more at its root, for the edge from
the new root. -/
theorem tree_indeg_right [Finite A] [Finite B] (b : B) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).indeg (.right b) = G₂.indeg b + optInd (some r₂) b := by
  rw [indeg, indeg, ← ncard_optInd_one (.root : TreeVert A B)]
  refine ncard_lift (ι := (TreeVert.right : B → TreeVert A B)) (fun _ _ h => TreeVert.right.inj h)
    (fun b' => ?_) (fun x hx => ?_) (fun x hx b' => ?_)
  · simp [tree]
  · cases x with
    | root => simp [tree, eq_comm]
    | left a => simp [tree]
    | right b' => exact (hx b' rfl).elim
  · simp only [Set.mem_ofPred_eq] at hx
    rw [hx.1]
    simp

/-- The out-degree of a vertex of the first subnetwork. -/
theorem tree_outdeg_left [Finite A] [Finite B] (a : A) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).outdeg (.left a) = G₁.outdeg a := by
  rw [outdeg, outdeg]
  refine ncard_lift_of_forall_notMem (ι := (TreeVert.left : A → TreeVert A B))
    (fun _ _ h => TreeVert.left.inj h) (fun a' => ?_) (fun x hx => ?_)
  · simp [tree]
  · cases x with
    | root => simp [tree]
    | left a' => exact (hx a' rfl).elim
    | right b => simp [tree]

/-- The out-degree of a vertex of the second subnetwork. -/
theorem tree_outdeg_right [Finite A] [Finite B] (b : B) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).outdeg (.right b) = G₂.outdeg b := by
  rw [outdeg, outdeg]
  refine ncard_lift_of_forall_notMem (ι := (TreeVert.right : B → TreeVert A B))
    (fun _ _ h => TreeVert.right.inj h) (fun b' => ?_) (fun x hx => ?_)
  · simp [tree]
  · cases x with
    | root => simp [tree]
    | left a => simp [tree]
    | right b' => exact (hx b' rfl).elim

/-- The new root has two children. -/
theorem tree_outdeg_root : (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).outdeg .root = 2 := by
  have : {w | (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).Adj .root w} = {.left r₁, .right r₂} := by
    ext w
    cases w <;> simp [tree]
  rw [outdeg, this, Set.ncard_pair (by simp)]

/-- The undirected edges of the graph of a tree node. -/
theorem tree_undirected_adj_iff {x y : TreeVert A B} :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj x y ↔
      (x = .root ∧ y = .left r₁) ∨ (x = .left r₁ ∧ y = .root) ∨
      (x = .root ∧ y = .right r₂) ∨ (x = .right r₂ ∧ y = .root) ∨
      (∃ a a', x = .left a ∧ y = .left a' ∧ G₁.undirected.Adj a a') ∨
      (∃ b b', x = .right b ∧ y = .right b' ∧ G₂.undirected.Adj b b') := by
  cases x <;> cases y <;> simp [undirected_adj, tree, eq_comm]

/-- The only undirected edge leaving the vertices of the first subnetwork is the edge from the
new root. -/
theorem tree_cut_left (x' y' : TreeVert A B) (hx' : x' ∈ Set.range (TreeVert.left : A → _))
    (hy' : y' ∉ Set.range (TreeVert.left : A → TreeVert A B))
    (h : (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj x' y') : s(x', y') = s(.root, .left r₁) := by
  obtain ⟨a, rfl⟩ := hx'
  rw [tree_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨a, a', h1, rfl, -⟩ | ⟨b, b', h, -⟩
  · cases h
  · rw [h1, Sym2.eq_swap]
  · cases h
  · cases h
  · exact (hy' (Set.mem_range_self a')).elim
  · cases h

/-- The only undirected edge leaving the vertices of the second subnetwork is the edge from the
new root. -/
theorem tree_cut_right (x' y' : TreeVert A B) (hx' : x' ∈ Set.range (TreeVert.right : B → _))
    (hy' : y' ∉ Set.range (TreeVert.right : B → TreeVert A B))
    (h : (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj x' y') : s(x', y') = s(.root, .right r₂) := by
  obtain ⟨b, rfl⟩ := hx'
  rw [tree_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h1, rfl⟩ | ⟨a, a', h, -⟩ | ⟨b, b', h1, rfl, -⟩
  · cases h
  · cases h
  · cases h
  · rw [h1, Sym2.eq_swap]
  · cases h
  · exact (hy' (Set.mem_range_self b')).elim

/-- The first subnetwork is attached at its root only. -/
theorem tree_attach_left (a : A) (y : TreeVert A B)
    (h : (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj (.left a) y) (hy : ∀ a', TreeVert.left a' ≠ y) :
    a ∈ ({r₁} : Set A) := by
  rw [tree_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h1, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨a₁, a', h1, rfl, -⟩ | ⟨b, b', h, -⟩
  · cases h
  · exact TreeVert.left.inj h1
  · cases h
  · cases h
  · exact (hy a' rfl).elim
  · cases h

/-- The second subnetwork is attached at its root only. -/
theorem tree_attach_right (b : B) (y : TreeVert A B)
    (h : (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj (.right b) y) (hy : ∀ b', TreeVert.right b' ≠ y) :
    b ∈ ({r₂} : Set B) := by
  rw [tree_undirected_adj_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h1, -⟩ | ⟨a, a', h, -⟩ | ⟨b₁, b', h1, rfl, -⟩
  · cases h
  · cases h
  · cases h
  · exact TreeVert.right.inj h1
  · cases h
  · exact (hy b' rfl).elim

/-- The cycle edges of the graph of a tree node are those of its subnetworks; the two new edges,
and the edges that are cut edges in a subnetwork, are cut edges. -/
theorem tree_cycles [Finite A] [Finite B] (h₁ : G₁.IsSubnet r₁) (h₂ : G₂.IsSubnet r₂) :
    ∃ K : SimpleGraph (TreeVert A B),
      (∀ v, (K.neighborSet v).ncard = 0 ∨ (K.neighborSet v).ncard = 2) ∧
      ∀ x y, (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj x y → ¬ K.Adj x y →
        ∃ S : Set (TreeVert A B), TreeVert.root ∉ S ∧ (x ∈ S ↔ y ∉ S) ∧
          ∀ x' y', x' ∈ S → y' ∉ S → (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).undirected.Adj x' y' →
            s(x', y') = s(x, y) := by
  obtain ⟨K₁, hK₁, hcut₁⟩ := h₁.cycles
  obtain ⟨K₂, hK₂, hcut₂⟩ := h₂.cycles
  let K : SimpleGraph (TreeVert A B) := SimpleGraph.fromRel fun x y => match x, y with
    | .left a, .left a' => K₁.Adj a a'
    | .right b, .right b' => K₂.Adj b b'
    | _, _ => False
  have hKL : ∀ a y, K.Adj (.left a) y ↔ ∃ a', y = .left a' ∧ K₁.Adj a a' := by
    intro a y
    cases y with
    | root => simp [K]
    | left a' =>
      simp only [K, SimpleGraph.fromRel_adj, ne_eq, TreeVert.left.injEq, exists_eq_left']
      exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
    | right b => simp [K]
  have hKR : ∀ b y, K.Adj (.right b) y ↔ ∃ b', y = .right b' ∧ K₂.Adj b b' := by
    intro b y
    cases y with
    | root => simp [K]
    | left a => simp [K]
    | right b' =>
      simp only [K, SimpleGraph.fromRel_adj, ne_eq, TreeVert.right.injEq, exists_eq_left']
      exact ⟨fun h => h.2.elim id (fun h' => h'.symm), fun h => ⟨h.ne, Or.inl h⟩⟩
  have hK0 : ∀ y, ¬ K.Adj .root y := by
    intro y
    cases y <;> simp [K]
  have hUL := undirected_adj_lift (G := G₁) (H := tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂)
    (ι := TreeVert.left) (fun _ _ h => TreeVert.left.inj h) (fun _ _ => Iff.rfl)
  have hUR := undirected_adj_lift (G := G₂) (H := tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂)
    (ι := TreeVert.right) (fun _ _ h => TreeVert.right.inj h) (fun _ _ => Iff.rfl)
  refine ⟨K, fun v => ?_, fun x y hxy hxyK => ?_⟩
  · cases v with
    | root =>
      left
      rw [Set.ncard_eq_zero]
      ext y
      simp [hK0 y]
    | left a =>
      rw [ncard_lift_of_forall_notMem (ι := (TreeVert.left : A → TreeVert A B))
        (t := K₁.neighborSet a) (fun _ _ h => TreeVert.left.inj h) (fun a' => by simp [hKL])
        (fun y hy => by
          simp only [SimpleGraph.mem_neighborSet, hKL, not_exists, not_and]
          exact fun a' h => (hy a' h.symm).elim)]
      exact hK₁ a
    | right b =>
      rw [ncard_lift_of_forall_notMem (ι := (TreeVert.right : B → TreeVert A B))
        (t := K₂.neighborSet b) (fun _ _ h => TreeVert.right.inj h) (fun b' => by simp [hKR])
        (fun y hy => by
          simp only [SimpleGraph.mem_neighborSet, hKR, not_exists, not_and]
          exact fun b' h => (hy b' h.symm).elim)]
      exact hK₂ b
  · -- the cut sets: the vertices of a subnetwork, or the image of a cut set of a subnetwork
    rw [tree_undirected_adj_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨a, a', rfl, rfl, hU⟩ | ⟨b, b', rfl, rfl, hU⟩
    · exact ⟨Set.range TreeVert.left, by simp, by simp, tree_cut_left⟩
    · refine ⟨Set.range TreeVert.left, by simp, by simp, fun x' y' hx' hy' h => ?_⟩
      rw [tree_cut_left x' y' hx' hy' h, Sym2.eq_swap]
    · exact ⟨Set.range TreeVert.right, by simp, by simp, tree_cut_right⟩
    · refine ⟨Set.range TreeVert.right, by simp, by simp, fun x' y' hx' hy' h => ?_⟩
      rw [tree_cut_right x' y' hx' hy' h, Sym2.eq_swap]
    · have hK' : ¬ K₁.Adj a a' := fun h => hxyK ((hKL a _).2 ⟨a', rfl, h⟩)
      obtain ⟨S₁, hr₁S, hS₁, hc₁⟩ := hcut₁ a a' hU hK'
      refine ⟨TreeVert.left '' S₁, by simp, ?_, crossing_lift (fun _ _ => hUL _ _)
        (P := {r₁}) tree_attach_left
        (fun a ha h => hr₁S (by rw [Set.mem_singleton_iff] at h; rwa [← h]))
        hc₁⟩
      simp only [Set.mem_image, TreeVert.left.injEq, exists_eq_right]
      exact hS₁
    · have hK' : ¬ K₂.Adj b b' := fun h => hxyK ((hKR b _).2 ⟨b', rfl, h⟩)
      obtain ⟨S₂, hr₂S, hS₂, hc₂⟩ := hcut₂ b b' hU hK'
      refine ⟨TreeVert.right '' S₂, by simp, ?_, crossing_lift (fun _ _ => hUR _ _)
        (P := {r₂}) tree_attach_right
        (fun b hb h => hr₂S (by rw [Set.mem_singleton_iff] at h; rwa [← h]))
        hc₂⟩
      simp only [Set.mem_image, TreeVert.right.injEq, exists_eq_right]
      exact hS₂


/-- The graph of a tree node on no cycle has the invariant when the graphs of its two
subnetworks have it, with distinct labels, and its two edges have positive lengths. -/
theorem isSubnet_tree (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂) (h₁ : G₁.IsSubnet r₁) (h₂ : G₂.IsSubnet r₂)
    (hdisj : ∀ a b x, G₁.label a = some x → G₂.label b = some x → False) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).IsSubnet .root := by
  have := h₁.finite
  have := h₂.finite
  have hr₁ : G₁.indeg r₁ = 0 := indeg_eq_zero_iff.2 h₁.not_adj_root
  have hr₂ : G₂.indeg r₂ = 0 := indeg_eq_zero_iff.2 h₂.not_adj_root
  -- the hybrid nodes are those of the subnetworks
  have hhybL : ∀ a, (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).IsHybrid (.left a) ↔ G₁.IsHybrid a := by
    intro a
    rw [IsHybrid, IsHybrid, tree_indeg_left, tree_outdeg_left]
    by_cases ha : a = r₁
    · subst ha
      simp [hr₁]
    · rw [optInd_some_of_ne (Ne.symm ha), add_zero]
  have hhybR : ∀ b, (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).IsHybrid (.right b) ↔ G₂.IsHybrid b := by
    intro b
    rw [IsHybrid, IsHybrid, tree_indeg_right, tree_outdeg_right]
    by_cases hb : b = r₂
    · subst hb
      simp [hr₂]
    · rw [optInd_some_of_ne (Ne.symm hb), add_zero]
  have hhyb0 : ¬ (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).IsHybrid .root := by
    rintro ⟨h, -⟩
    rw [indeg_eq_two_iff] at h
    obtain ⟨u, _, _, hu⟩ := h
    exact tree_not_adj_root u ((hu u).2 (Or.inl rfl))
  -- a hybrid node of a subnetwork is not its root
  have hne₁ : ∀ a, G₁.IsHybrid a → a ≠ r₁ := fun a ha h => by rw [h, IsHybrid, hr₁] at ha; omega
  have hne₂ : ∀ b, G₂.IsHybrid b → b ≠ r₂ := fun b hb h => by rw [h, IsHybrid, hr₂] at hb; omega
  obtain ⟨f₁, hf₁⟩ := h₁.height
  obtain ⟨f₂, hf₂⟩ := h₂.height
  refine
    { finite := inferInstance
      height := ⟨fun | .root => 0 | .left a => f₁ a + 1 | .right b => f₂ b + 1, ?_⟩
      not_adj_root := tree_not_adj_root
      outdeg_root := Or.inr tree_outdeg_root
      degrees := ?_
      len_pos := ?_
      inh_mem_Ioo := ?_
      inh_add_inh := ?_
      isSome_label_iff := ?_
      label_injective := ?_
      cycles := ?_ }
  · intro u v huv
    cases u <;> cases v <;> simp_all [tree]
  · intro v hv
    cases v with
    | root => exact (hv rfl).elim
    | left a =>
      rw [tree_indeg_left, tree_outdeg_left]
      by_cases ha : a = r₁
      · subst ha
        rw [hr₁, optInd_some_self]
        rcases h₁.outdeg_root with h | h <;> simp [DegOK, h]
      · rw [optInd_some_of_ne (Ne.symm ha), add_zero]
        exact h₁.degrees a ha
    | right b =>
      rw [tree_indeg_right, tree_outdeg_right]
      by_cases hb : b = r₂
      · subst hb
        rw [hr₂, optInd_some_self]
        rcases h₂.outdeg_root with h | h <;> simp [DegOK, h]
      · rw [optInd_some_of_ne (Ne.symm hb), add_zero]
        exact h₂.degrees b hb
  · intro u v huv
    cases u <;> cases v <;> simp_all [tree, h₁.len_pos, h₂.len_pos]
  · intro u v huv hv
    cases v with
    | root => exact (hhyb0 hv).elim
    | left a =>
      rw [hhybL] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (tree_adj_left_iff u a).1 huv
      · exact (hne₁ a hv h0).elim
      · exact h₁.inh_mem_Ioo u a hu hv
    | right b =>
      rw [hhybR] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (tree_adj_right_iff u b).1 huv
      · exact (hne₂ b hv h0).elim
      · exact h₂.inh_mem_Ioo u b hu hv
  · intro u u' v huv hu'v huu' hv
    cases v with
    | root => exact (hhyb0 hv).elim
    | left a =>
      rw [hhybL] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (tree_adj_left_iff u a).1 huv
      · exact (hne₁ a hv h0).elim
      obtain ⟨-, h0⟩ | ⟨u', rfl, hu'⟩ := (tree_adj_left_iff u' a).1 hu'v
      · exact (hne₁ a hv h0).elim
      exact h₁.inh_add_inh u u' a hu hu' (fun h => huu' (by rw [h])) hv
    | right b =>
      rw [hhybR] at hv
      obtain ⟨-, h0⟩ | ⟨u, rfl, hu⟩ := (tree_adj_right_iff u b).1 huv
      · exact (hne₂ b hv h0).elim
      obtain ⟨-, h0⟩ | ⟨u', rfl, hu'⟩ := (tree_adj_right_iff u' b).1 hu'v
      · exact (hne₂ b hv h0).elim
      exact h₂.inh_add_inh u u' b hu hu' (fun h => huu' (by rw [h])) hv
  · intro v
    cases v with
    | root =>
      rw [tree_outdeg_root]
      simp [tree]
    | left a =>
      rw [tree_outdeg_left]
      exact h₁.isSome_label_iff a
    | right b =>
      rw [tree_outdeg_right]
      exact h₂.isSome_label_iff b
  · intro u v x hu hv
    cases u with
    | root => simp [tree] at hu
    | left a =>
      cases v with
      | root => simp [tree] at hv
      | left a' => exact congrArg _ (h₁.label_injective a a' x hu hv)
      | right b => exact (hdisj a b x hu hv).elim
    | right b =>
      cases v with
      | root => simp [tree] at hv
      | left a => exact (hdisj a b x hv hu).elim
      | right b' => exact congrArg _ (h₂.label_injective b b' x hu hv)
  · exact tree_cycles h₁ h₂

end MetricDigraph

end Phylogenetics
