module

public import Phylogenetics.NMSC.Context
public import Phylogenetics.NMSC.Arms
public import Mathlib.Data.List.GetD
/-!
# The quartet CFs of the components of a cycle

Under the NMSC on a metric level-1 network `N`, the quartet CF of four taxa from distinct components
of a cycle `Ω` is the CF `cycleCF M` of the induced metric quarnet, where the metric cycle `M` has
the inheritance probability and the edge lengths of `Ω` (`Phylogenetics.nmsc_quartetCF`). The
induced metric quarnets, and the dependence of the quartet CFs on them only, are due to Baños
(2019); here the CFs are derived from the definition of the NMSC (`Phylogenetics.Net.geneTreeDist`).

The proof:
* `Phylogenetics.quartetCF_eq_sum_top` reduces the CF to the expected score of the forest at the top
  node of `Ω`;
* the components hanging from `Ω` (and the hybrid component) each send at most one lineage, which
  reaches the cycle unchanged (`Phylogenetics.Net.forestDist_of_card_le_one`); the lineage of the
  hybrid component takes the side of `γ` with probability `γ`
  (`Phylogenetics.Net.forestDist_cycle_of_single`);
* each side is then an arm of the displayed tree (`Phylogenetics.Side.forestDist_eq_armDist`), with
  the positions of the components and the edge lengths `Ω.edgeLen`, and
  `Phylogenetics.displayed_score` computes the expected score;
* the two displayed trees put the hybrid component at position `0` and `d`, as in `cycleCF`.

The bookkeeping between the positions of the components (`Ω.components`), the nodes of the two sides
and the edges of the cycle (`Ω.edges`) is in the lemmas `Phylogenetics.Net.Cycle.component_zero`,
`Phylogenetics.Net.Cycle.component_side₁`, `Phylogenetics.Net.Cycle.component_root`,
`Phylogenetics.Net.Cycle.component_side₂`, `Phylogenetics.Net.Cycle.size_of_top_eq`,
`Phylogenetics.Net.Cycle.size_of_top_ne`, `Phylogenetics.Net.Cycle.edgeLen_side₁` and the private
lemmas around them; the components are pairwise disjoint
(`Phylogenetics.Net.Cycle.component_disjoint`) because the leaves of a well-formed network have
distinct labels. -/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u

/-- The process along a side is the arm process of its nodes, listed from the bottom. -/
theorem Side.forestDist_eq_armDist {X : Type u} [DecidableEq X] (s : Fin 4 → X) (S : Side X)
    (F : Finset (Finset (Fin 4))) :
    S.forestDist s F = armDist (Pi.single F 1 ᵥ* kingmanTransition S.hybLen)
      (S.nodes.reverse.map fun n => (n.2.2.forestDist s ᵥ* kingmanTransition n.2.1, n.1)) := by
  match S with
  | .hyb ℓ =>
    simp only [Side.forestDist, Side.hybLen, Side.nodes, List.reverse_nil, List.map_nil, armDist,
      List.foldl_nil, single_one_vecMul, row_apply']
  | .node ℓ b N S =>
    rw [Side.forestDist]
    beta_reduce
    rw [Side.forestDist_eq_armDist s S F]
    simp only [Side.nodes, Side.hybLen, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, armDist, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ### Subnetworks -/

section Structure

variable {X : Type u}

mutual
/-- The leaves of a subnetwork are a sublist of the leaves of the network. -/
theorem Net.leaves_sublist_of_mem_subnets :
    ∀ {N M : Net X}, M ∈ N.subnets → M.leaves.Sublist N.leaves
  | .leaf x, M, h => by
    simp only [Net.subnets, List.mem_singleton] at h
    subst h
    exact List.Sublist.refl _
  | .tree ℓ₁ N₁ ℓ₂ N₂, M, h => by
    simp only [Net.subnets, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact List.Sublist.refl _
    · exact (Net.leaves_sublist_of_mem_subnets h).trans (by simp [Net.leaves])
    · exact (Net.leaves_sublist_of_mem_subnets h).trans (by simp [Net.leaves])
  | .cycle γ S₁ S₂ ℓ N, M, h => by
    simp only [Net.subnets, List.mem_cons, List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · exact List.Sublist.refl _
    · exact (Side.leaves_sublist_of_mem_subnets h).trans (by simp [Net.leaves])
    · exact (Side.leaves_sublist_of_mem_subnets h).trans (by simp [Net.leaves])
    · exact (Net.leaves_sublist_of_mem_subnets h).trans (by simp [Net.leaves])

/-- The leaves of a subnetwork hanging from a side are a sublist of the leaves of the side. -/
theorem Side.leaves_sublist_of_mem_subnets :
    ∀ {S : Side X} {M : Net X}, M ∈ S.subnets → M.leaves.Sublist S.leaves
  | .hyb ℓ, M, h => by simp [Side.subnets] at h
  | .node ℓ b N S, M, h => by
    simp only [Side.subnets, List.mem_append] at h
    rcases h with h | h
    · exact (Net.leaves_sublist_of_mem_subnets h).trans (by simp [Side.leaves])
    · exact (Side.leaves_sublist_of_mem_subnets h).trans (by simp [Side.leaves])
end

mutual
/-- The subnetworks of a metric network are metric. -/
theorem Net.isMetric_of_mem_subnets :
    ∀ {N M : Net X}, M ∈ N.subnets → N.IsMetric → M.IsMetric
  | .leaf x, M, h, _ => by
    simp only [Net.subnets, List.mem_singleton] at h
    subst h
    trivial
  | .tree ℓ₁ N₁ ℓ₂ N₂, M, h, hN => by
    simp only [Net.subnets, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hN
    · exact Net.isMetric_of_mem_subnets h hN.2.2.1
    · exact Net.isMetric_of_mem_subnets h hN.2.2.2
  | .cycle γ S₁ S₂ ℓ N, M, h, hN => by
    simp only [Net.subnets, List.mem_cons, List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · exact hN
    · exact Side.isMetric_of_mem_subnets h hN.2.2.2.1
    · exact Side.isMetric_of_mem_subnets h hN.2.2.2.2.1
    · exact Net.isMetric_of_mem_subnets h hN.2.2.2.2.2.1

/-- The subnetworks hanging from a metric side are metric. -/
theorem Side.isMetric_of_mem_subnets :
    ∀ {S : Side X} {M : Net X}, M ∈ S.subnets → S.IsMetric → M.IsMetric
  | .hyb ℓ, M, h, _ => by simp [Side.subnets] at h
  | .node ℓ b N S, M, h, hS => by
    simp only [Side.subnets, List.mem_append] at h
    rcases h with h | h
    · exact Net.isMetric_of_mem_subnets h hS.2.2.1
    · exact Side.isMetric_of_mem_subnets h hS.2.2.2
end

/-- The leaves below a side are those of the networks hanging from its nodes. -/
theorem Side.leaves_eq_flatten : ∀ S : Side X, S.leaves = (S.nodes.map fun n => n.2.2.leaves).flatten
  | .hyb _ => rfl
  | .node ℓ b N S => by simp [Side.leaves, Side.nodes, Side.leaves_eq_flatten S]

private theorem nc_side_isMetric_nodes :
    ∀ {S : Side X}, S.IsMetric → (∀ n ∈ S.nodes, 0 < n.1) ∧ 0 < S.hybLen
  | .hyb ℓ, h => ⟨by simp [Side.nodes], h⟩
  | .node ℓ b N S, h => by
    obtain ⟨h1, h2⟩ := nc_side_isMetric_nodes h.2.2.2
    refine ⟨?_, h2⟩
    intro n hn
    simp only [Side.nodes, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact h.1
    · exact h1 n hn

private theorem nc_pendant_sublist {S : Side X} {n : ℝ × ℝ × Net X} (hn : n ∈ S.nodes) :
    n.2.2.leaves.Sublist S.leaves := by
  rw [Side.leaves_eq_flatten]
  exact List.sublist_flatten_of_mem (List.mem_map_of_mem hn)

end Structure

/-! ### The edges of a cycle -/

section CycleEdges

variable {X : Type u} {N : Net X} (Ω : N.Cycle)

/-- The edges of the two sides of `Ω`, from the hybrid node up `side₁` and down `side₂`: the edges
of the cycle, before the two edges at the top node are merged when it is the root of `N`. -/
private def ncE : List ℝ :=
  [Ω.side₁.hybLen] ++ Ω.side₁.nodes.reverse.map (fun n => n.1) ++
    Ω.side₂.nodes.map (fun n => n.1) ++ [Ω.side₂.hybLen]

private theorem nc_edges_of_ne (h : Ω.top ≠ N) : Ω.edges = ncE Ω := by
  simp only [Net.Cycle.edges, ite_eq_right h]; rfl

private theorem nc_edges_of_eq (h : Ω.top = N) :
    Ω.edges = (ncE Ω).take Ω.side₁.nodes.length ++
      [(ncE Ω).getD Ω.side₁.nodes.length 0 + (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0] ++
        (ncE Ω).drop (Ω.side₁.nodes.length + 2) := by
  simp only [Net.Cycle.edges, ite_eq_left h]; rfl

private theorem ncE_length :
    (ncE Ω).length = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 2 := by
  simp [ncE]; omega

private theorem ncE_zero : (ncE Ω).getD 0 0 = Ω.side₁.hybLen := by simp [ncE]

private theorem ncE_side₁ {i : ℕ} (hi : i < Ω.side₁.nodes.length) :
    (ncE Ω).getD (i + 1) 0 = (Ω.side₁.nodes.reverse[i]'(by simpa using hi)).1 := by
  unfold ncE
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map]

private theorem ncE_side₂ {j : ℕ} (hj : j < Ω.side₂.nodes.length) :
    (ncE Ω).getD (Ω.side₁.nodes.length + 1 + j) 0 = (Ω.side₂.nodes[j]).1 := by
  unfold ncE
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  congr 2
  simp

private theorem ncE_last :
    (ncE Ω).getD (Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1) 0 = Ω.side₂.hybLen := by
  unfold ncE
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem nc_edgeLen_of_ne (h : Ω.top ≠ N) (m : ℕ) : Ω.edgeLen m = (ncE Ω).getD m 0 := by
  rw [Net.Cycle.edgeLen, nc_edges_of_ne Ω h]

private theorem nc_edgeLen_of_lt {m : ℕ} (hm : m < Ω.side₁.nodes.length) :
    Ω.edgeLen m = (ncE Ω).getD m 0 := by
  by_cases h : Ω.top = N
  · have hl := ncE_length Ω
    rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h, List.append_assoc,
      List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hm]
  · exact nc_edgeLen_of_ne Ω h m

private theorem nc_edgeLen_of_eq_p (h : Ω.top = N) :
    Ω.edgeLen Ω.side₁.nodes.length =
      (ncE Ω).getD Ω.side₁.nodes.length 0 + (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0 := by
  have hl := ncE_length Ω
  rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp), List.length_take, Nat.min_eq_left (by omega),
    Nat.sub_self]
  simp

private theorem nc_edgeLen_of_eq_of_gt (h : Ω.top = N) {m : ℕ}
    (hm : Ω.side₁.nodes.length < m) : Ω.edgeLen m = (ncE Ω).getD (m + 1) 0 := by
  have hl := ncE_length Ω
  rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  simp; omega

/-- For `1 ≤ m < p`, the length `Ω.edgeLen m` of the edge of the cycle between the positions `m`
and `m + 1` is the length of the edge above the node at height `m` of `side₁` (counted from the
hybrid node; the component at position `m` hangs from that node). -/
theorem Net.Cycle.edgeLen_side₁ {m : ℕ} (hm1 : 1 ≤ m) (hm : m < Ω.side₁.nodes.length) :
    Ω.edgeLen m = (Ω.side₁.nodes.reverse[m - 1]'(by simp; omega)).1 := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [nc_edgeLen_of_lt Ω hm, ncE_side₁ Ω (by omega)]
  rfl

end CycleEdges

/-! ### The components of a cycle -/

section CycleComponents

variable {X : Type u} [DecidableEq X] {N : Net X} (Ω : N.Cycle)

private theorem nc_components_of_eq (h : Ω.top = N) :
    Ω.components = [Ω.below.taxa] ++ Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
      Ω.side₂.nodes.map (fun n => n.2.2.taxa) := by
  simp only [Net.Cycle.components, ite_eq_left h, List.append_nil]

private theorem nc_components_of_ne (h : Ω.top ≠ N) :
    Ω.components = [Ω.below.taxa] ++ Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
      [N.taxa \ Ω.top.taxa] ++ Ω.side₂.nodes.map (fun n => n.2.2.taxa) := by
  simp only [Net.Cycle.components, ite_eq_right h]

/-- The size of a cycle whose top node is the root of the network. -/
theorem Net.Cycle.size_of_top_eq (h : Ω.top = N) :
    Ω.size = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 := by
  rw [Net.Cycle.size, nc_components_of_eq Ω h]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_reverse]
  omega

/-- The size of a cycle whose top node is not the root of the network. -/
theorem Net.Cycle.size_of_top_ne (h : Ω.top ≠ N) :
    Ω.size = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 2 := by
  rw [Net.Cycle.size, nc_components_of_ne Ω h]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_reverse]
  omega

/-- The component at position `0` is the hybrid component. -/
theorem Net.Cycle.component_zero : Ω.component 0 = Ω.below.taxa := by
  simp [Net.Cycle.component, Net.Cycle.components]

/-- The component at position `i + 1 ≤ p` hangs from the node at height `i + 1` of `side₁`. -/
theorem Net.Cycle.component_side₁ {i : ℕ} (hi : i < Ω.side₁.nodes.length) :
    Ω.component (i + 1) = (Ω.side₁.nodes.reverse[i]'(by simpa using hi)).2.2.taxa := by
  have hA : i < (Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa)).length := by simpa using hi
  unfold Net.Cycle.component Net.Cycle.components
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [List.getD_cons_succ, List.getD_append _ _ _ _ hA, List.getD_eq_getElem _ _ hA,
    List.getElem_map]

/-- The component at position `p + 1` is the component of the root, if the top node of the cycle
is not the root. -/
theorem Net.Cycle.component_root (h : Ω.top ≠ N) :
    Ω.component (Ω.side₁.nodes.length + 1) = N.taxa \ Ω.top.taxa := by
  rw [Net.Cycle.component, nc_components_of_ne Ω h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The component at position `d - (i + 1)` hangs from the node at height `i + 1` of `side₂`
(counted from the hybrid node). -/
theorem Net.Cycle.component_side₂ {i : ℕ} (hi : i < Ω.side₂.nodes.length) :
    Ω.component (Ω.size - (i + 1)) = (Ω.side₂.nodes.reverse[i]'(by simpa using hi)).2.2.taxa := by
  obtain ⟨pre, hpre⟩ :
      ∃ pre, Ω.components = pre ++ Ω.side₂.nodes.map (fun n => n.2.2.taxa) := ⟨_, rfl⟩
  have hs : Ω.size = pre.length + Ω.side₂.nodes.length := by rw [Net.Cycle.size, hpre]; simp
  rw [Net.Cycle.component, hpre, List.getD_append_right _ _ _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_reverse]
  exact congrArg (fun n : ℝ × ℝ × Net X => n.2.2.taxa) (getElem_congr_idx (c := Ω.side₂.nodes)
    (show Ω.size - (i + 1) - pre.length = Ω.side₂.nodes.length - 1 - i by omega))

private theorem nc_component_of_le {i : ℕ} (hi : Ω.size ≤ i) : Ω.component i = ∅ :=
  List.getD_eq_default _ _ hi

omit [DecidableEq X] in
private theorem nc_top_leaves :
    Ω.top.leaves = Ω.side₁.leaves ++ Ω.side₂.leaves ++ Ω.below.leaves := rfl

omit [DecidableEq X] in
private theorem nc_top_sublist : Ω.top.leaves.Sublist N.leaves :=
  Net.leaves_sublist_of_mem_subnets Ω.mem

omit [DecidableEq X] in
private theorem nc_below_sublist : Ω.below.leaves.Sublist N.leaves :=
  (by rw [nc_top_leaves]; exact List.sublist_append_right _ _ : Ω.below.leaves.Sublist _).trans
    (nc_top_sublist Ω)

omit [DecidableEq X] in
private theorem nc_pendant₁_sublist {n : ℝ × ℝ × Net X} (hn : n ∈ Ω.side₁.nodes) :
    n.2.2.leaves.Sublist Ω.top.leaves :=
  (nc_pendant_sublist hn).trans (by
    rw [nc_top_leaves]; exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _))

omit [DecidableEq X] in
private theorem nc_pendant₂_sublist {n : ℝ × ℝ × Net X} (hn : n ∈ Ω.side₂.nodes) :
    n.2.2.leaves.Sublist Ω.top.leaves :=
  (nc_pendant_sublist hn).trans (by
    rw [nc_top_leaves]; exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _))

/-- The networks hanging below the cycle: the network below the hybrid node and the pendant
ones. -/
private def ncT : List (Net X) :=
  [Ω.below] ++ Ω.side₁.nodes.reverse.map (fun n => n.2.2) ++ Ω.side₂.nodes.map (fun n => n.2.2)

omit [DecidableEq X] in
private theorem ncT_perm : ((ncT Ω).map Net.leaves).flatten.Perm Ω.top.leaves := by
  rw [nc_top_leaves, Side.leaves_eq_flatten, Side.leaves_eq_flatten]
  simp only [ncT, List.map_append, List.flatten_append, List.map_reverse, List.map_map,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine (List.Perm.append_right _ (List.Perm.append_left _
    (List.Perm.flatten (List.reverse_perm _)))).trans ?_
  rw [List.append_assoc]
  exact List.perm_append_comm

private theorem ncT_taxa_subset {M : Net X} (hM : M ∈ ncT Ω) : M.taxa ⊆ Ω.top.taxa := by
  intro y hy
  simp only [Net.taxa, List.mem_toFinset] at hy ⊢
  exact (ncT_perm Ω).subset (List.mem_flatten.2 ⟨M.leaves, List.mem_map_of_mem hM, hy⟩)

private theorem ncT_pairwise (hN : N.leaves.Nodup) :
    ((ncT Ω).map Net.taxa).Pairwise Disjoint := by
  have h1 : ((ncT Ω).map Net.leaves).flatten.Nodup :=
    (ncT_perm Ω).nodup_iff.2 ((nc_top_sublist Ω).nodup hN)
  have h2 := (List.nodup_flatten.1 h1).2
  rw [List.pairwise_map] at h2 ⊢
  exact h2.imp fun h => List.disjoint_toFinset_iff_disjoint.2 h

private theorem nc_components_pairwise (hN : N.leaves.Nodup) :
    Ω.components.Pairwise Disjoint := by
  have hT := ncT_pairwise Ω hN
  have hTeq : (ncT Ω).map Net.taxa = [Ω.below.taxa] ++
      Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
        Ω.side₂.nodes.map (fun n => n.2.2.taxa) := by
    simp [ncT, Function.comp_def]
  by_cases h : Ω.top = N
  · rw [nc_components_of_eq Ω h, ← hTeq]
    exact hT
  · have hperm : ([Ω.below.taxa] ++ Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
        [N.taxa \ Ω.top.taxa] ++ Ω.side₂.nodes.map (fun n => n.2.2.taxa)).Perm
        ((N.taxa \ Ω.top.taxa) :: ([Ω.below.taxa] ++
          Ω.side₁.nodes.reverse.map (fun n => n.2.2.taxa) ++
            Ω.side₂.nodes.map (fun n => n.2.2.taxa))) := by
      rw [List.append_assoc _ [N.taxa \ Ω.top.taxa]]
      exact List.perm_middle
    rw [nc_components_of_ne Ω h, List.Perm.pairwise_iff (R := Disjoint) (fun h => h.symm) hperm,
      List.pairwise_cons, ← hTeq]
    refine ⟨fun c hc => ?_, hT⟩
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hc
    exact sdiff_disjoint.mono_right (ncT_taxa_subset Ω hM)

/-- The components of a cycle of a network with distinct leaf labels are pairwise disjoint. -/
theorem Net.Cycle.component_disjoint (hN : N.leaves.Nodup) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Ω.component i) (Ω.component j) := by
  have hpw := List.pairwise_iff_getElem.1 (nc_components_pairwise Ω hN)
  unfold Net.Cycle.component
  rcases lt_or_ge i Ω.components.length with hi | hi
  · rcases lt_or_ge j Ω.components.length with hj | hj
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hpw i j hi hj h
      · exact (hpw j i hj hi h).symm
    · rw [List.getD_eq_default _ _ hj]; exact disjoint_empty_right _
  · rw [List.getD_eq_default _ _ hi]; exact disjoint_empty_left _

private theorem nc_top_taxa_subset : Ω.top.taxa ⊆ N.taxa := fun y hy => by
  simp only [Net.taxa, List.mem_toFinset] at hy ⊢
  exact (nc_top_sublist Ω).subset hy

/-- Every component except the component of the root lies below the top node of the cycle. -/
private theorem nc_component_subset_top {i : ℕ}
    (hi : Ω.top = N ∨ i ≠ Ω.side₁.nodes.length + 1) : Ω.component i ⊆ Ω.top.taxa := by
  have hsub : ∀ M : Net X, M.leaves.Sublist Ω.top.leaves → M.taxa ⊆ Ω.top.taxa :=
    fun M hM y hy => by
      simp only [Net.taxa, List.mem_toFinset] at hy ⊢
      exact hM.subset hy
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [Net.Cycle.component_zero]
    exact hsub _ (by rw [nc_top_leaves]; exact List.sublist_append_right _ _)
  by_cases hip : i ≤ Ω.side₁.nodes.length
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Net.Cycle.component_side₁ Ω (by omega)]
    exact hsub _ (nc_pendant₁_sublist Ω (List.mem_reverse.1 (List.getElem_mem _)))
  by_cases hid : Ω.size ≤ i
  · rw [nc_component_of_le Ω hid]; exact empty_subset _
  have hq : Ω.size - 1 - i < Ω.side₂.nodes.length := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h] at hid ⊢; omega
    · have := hi.resolve_left h
      rw [Net.Cycle.size_of_top_ne Ω h] at hid ⊢; omega
  have := Net.Cycle.component_side₂ Ω hq
  rw [show Ω.size - (Ω.size - 1 - i + 1) = i by omega] at this
  rw [this]
  exact hsub _ (nc_pendant₂_sublist Ω (List.mem_reverse.1 (List.getElem_mem _)))

private theorem nc_component_subset (i : ℕ) : Ω.component i ⊆ N.taxa := by
  by_cases h : Ω.top ≠ N ∧ i = Ω.side₁.nodes.length + 1
  · rw [h.2, Net.Cycle.component_root Ω h.1]; exact sdiff_subset
  · exact (nc_component_subset_top Ω (by tauto)).trans (nc_top_taxa_subset Ω)

end CycleComponents

/-- A cycle of a metric network has a metric cycle with its inheritance probability and edge
lengths. -/
theorem Net.Cycle.exists_metricCycle {X : Type u} [DecidableEq X] {N : Net X}
    (hN : N.WellFormed) (Ω : N.Cycle) :
    ∃ M : MetricCycle Ω.size, M.γ = Ω.γ ∧ ∀ m, 1 ≤ m → m ≤ Ω.size - 2 → M.w m = Ω.edgeLen m := by
  have hmet : Ω.top.IsMetric := Net.isMetric_of_mem_subnets Ω.mem hN.1
  obtain ⟨hγ0, hγ1, -, hS₁, hS₂, -, -⟩ := hmet
  -- all the edges of the two sides have positive lengths
  have hE : ∀ y ∈ ncE Ω, 0 < y := by
    intro y hy
    simp only [ncE, List.mem_append, List.mem_singleton, List.mem_map, List.mem_reverse] at hy
    rcases hy with ((rfl | ⟨n, hn, rfl⟩) | ⟨n, hn, rfl⟩) | rfl
    · exact (nc_side_isMetric_nodes hS₁).2
    · exact (nc_side_isMetric_nodes hS₁).1 n hn
    · exact (nc_side_isMetric_nodes hS₂).1 n hn
    · exact (nc_side_isMetric_nodes hS₂).2
  have hEm : ∀ m, m < (ncE Ω).length → 0 < (ncE Ω).getD m 0 := fun m hm => by
    rw [List.getD_eq_getElem _ _ hm]; exact hE _ (List.getElem_mem hm)
  have hl := ncE_length Ω
  refine ⟨⟨Ω.γ, Ω.edgeLen, hγ0, hγ1, fun m hm1 hm2 => ?_⟩, rfl, fun _ _ _ => rfl⟩
  by_cases h : Ω.top = N
  · have hs := Net.Cycle.size_of_top_eq Ω h
    rcases lt_trichotomy m Ω.side₁.nodes.length with hm | rfl | hm
    · rw [nc_edgeLen_of_lt Ω hm]; exact hEm _ (by omega)
    · rw [nc_edgeLen_of_eq_p Ω h]; exact add_pos (hEm _ (by omega)) (hEm _ (by omega))
    · rw [nc_edgeLen_of_eq_of_gt Ω h hm]; exact hEm _ (by omega)
  · have hs := Net.Cycle.size_of_top_ne Ω h
    rw [nc_edgeLen_of_ne Ω h]; exact hEm _ (by omega)

/-! ### The sides as arms of the displayed trees -/

section Arms

variable {X : Type u} [DecidableEq X] {N : Net X} (Ω : N.Cycle)

/-- The length of the top edge of a side. -/
private def ncTopLen {Y : Type u} : Side Y → ℝ
  | .hyb ℓ => ℓ
  | .node ℓ _ _ _ => ℓ

omit [DecidableEq X] in
private theorem ncTopLen_of_nil {S : Side X} (h : S.nodes = []) : ncTopLen S = S.hybLen := by
  cases S with
  | hyb ℓ => rfl
  | node ℓ b M S => simp [Side.nodes] at h

omit [DecidableEq X] in
private theorem ncTopLen_of_pos {S : Side X} (h : 0 < S.nodes.length) :
    ncTopLen S = (S.nodes[0]'h).1 := by
  cases S with
  | hyb ℓ => simp [Side.nodes] at h
  | node ℓ b M S => rfl

omit [DecidableEq X] in
private theorem ncE_p : (ncE Ω).getD Ω.side₁.nodes.length 0 = ncTopLen Ω.side₁ := by
  rcases Nat.eq_zero_or_pos Ω.side₁.nodes.length with hp | hp
  · rw [hp, ncE_zero, ncTopLen_of_nil (List.length_eq_zero_iff.1 hp)]
  · obtain ⟨i, hi⟩ : ∃ i, Ω.side₁.nodes.length = i + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
    rw [hi, ncE_side₁ Ω (by omega), ncTopLen_of_pos hp, List.getElem_reverse]
    exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))

omit [DecidableEq X] in
private theorem ncE_p1 : (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0 = ncTopLen Ω.side₂ := by
  rcases Nat.eq_zero_or_pos Ω.side₂.nodes.length with hq | hq
  · have := ncE_last Ω
    rw [hq, add_zero] at this
    rw [this, ncTopLen_of_nil (List.length_eq_zero_iff.1 hq)]
  · have := ncE_side₂ Ω (j := 0) hq
    rw [add_zero] at this
    rw [this, ncTopLen_of_pos hq]

private theorem nc_card_filter_le_one {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ) :
    #(univ.filter fun l => pos l = h) ≤ 1 :=
  card_le_one.2 fun _ ha _ hb => hinj ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)

private theorem nc_card_roots_posForest {pos : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (h : ℕ) : #(roots (posForest pos h)) ≤ 1 :=
  (card_le_card (filter_subset _ _)).trans (card_image_le.trans (nc_card_filter_le_one hinj h))

private theorem nc_single_posForest {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ)
    (t : ℝ) :
    Pi.single (posForest pos h) 1 ᵥ* kingmanTransition t = Pi.single (posForest pos h) 1 :=
  single_vecMul_kingmanTransition (isGood_singletons _).1 (nc_card_roots_posForest hinj h) t

private theorem nc_posForest_cases {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ) :
    posForest pos h = ∅ ∨ ∃ l, posForest pos h = {{l}} := by
  obtain ⟨l, hl⟩ := card_le_one_iff_subset_singleton.1 (nc_card_filter_le_one hinj h)
  rcases subset_singleton_iff.1 hl with he | he
  · left; unfold posForest; rw [he, image_empty]
  · right; exact ⟨l, by unfold posForest; rw [he, image_singleton]⟩

private theorem nc_posForest_congr {pos pos' : Fin 4 → ℕ} {h : ℕ}
    (hpos : ∀ l, pos' l = h ↔ pos l = h) : posForest pos' h = posForest pos h := by
  unfold posForest
  congr 1
  ext l
  simp [hpos]

/-- A network hanging from the cycle (or below its hybrid node), the component at position `h`:
at most one lineage is sampled from it, and it reaches the cycle unchanged. -/
private theorem nc_pendant_dist (s : Fin 4 → X) {pos : Fin 4 → ℕ}
    (hinj : Function.Injective pos) (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    {M : Net X} {h : ℕ} (hMh : Ω.component h = M.taxa) (t : ℝ) :
    M.forestDist s ᵥ* kingmanTransition t = Pi.single (posForest pos h) 1 := by
  have hT : (univ.filter fun l => s l ∈ M.taxa) = univ.filter fun l => pos l = h := by
    ext l
    simp only [mem_filter, mem_univ, true_and, ← hMh, hcomp]
  rw [Net.forestDist_of_card_le_one M s (hT ▸ nc_card_filter_le_one hinj h)]
  have hF : M.sampledForest s = posForest pos h := by
    unfold Net.sampledForest posForest
    rw [hT]
  rw [hF, nc_single_posForest hinj h t]

/-- The side `side₁` is the left arm `0, 1, …, p` of the displayed tree. -/
private theorem nc_side₁_eq_leftArm (s : Fin 4 → X)
    {pos pos' : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    (hpos : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h)) :
    Ω.side₁.forestDist s (posForest pos' 0) =
      leftArm Ω.side₁.nodes.length Ω.edgeLen (ncTopLen Ω.side₁) pos' := by
  have hpd : Ω.side₁.nodes.length < Ω.size := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h]; omega
    · rw [Net.Cycle.size_of_top_ne Ω h]; omega
  rw [Side.forestDist_eq_armDist]
  unfold leftArm
  congr 1
  · congr 2
    split_ifs with hp
    · exact (ncTopLen_of_nil (List.length_eq_zero_iff.1 hp)).symm
    · rw [nc_edgeLen_of_lt Ω (Nat.pos_of_ne_zero hp), ncE_zero]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < Ω.side₁.nodes.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_side₁ Ω hi),
        nc_posForest_congr (fun l => hpos l (i + 1) (by omega) (by omega))]
    · dsimp only
      split_ifs with hip
      · rw [ncTopLen_of_pos (by omega), List.getElem_reverse]
        exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))
      · rw [nc_edgeLen_of_lt Ω (by omega), ncE_side₁ Ω hi]

/-- The side `side₂` is the right arm `d, d - 1, …, d - q` of the displayed tree. -/
private theorem nc_side₂_eq_rightArm (s : Fin 4 → X)
    {pos pos' : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    (hpos : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h)) :
    Ω.side₂.forestDist s (posForest pos' Ω.size) =
      rightArm Ω.size Ω.side₂.nodes.length Ω.edgeLen (ncTopLen Ω.side₂) pos' := by
  have hqd : Ω.side₂.nodes.length + Ω.side₁.nodes.length + 1 ≤ Ω.size := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h]; omega
    · rw [Net.Cycle.size_of_top_ne Ω h]; omega
  rw [Side.forestDist_eq_armDist]
  unfold rightArm
  congr 1
  · congr 2
    split_ifs with hq
    · exact (ncTopLen_of_nil (List.length_eq_zero_iff.1 hq)).symm
    · by_cases h : Ω.top = N
      · have hs := Net.Cycle.size_of_top_eq Ω h
        have hm : Ω.side₁.nodes.length < Ω.size - 1 := by omega
        rw [nc_edgeLen_of_eq_of_gt Ω h hm,
          show Ω.size - 1 + 1 = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 by omega,
          ncE_last]
      · have hs := Net.Cycle.size_of_top_ne Ω h
        rw [nc_edgeLen_of_ne Ω h,
          show Ω.size - 1 = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 by omega, ncE_last]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < Ω.side₂.nodes.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_side₂ Ω hi),
        nc_posForest_congr (fun l => hpos l (Ω.size - (i + 1)) (by omega) (by omega))]
    · dsimp only
      split_ifs with hiq
      · rw [ncTopLen_of_pos (by omega), List.getElem_reverse]
        exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))
      · rw [List.getElem_reverse]
        have hj : Ω.side₂.nodes.length - 1 - i < Ω.side₂.nodes.length := by omega
        by_cases h : Ω.top = N
        · have hs := Net.Cycle.size_of_top_eq Ω h
          have hm : Ω.side₁.nodes.length < Ω.size - (i + 1) - 1 := by omega
          rw [nc_edgeLen_of_eq_of_gt Ω h hm,
            show Ω.size - (i + 1) - 1 + 1 =
              Ω.side₁.nodes.length + 1 + (Ω.side₂.nodes.length - 1 - i) by omega,
            ncE_side₂ Ω hj]
        · have hs := Net.Cycle.size_of_top_ne Ω h
          rw [nc_edgeLen_of_ne Ω h,
            show Ω.size - (i + 1) - 1 =
              Ω.side₁.nodes.length + 1 + (Ω.side₂.nodes.length - 1 - i) by omega,
            ncE_side₂ Ω hj]

/-- The shape of the displayed trees of `Ω`, as `Phylogenetics.displayed_score` takes it: the top
node is a node of the path (the root component hangs there) or lies inside its edge `p`. -/
private theorem nc_rv : ∃ rv : Bool,
    Ω.size = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 + (if rv then 1 else 0) ∧
    (if rv then ncTopLen Ω.side₁ = Ω.edgeLen Ω.side₁.nodes.length ∧
        ncTopLen Ω.side₂ = Ω.edgeLen (Ω.side₁.nodes.length + 1)
      else ncTopLen Ω.side₁ + ncTopLen Ω.side₂ = Ω.edgeLen Ω.side₁.nodes.length) := by
  by_cases h : Ω.top = N
  · refine ⟨false, by simp [Net.Cycle.size_of_top_eq Ω h], ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [nc_edgeLen_of_eq_p Ω h, ncE_p, ncE_p1]
  · refine ⟨true, by simp [Net.Cycle.size_of_top_ne Ω h], ?_⟩
    simp only [ite_true]
    rw [nc_edgeLen_of_ne Ω h, nc_edgeLen_of_ne Ω h, ncE_p, ncE_p1]
    exact ⟨rfl, rfl⟩

/-- The expected score at the top node of the cycle, for one lineage from each of four distinct
components: the two placements of the lineage of the hybrid component. -/
private theorem nc_sum_top (hN : N.leaves.Nodup) (s : Fin 4 → X) {pos : Fin 4 → ℕ}
    (hinj : Function.Injective pos) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) :
    ∑ F, Ω.top.forestDist s F * quartetScore F =
      Ω.γ * pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) +
        (1 - Ω.γ) * pathCF Ω.edgeLen (toRightEnd Ω.size (pos 0)) (toRightEnd Ω.size (pos 1))
          (toRightEnd Ω.size (pos 2)) (toRightEnd Ω.size (pos 3)) := by
  have hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h := fun l h =>
    ⟨fun hm => by
      by_contra hne
      exact disjoint_left.1 (Net.Cycle.component_disjoint Ω hN hne) (hs l) hm,
     fun he => he ▸ hs l⟩
  -- the placement of the lineage of the hybrid component on the side of `C_{d-1}`
  set pos' : Fin 4 → ℕ := fun l => toRightEnd Ω.size (pos l) with hpos'
  have hinj' : Function.Injective pos' := by
    intro a b hab
    apply hinj
    have ha := hlt a
    have hb := hlt b
    simp only [hpos', toRightEnd] at hab
    split_ifs at hab <;> omega
  have hpos'h : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h) := by
    intro l h h1 h2
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  have hle' : ∀ l, pos' l ≤ Ω.size := by
    intro l
    have := hlt l
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  -- the forests entering the two arms at their lower ends
  have hE0 : posForest pos' 0 = ∅ := by
    unfold posForest
    rw [filter_false_of_mem (fun l _ => ?_), image_empty]
    have := hlt l
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  have hEd : posForest pos Ω.size = ∅ := by
    unfold posForest
    rw [filter_false_of_mem (fun l _ => (hlt l).ne), image_empty]
  have hEd' : posForest pos' Ω.size = posForest pos 0 := by
    unfold posForest
    congr 1
    ext l
    have := hlt l
    simp only [mem_filter, mem_univ, true_and, hpos', toRightEnd]
    split_ifs <;> omega
  -- the cycle: the hybrid component sends at most one lineage
  have hbelow : Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ =
      Pi.single (posForest pos 0) 1 :=
    nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_zero Ω) Ω.ℓ
  have htop : Ω.top.forestDist s =
      Ω.γ • forestUnion (Ω.side₁.forestDist s (posForest pos 0)) (Ω.side₂.forestDist s ∅) +
        (1 - Ω.γ) • forestUnion (Ω.side₁.forestDist s ∅)
          (Ω.side₂.forestDist s (posForest pos 0)) :=
    Net.forestDist_cycle_of_single s Ω.γ Ω.ℓ Ω.side₁ Ω.side₂ Ω.below _
      (nc_posForest_cases hinj 0) hbelow
  -- the two displayed trees
  obtain ⟨rv, hdrv, ht⟩ := nc_rv Ω
  have A1 := displayed_score _ _ _ rv hdrv _ _ _ ht pos hinj (fun l => (hlt l).le)
  rw [← nc_side₁_eq_leftArm Ω s hinj hcomp (fun _ _ _ _ => Iff.rfl),
    ← nc_side₂_eq_rightArm Ω s hinj hcomp (fun _ _ _ _ => Iff.rfl), hEd] at A1
  have A2 := displayed_score _ _ _ rv hdrv _ _ _ ht pos' hinj' hle'
  rw [← nc_side₁_eq_leftArm Ω s hinj hcomp hpos'h,
    ← nc_side₂_eq_rightArm Ω s hinj hcomp hpos'h, hE0, hEd'] at A2
  rw [htop]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, sum_add_distrib,
    ← mul_sum]
  rw [A1, A2]

end Arms

/-- `pathCF w` at distinct positions in `[0, d]` reads `w` only on `[1, d - 2]`, between the two
middle positions. -/
private theorem nc_pathCF_congr {w w' : ℕ → ℝ} {d a b c e : ℕ} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : a ≤ d) (hb : b ≤ d)
    (hc : c ≤ d) (he : e ≤ d) (hw : ∀ m, 1 ≤ m → m ≤ d - 2 → w m = w' m) :
    pathCF w a b c e = pathCF w' a b c e := by
  simp only [pathCF, pathLen]
  rw [sum_congr rfl fun m hm => hw m (by rw [mem_Ico] at hm; omega) (by rw [mem_Ico] at hm; omega)]

/-- **The quartet CFs of the components of a cycle** (the induced metric quarnets of Baños 2019):
under the NMSC on a metric level-1 network `N`, the component CFs of a cycle `Ω`, for any choice
`x` of one taxon per component, are the CFs of the induced metric quarnets, those of the metric
cycle `M` with the inheritance probability and edge lengths of `Ω`. -/
theorem nmsc_quartetCF {X : Type u} [DecidableEq X] (N : Net X) (hN : N.WellFormed)
    (Ω : N.Cycle) {d : ℕ} (hΩ : Ω.size = d) (M : MetricCycle d) (hγ : M.γ = Ω.γ)
    (hw : ∀ m, 1 ≤ m → m ≤ d - 2 → M.w m = Ω.edgeLen m) (ord : Equiv.Perm (Fin d))
    (x : Fin d → X) (hx : ∀ i : Fin d, x (ord i) ∈ Ω.component i) :
    NMSCQuartetCF M ord (N.componentCF x) := by
  subst hΩ
  intro a b c e hab hac hae hbc hbe hce
  -- the lineages `0, 1, 2, 3`, their taxa `s` and the positions `pos` of their components
  set v : Fin 4 → Fin Ω.size := ![a, b, c, e] with hv
  have hvinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v, eq_comm]
  set pos : Fin 4 → ℕ := fun l => (ord.symm (v l) : ℕ) with hpos
  set s : Fin 4 → X := fun l => x (v l) with hsdef
  have hinj : Function.Injective pos := fun i j h => hvinj (ord.symm.injective (Fin.ext h))
  have hlt : ∀ l, pos l < Ω.size := fun l => (ord.symm (v l)).isLt
  have hs : ∀ l, s l ∈ Ω.component (pos l) := fun l => by
    have := hx (ord.symm (v l))
    rwa [Equiv.apply_symm_apply] at this
  have hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h := fun l h =>
    ⟨fun hm => by
      by_contra hne
      exact disjoint_left.1 (Net.Cycle.component_disjoint Ω hN.2 hne) (hs l) hm,
     fun he => he ▸ hs l⟩
  -- the hypotheses of `quartetCF_eq_sum_top`: at most one taxon in the component of the root
  have hsinj : Function.Injective s := fun i j h => hinj ((hcomp i (pos j)).1 (h ▸ hs j))
  have hsN : ∀ l, s l ∈ N.taxa := fun l => nc_component_subset Ω _ (hs l)
  have h3 : 3 ≤ #(univ.filter fun l => s l ∈ Ω.top.taxa) := by
    have hout : #(univ.filter fun l => ¬ s l ∈ Ω.top.taxa) ≤ 1 := by
      refine (card_le_card fun l hl => ?_).trans
        (nc_card_filter_le_one hinj (Ω.side₁.nodes.length + 1))
      simp only [mem_filter, mem_univ, true_and] at hl ⊢
      by_contra hne
      exact hl (nc_component_subset_top Ω (Or.inr hne) (hs l))
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin 4)))
      (fun l => s l ∈ Ω.top.taxa)
    rw [card_univ, Fintype.card_fin] at this
    omega
  have key : N.quartetCF (s 0) (s 1) (s 2) (s 3) =
      cycleCF M (pos 0) (pos 1) (pos 2) (pos 3) := by
    rw [quartetCF_eq_sum_top N hN.2 Ω s hsN h3, nc_sum_top Ω hN.2 s hinj hlt hs]
    -- `M.w` and `Ω.edgeLen` agree where `pathCF` reads them
    have hd : ∀ {i j : Fin 4}, i ≠ j → pos i ≠ pos j := fun h h' => h (hinj h')
    have hpc : pathCF M.w (pos 0) (pos 1) (pos 2) (pos 3) =
        pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) :=
      nc_pathCF_congr (hd (by decide)) (hd (by decide)) (hd (by decide)) (hd (by decide))
        (hd (by decide)) (hd (by decide)) (hlt 0).le (hlt 1).le (hlt 2).le (hlt 3).le hw
    have hd' : ∀ {i j : Fin 4}, i ≠ j →
        toRightEnd Ω.size (pos i) ≠ toRightEnd Ω.size (pos j) := fun {i j} h h' => by
      have := hd h
      have := hlt i
      have := hlt j
      unfold toRightEnd at h'
      split_ifs at h' <;> omega
    have hle : ∀ l, toRightEnd Ω.size (pos l) ≤ Ω.size := fun l => by
      have := hlt l
      unfold toRightEnd
      split_ifs <;> omega
    have hpc' : pathCF M.w (toRightEnd Ω.size (pos 0)) (toRightEnd Ω.size (pos 1))
        (toRightEnd Ω.size (pos 2)) (toRightEnd Ω.size (pos 3)) =
        pathCF Ω.edgeLen (toRightEnd Ω.size (pos 0)) (toRightEnd Ω.size (pos 1))
          (toRightEnd Ω.size (pos 2)) (toRightEnd Ω.size (pos 3)) :=
      nc_pathCF_congr (hd' (by decide)) (hd' (by decide)) (hd' (by decide)) (hd' (by decide))
        (hd' (by decide)) (hd' (by decide)) (hle 0) (hle 1) (hle 2) (hle 3) hw
    unfold cycleCF
    rw [hγ]
    split_ifs with h0
    · rw [hpc, hpc']
    · -- no taxon in the hybrid component: the two displayed trees give the same CF
      have htre : ∀ a : ℕ, a ≠ 0 → toRightEnd Ω.size a = a := fun a ha => by
        unfold toRightEnd
        exact ite_eq_right ha
      simp only [not_or] at h0
      rw [htre _ h0.1, htre _ h0.2.1, htre _ h0.2.2.1, htre _ h0.2.2.2, hpc]
      ring
  exact key

end Phylogenetics
