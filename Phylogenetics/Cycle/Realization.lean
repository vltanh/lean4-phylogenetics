module

public import Phylogenetics.NMSC.Cycle
/-!
# Every metric cycle is a cycle of a network

`Phylogenetics.Net.Cycle.exists_metricCycle` reads off the metric cycle of a cycle of a network: its
inheritance probability and edge lengths; so the component CFs of a cycle with `d` components are
given by the formulas `Phylogenetics.cycleCF` of a metric `d`-cycle
(`Phylogenetics.Net.Cycle.exists_nmscQuartetCF`). Conversely, every metric cycle with `d ≥ 3`
components is the cycle of a well-formed network whose taxa are its components, one taxon per
component (`Phylogenetics.MetricCycle.exists_net`), and whose component CFs are given by the
formulas `cycleCF` of that metric cycle (`Phylogenetics.MetricCycle.exists_net_nmscQuartetCF`).
The network is the cycle itself: the side of `C₁` carries the pendant leaves `1, …, d - 1` with the
given edge lengths, the other side is the hybrid edge, and the leaf `0` hangs below the hybrid node.
So an explicit metric cycle, for instance a counterexample about the CF formulas, is the cycle of
a network with the same component CFs. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u

/-! ### The side of `C₁` -/

/-- A side with `k` nodes: the node at height `h` (counted from the hybrid node, `1 ≤ h ≤ k`) has
an edge of length `len h` above it and a pendant edge of length `1` to the leaf `lf h`; the hybrid
edge has length `1`. -/
private def p8f_side {X : Type u} (len : ℕ → ℝ) (lf : ℕ → X) : ℕ → Side X
  | 0 => .hyb 1
  | k + 1 => .node (len (k + 1)) 1 (.leaf (lf (k + 1))) (p8f_side len lf k)

/-- The nodes of `p8f_side`, from the hybrid node up. -/
private theorem p8f_side_nodes {X : Type u} (len : ℕ → ℝ) (lf : ℕ → X) (k : ℕ) :
    (p8f_side len lf k).nodes.reverse = (List.range k).map fun i =>
      (len (i + 1), (1 : ℝ), (Net.leaf (lf (i + 1)) : Net X)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [p8f_side, Side.nodes, List.reverse_cons, ih, List.range_succ, List.map_append]
    rfl

/-- The leaves of `p8f_side`, from the hybrid node up. -/
private theorem p8f_side_leaves {X : Type u} (len : ℕ → ℝ) (lf : ℕ → X) (k : ℕ) :
    (p8f_side len lf k).leaves.reverse = (List.range k).map fun i => lf (i + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [p8f_side, Side.leaves, List.reverse_append, ih, List.range_succ, List.map_append]
    rfl

private theorem p8f_side_isMetric {X : Type u} {len : ℕ → ℝ} (lf : ℕ → X) {k : ℕ}
    (hlen : ∀ h, 1 ≤ h → h ≤ k → 0 < len h) : (p8f_side len lf k).IsMetric := by
  induction k with
  | zero => exact (one_pos : (0 : ℝ) < 1)
  | succ k ih => exact ⟨hlen _ (by omega) le_rfl, one_pos, trivial, ih fun h h1 h2 =>
      hlen h h1 (by omega)⟩

/-! ### The network of a metric cycle -/

/-- The lengths along the side of `C₁`: `w_h` above the node at height `h ≤ d - 2`, and `1` above
the top node (that edge and the hybrid edge of the other side form the edge `w_{d-1}` of the
semi-directed cycle, which the metric cycle does not record). -/
private def p8f_len {d : ℕ} (M : MetricCycle d) (h : ℕ) : ℝ := if h ≤ d - 2 then M.w h else 1

/-- The side of `C₁`: the leaf `h` hangs from the node at height `h`, `1 ≤ h ≤ d - 1`. -/
private def p8f_side₁ {d : ℕ} [NeZero d] (M : MetricCycle d) : Side (Fin d) :=
  p8f_side (p8f_len M) (Fin.ofNat d) (d - 1)

/-- The network of the metric cycle `M`: its root is the top node of a `d`-cycle, with the leaf `0`
below the hybrid node. -/
private def p8f_net {d : ℕ} [NeZero d] (M : MetricCycle d) : Net (Fin d) :=
  .cycle M.γ (p8f_side₁ M) (.hyb 1) 1 (.leaf 0)

/-- The cycle of `p8f_net M`. -/
private def p8f_cycle {d : ℕ} [NeZero d] (M : MetricCycle d) : (p8f_net M).Cycle where
  γ := M.γ
  side₁ := p8f_side₁ M
  side₂ := .hyb 1
  ℓ := 1
  below := .leaf 0
  mem := by simp [p8f_net, Net.subnets]

private theorem p8f_cycle_nodes {d : ℕ} [NeZero d] (M : MetricCycle d) :
    (p8f_cycle M).side₁.nodes.reverse = (List.range (d - 1)).map fun i =>
      (p8f_len M (i + 1), (1 : ℝ), (Net.leaf (Fin.ofNat d (i + 1)) : Net (Fin d))) :=
  p8f_side_nodes _ _ _

private theorem p8f_node {d : ℕ} [NeZero d] (M : MetricCycle d) (j : ℕ)
    (hj : j < (p8f_cycle M).side₁.nodes.reverse.length) :
    (p8f_cycle M).side₁.nodes.reverse[j] =
      (p8f_len M (j + 1), 1, .leaf (Fin.ofNat d (j + 1))) := by
  rw [List.getElem_of_eq (p8f_cycle_nodes M), List.getElem_map, List.getElem_range]

private theorem p8f_length {d : ℕ} [NeZero d] (M : MetricCycle d) :
    (p8f_cycle M).side₁.nodes.length = d - 1 := by
  rw [← List.length_reverse, p8f_cycle_nodes, List.length_map, List.length_range]

/-- The leaves of `p8f_net M` are `0, 1, …, d - 1`, each once. -/
private theorem p8f_nodup {d : ℕ} [NeZero d] (M : MetricCycle d) : (p8f_net M).leaves.Nodup := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hrange : (List.range d).map (Fin.ofNat d) =
      0 :: (p8f_side₁ M).leaves.reverse := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    rw [p8f_side₁, p8f_side_leaves, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_sub_cancel]
    rfl
  have hperm : (p8f_net M).leaves.Perm ((List.range d).map (Fin.ofNat d)) := by
    rw [hrange]
    show ((p8f_side₁ M).leaves ++ [] ++ [0]).Perm _
    rw [List.append_nil]
    exact List.perm_append_comm.trans (List.Perm.cons _ (List.reverse_perm _).symm)
  refine hperm.nodup_iff.2 (List.Nodup.map_on (fun a ha b hb h => ?_) List.nodup_range)
  have := congrArg Fin.val h
  rw [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt (List.mem_range.1 ha),
    Nat.mod_eq_of_lt (List.mem_range.1 hb)] at this
  exact this

/-- **Every metric cycle is a cycle of a network.** For a metric cycle `M` with `d ≥ 3` components
there is a well-formed network on the taxa `Fin d` with a cycle of `d` components whose inheritance
probability and edge lengths are those of `M`, and whose component at position `i` contains the
taxon `i`. -/
theorem MetricCycle.exists_net {d : ℕ} (hd : 3 ≤ d) (M : MetricCycle d) :
    ∃ (N : Net (Fin d)) (Ω : N.Cycle), N.WellFormed ∧ Ω.size = d ∧ Ω.γ = M.γ ∧
      (∀ m, 1 ≤ m → m ≤ d - 2 → Ω.edgeLen m = M.w m) ∧ ∀ i : Fin d, i ∈ Ω.component i := by
  have : NeZero d := ⟨by omega⟩
  have hp := p8f_length M
  refine ⟨p8f_net M, p8f_cycle M, ⟨⟨M.γ_pos, M.γ_lt_one, one_pos,
    p8f_side_isMetric _ fun k hk1 hk2 => ?_, (one_pos : (0 : ℝ) < 1), trivial, Or.inl ?_⟩,
    p8f_nodup M⟩, ?_, rfl, fun m hm1 hm2 => ?_, fun i => ?_⟩
  · -- the edges along the side of `C₁` have positive lengths
    unfold p8f_len
    split_ifs with hk
    · exact M.w_pos k hk1 hk
    · exact one_pos
  · -- the side of `C₁` has `d - 1 ≥ 2` nodes
    intro h
    rw [show (p8f_side₁ M).nodes = (p8f_cycle M).side₁.nodes from rfl] at h
    rw [h, List.length_nil] at hp
    omega
  · rw [Net.Cycle.size_of_top_eq _ rfl, hp]
    show d - 1 + 0 + 1 = d
    omega
  · rw [Net.Cycle.edgeLen_side₁ _ hm1 (by omega), p8f_node, Nat.sub_add_cancel hm1]
    exact ite_eq_left hm2
  · rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · obtain rfl : i = 0 := Fin.ext h0
      rw [show ((0 : Fin d) : ℕ) = 0 from rfl, Net.Cycle.component_zero]
      simp [p8f_cycle, Net.taxa, Net.leaves]
    · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
      rw [hj, Net.Cycle.component_side₁ _ (by omega), p8f_node]
      have hi : Fin.ofNat d (j + 1) = i := Fin.ext (by
        rw [Fin.val_ofNat, ← hj]
        exact Nat.mod_eq_of_lt i.isLt)
      rw [hi]
      simp [Net.taxa, Net.leaves]

/-- The network of `Phylogenetics.MetricCycle.exists_net`, with its component CFs: in the cyclic
order around the cycle, they are given by the formulas `cycleCF` of `M`
(`Phylogenetics.nmsc_quartetCF`). -/
theorem MetricCycle.exists_net_nmscQuartetCF {d : ℕ} (hd : 3 ≤ d) (M : MetricCycle d) :
    ∃ (N : Net (Fin d)) (Ω : N.Cycle), N.WellFormed ∧ Ω.size = d ∧
      (∀ i : Fin d, i ∈ Ω.component i) ∧ NMSCQuartetCF M (Equiv.refl _) (N.componentCF id) := by
  obtain ⟨N, Ω, hN, hΩ, hγ, hw, hx⟩ := M.exists_net hd
  exact ⟨N, Ω, hN, hΩ, hx, nmsc_quartetCF N hN Ω hΩ M hγ.symm (fun m h1 h2 => (hw m h1 h2).symm)
    (Equiv.refl _) id hx⟩

/-! ### The metric cycle of a cycle of a network -/

/-- The component CFs of a cycle with `d` components of a metric level-1 network are given by the
formulas `cycleCF` of a metric `d`-cycle: the one read off the cycle
(`Phylogenetics.Net.Cycle.exists_metricCycle`, `Phylogenetics.nmsc_quartetCF`). -/
theorem Net.Cycle.exists_nmscQuartetCF {X : Type u} [DecidableEq X] {N : Net X}
    (hN : N.WellFormed) (Ω : N.Cycle) {d : ℕ} (hΩ : Ω.size = d) (ord : Equiv.Perm (Fin d))
    (x : Fin d → X) (hx : ∀ i : Fin d, x (ord i) ∈ Ω.component i) :
    ∃ M : MetricCycle d, NMSCQuartetCF M ord (N.componentCF x) := by
  subst hΩ
  obtain ⟨M, hγ, hw⟩ := Ω.exists_metricCycle hN
  exact ⟨M, nmsc_quartetCF N hN Ω rfl M hγ hw ord x hx⟩

end Phylogenetics
