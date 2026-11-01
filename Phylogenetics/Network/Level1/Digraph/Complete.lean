module

public import Phylogenetics.Network.Level1.Digraph.CompleteCycle
public import Phylogenetics.Network.Level1.Digraph.CompleteEmbed
public import Mathlib.Tactic.Linarith
/-!
# Every rooted binary metric level-1 network is described by a network term

Every rooted binary metric level-1 phylogenetic network on the taxa `X`
(`Phylogenetics.MetricDigraph.IsNetwork`) is isomorphic to the graph of a well-formed term
`N : Phylogenetics.Net X` with at least two leaves, by an isomorphism that preserves the edges, the
leaf labels, the edge lengths and the inheritance probabilities
(`Phylogenetics.MetricDigraph.IsNetwork.exists_net`).

The proof goes down from the root, by strong induction on the number of descendants
(`Phylogenetics.MetricDigraph.IsNetwork.exists_describesNet`): the descendants of a vertex `v` that
roots a subnetwork (`Phylogenetics.MetricDigraph.IsSubnetRoot`) are the image of the graph of a
term, `v` that of its root (`Phylogenetics.MetricDigraph.DescribesNet`). A vertex without children
is a leaf; a vertex whose two children have no common descendant is a tree node on no cycle;
otherwise it is the top node of a cycle (`Phylogenetics.Network.Level1.Digraph.CompleteCycle`), whose sides are
described node by node. The pieces are put together by `Phylogenetics.Network.Level1.Digraph.CompleteEmbed`. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v

variable {X : Type u}

namespace MetricDigraph

variable {V : Type v} {G : MetricDigraph V X}

/-- The term `N` describes the subnetwork of `G` below `v`, through the map `f`: `N` is metric,
with distinct leaf labels, which are labels of descendants of `v`, and `f` embeds the graph of
`N` onto the descendants of `v`, sending the root of `N` to `v`. -/
structure DescribesNet (G : MetricDigraph V X) (v : V) (N : Net X) (f : N.Vert → V) : Prop where
  /-- The term is metric. -/
  isMetric : N.IsMetric
  /-- The leaf labels are distinct. -/
  nodup : N.leaves.Nodup
  /-- The leaf labels are labels of descendants of `v`. -/
  label : ∀ x ∈ N.leaves, ∃ w ∈ G.desc v, G.label w = some x
  /-- The root is sent to `v`. -/
  root : f N.root = v
  /-- The graph of `N` embeds onto the descendants of `v`. -/
  embeds : G.Embeds N.toGraph f (G.desc v)

/-- The side `S` describes the side of a cycle of `G` with hybrid node `h` from its first node
`p` (with parent `u`), through the map `f`: `S` is metric, with distinct leaf labels, which are
labels of descendants of `p` not below `h`, and `f` embeds the graph of `S`
(`Phylogenetics.MetricDigraph.SideEmbeds`). -/
structure DescribesSide (G : MetricDigraph V X) (h u p : V) (S : Side X) (f : S.Vert → V) :
    Prop where
  /-- The side is metric. -/
  isMetric : S.IsMetric
  /-- The leaf labels are distinct. -/
  nodup : S.leaves.Nodup
  /-- The leaf labels are labels of descendants of `p` not below `h`. -/
  label : ∀ x ∈ S.leaves, ∃ w ∈ G.desc p \ G.desc h, G.label w = some x
  /-- The graph of `S` embeds from `p`. -/
  embeds : G.SideEmbeds S.toGraph f h u p

/-- Lists of labels of vertices in disjoint sets of a labelled network have no common
element. -/
private theorem p8g2_disjoint_labels (hl : G.IsLabelled) {S T : Set V} (hST : Disjoint S T)
    {l₁ l₂ : List X} (h₁ : ∀ x ∈ l₁, ∃ w ∈ S, G.label w = some x)
    (h₂ : ∀ x ∈ l₂, ∃ w ∈ T, G.label w = some x) : ∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y := by
  rintro x hx y hy rfl
  obtain ⟨w₁, hw₁, hx₁⟩ := h₁ x hx
  obtain ⟨w₂, hw₂, hx₂⟩ := h₂ x hy
  exact Set.disjoint_left.1 hST hw₁ (hl.label_injective w₁ w₂ x hx₁ hx₂ ▸ hw₂)

/-- **The sides of a cycle, node by node.** Given the nodes `P` of a side of a cycle with hybrid
node `h`, from the child `c` of the top node `v` (`Phylogenetics.MetricDigraph.IsSideNodes`), and
the description of the subnetworks with fewer descendants than `v`, the part of the side from each
of its nodes `p` (or from `h`), entered from `u`, is described by a side term; the descendants of
`p` not below `h` are not descendants of the other child `c'` of `v`. By induction on the number of
descendants of `p`. -/
private theorem p8g2_side (hG : G.IsNetwork) {n : ℕ}
    (ih : ∀ w, (G.desc w).ncard ≤ n → G.IsSubnetRoot w →
      ∃ (N : Net X) (f : N.Vert → V), G.DescribesNet w N f)
    {v c c' h : V} {P : Set V} (hvn : (G.desc v).ncard ≤ n + 1) (hvc : G.Adj v c)
    (hP : G.IsSideNodes c h P) (hh' : h ∈ G.desc c')
    (hmin : ∀ y ∈ G.desc c ∩ G.desc c', h ∈ G.desc y → y = h) (m : ℕ) :
    ∀ u p, (G.desc p).ncard ≤ m → G.Adj u p → (p = h ∨ p ∈ P) →
      ∃ (S : Side X) (f : S.Vert → V), G.DescribesSide h u p S f ∧
        Disjoint (G.desc p \ G.desc h) (G.desc c') := by
  have hB := hG.binary
  have := hB.finite
  induction m with
  | zero =>
    intro u p hp
    exact absurd hp (Nat.not_le.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨p, self_mem_desc p⟩))
  | succ m ihm =>
    intro u p hpm hup hp
    rcases hp with rfl | hp
    -- the end of the side: a single hybrid edge
    · refine ⟨.hyb (G.len u p), Empty.elim, ⟨hG.metric.len_pos u p hup, List.nodup_nil,
        fun x hx => absurd hx List.not_mem_nil, sideEmbeds_hyb⟩, ?_⟩
      rw [Set.sdiff_self]
      exact Set.empty_disjoint _
    -- a node `p` of the side, with the next node `s` and the pendant subnetwork below `q`
    · obtain ⟨s, q, hch, hsq, hs, hhq, he⟩ := hP.next p hp
      have hps : G.Adj p s := (hch s).2 (Or.inl rfl)
      have hpq : G.Adj p q := (hch q).2 (Or.inr rfl)
      have hpc : p ∈ G.desc c := hP.mem_desc p hp
      have hhp : h ∈ G.desc p := hP.anc p hp
      have hph : p ∉ G.desc h := fun h' => hP.ne p hp (hB.eq_of_mem_desc_of_mem_desc h' hhp)
      have hhs : h ∈ G.desc s := by
        rcases hs with rfl | hs
        · exact self_mem_desc _
        · exact hP.anc s hs
      -- the descendants of `q` avoid those of `h` and of `s`
      have hqh : Disjoint (G.desc q) (G.desc h) := by
        refine Set.disjoint_left.2 fun w hwq hwh => hph ?_
        exact he.reflTransGen hhq hwh hwq
      have hqs : Disjoint (G.desc q) (G.desc s) := by
        refine Set.disjoint_left.2 fun w hwq hws => hB.notMem_desc_of_adj hps ?_
        exact he.reflTransGen (fun hsq' => hhq (desc_subset hsq' hhs)) hws hwq
      -- the rest of the side, from `s`
      have hsm : (G.desc s).ncard ≤ m := Nat.le_of_lt_succ
        ((hB.ncard_desc_lt (mem_desc_of_adj hps) (hB.ne_of_adj hps).symm).trans_le hpm)
      obtain ⟨S', f', hS', hd'⟩ := ihm p s hsm hps hs
      -- the subnetwork below `q`
      have hvq : q ∈ G.desc v :=
        desc_subset (mem_desc_of_adj hvc) (desc_subset hpc (mem_desc_of_adj hpq))
      have hqv : q ≠ v := fun h' => hB.notMem_desc_of_adj hvc
        (h' ▸ desc_subset hpc (mem_desc_of_adj hpq))
      obtain ⟨N, g, hN⟩ := ih q (Nat.le_of_lt_succ ((hB.ncard_desc_lt hvq hqv).trans_le hvn))
        (hB.isSubnetRoot_of_entersOnly he hpq)
      refine ⟨.node (G.len u p) (G.len p q) N S', NodeVert.elim p g f', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · exact ⟨hG.metric.len_pos u p hup, hG.metric.len_pos p q hpq, hN.isMetric, hS'.isMetric⟩
      · refine List.nodup_append.2 ⟨hN.nodup, hS'.nodup, ?_⟩
        exact p8g2_disjoint_labels hG.labelled (hqs.mono_right Set.sdiff_subset) hN.label hS'.label
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨w, hw, hwx⟩ := hN.label x hx
          exact ⟨w, ⟨desc_subset (mem_desc_of_adj hpq) hw, Set.disjoint_left.1 hqh hw⟩, hwx⟩
        · obtain ⟨w, hw, hwx⟩ := hS'.label x hx
          exact ⟨w, ⟨desc_subset (mem_desc_of_adj hps) hw.1, hw.2⟩, hwx⟩
      · refine hB.sideEmbeds_node hch hph hqh hqs he
          (hB.label_eq_none_of_adj hG.labelled hps)
          (not_isHybrid_of_indeg_eq_one (hB.indeg_eq_one_of_entersOnly he hpq))
          (fun hsh => not_isHybrid_of_indeg_eq_one (hP.indeg s (hs.resolve_left hsh)))
          hN.embeds hN.root hS'.embeds
      -- the part of the side from `p` is not below `c'`
      · refine Set.disjoint_left.2 fun x ⟨hxp, hxh⟩ hxc' => ?_
        have hpc' : p ∉ G.desc c' := fun h' => hP.ne p hp (hmin p ⟨hpc, h'⟩ hhp)
        rcases (mem_desc_iff_of_adj_iff hch).1 hxp with rfl | hxs | hxq
        · exact hpc' hxc'
        · exact Set.disjoint_left.1 hd' ⟨hxs, hxh⟩ hxc'
        · have hc'q : c' ∉ G.desc q := fun h' => hhq (desc_subset h' hh')
          exact hpc' (he.reflTransGen hc'q hxc' hxq)

/-- **Every subnetwork is described by a term.** In a network `G`, the descendants of a vertex `v`
rooting a subnetwork (`Phylogenetics.MetricDigraph.IsSubnetRoot`) are described by a term
(`Phylogenetics.MetricDigraph.DescribesNet`), by strong induction on their number: a vertex without
children is a leaf; if the two children of `v` have no common descendant, `v` is a tree node on no
cycle; otherwise `v` is the top node of a cycle
(`Phylogenetics.MetricDigraph.IsBinary.exists_cycle`). -/
theorem IsNetwork.exists_describesNet (hG : G.IsNetwork) (n : ℕ) :
    ∀ v, (G.desc v).ncard ≤ n → G.IsSubnetRoot v →
      ∃ (N : Net X) (f : N.Vert → V), G.DescribesNet v N f := by
  have hB := hG.binary
  have := hB.finite
  induction n with
  | zero =>
    intro v hv
    exact absurd hv (Nat.not_le.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨v, self_mem_desc v⟩))
  | succ n ih =>
    intro v hvn hv
    rcases hv.outdeg with h0 | h2
    -- a leaf
    · have hno : ∀ w, ¬ G.Adj v w := outdeg_eq_zero_iff.1 h0
      have hleaf : G.IsLeaf v := by
        rcases hB.degrees v with h' | h' | h' | h'
        · have := h'.2; omega
        · exact h'
        · have := h'.2; omega
        · have := h'.2; omega
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((hG.labelled.isSome_label_iff v).2 hleaf)
      refine ⟨.leaf x, fun _ => v, trivial, List.nodup_singleton x, fun y hy => ?_, rfl,
        embeds_leaf hno hx⟩
      rw [Net.leaves, List.mem_singleton] at hy
      exact ⟨v, self_mem_desc v, hy ▸ hx⟩
    · obtain ⟨c₁, c₂, hne, hvc⟩ := outdeg_eq_two_iff.1 h2
      have hvc₁ : G.Adj v c₁ := (hvc c₁).2 (Or.inl rfl)
      have hvc₂ : G.Adj v c₂ := (hvc c₂).2 (Or.inr rfl)
      have hvc' : ∀ x, G.Adj v x ↔ x = c₂ ∨ x = c₁ := fun x => (hvc x).trans or_comm
      have hlv : G.label v = none := hB.label_eq_none_of_adj hG.labelled hvc₁
      have hlt : ∀ w ∈ G.desc v, w ≠ v → (G.desc w).ncard ≤ n := fun w hw hwv =>
        Nat.le_of_lt_succ ((hB.ncard_desc_lt hw hwv).trans_le hvn)
      by_cases hint : (G.desc c₁ ∩ G.desc c₂).Nonempty
      -- the top node of a cycle
      · obtain ⟨h, c, hh₁, hh₂, hmin, hhyb, hhc, he, ⟨P₁, hP₁⟩, ⟨P₂, hP₂⟩⟩ :=
          hB.exists_cycle hG.level1 hvc hne hint
        have hmin' : ∀ y ∈ G.desc c₂ ∩ G.desc c₁, h ∈ G.desc y → y = h :=
          fun y hy => hmin y ⟨hy.2, hy.1⟩
        have hhc' : G.Adj h c := (hhc c).2 rfl
        have hv₁ : v ∉ G.desc c₁ := hB.notMem_desc_of_adj hvc₁
        have hv₂ : v ∉ G.desc c₂ := hB.notMem_desc_of_adj hvc₂
        have hhv : h ∈ G.desc v := desc_subset (mem_desc_of_adj hvc₁) hh₁
        have hcv : c ∈ G.desc v := desc_subset hhv (mem_desc_of_adj hhc')
        -- the two sides and the subnetwork below the hybrid node
        obtain ⟨S₁, f₁, hS₁, hd₁⟩ := p8g2_side hG ih hvn hvc₁ hP₁ hh₂ hmin _ v c₁ le_rfl hvc₁
          hP₁.start
        obtain ⟨S₂, f₂, hS₂, hd₂⟩ := p8g2_side hG ih hvn hvc₂ hP₂ hh₁ hmin' _ v c₂ le_rfl hvc₂
          hP₂.start
        obtain ⟨N, g, hN⟩ := ih c (hlt c hcv (fun h' => hv₁ (h' ▸ desc_subset hh₁
          (mem_desc_of_adj hhc')))) (hB.isSubnetRoot_of_entersOnly he hhc')
        -- the parent `y₁` of `h` on the side of `c₁`, and the inheritance probability `γ`
        obtain ⟨y₁, hy₁h, hy₁, hy₁s, hy₁n⟩ : ∃ y₁, G.Adj y₁ h ∧
            (y₁ = v ∨ y₁ ∈ G.desc c₁ \ G.desc h) ∧
            (∀ a, S₁.toGraph.last = some a → f₁ a = y₁) ∧ (S₁.toGraph.last = none → y₁ = v) := by
          rcases hl : S₁.toGraph.last with _ | a
          · have hc₁h : c₁ = h := hS₁.embeds.last_eq_none.1 hl
            exact ⟨v, hc₁h ▸ hvc₁, Or.inl rfl, fun a ha => absurd ha (by simp), fun _ => rfl⟩
          · refine ⟨f₁ a, (hS₁.embeds.last_eq_some a).1 hl, Or.inr (hS₁.embeds.embeds.mem a),
              fun b hb => ?_, fun h' => absurd h' (by simp)⟩
            rw [Option.some_inj] at hb
            rw [hb]
        have hy₁c₂ : ∀ y, y ∈ G.desc c₂ → y₁ ≠ y := by
          rintro y hy rfl
          rcases hy₁ with rfl | hy₁
          · exact hv₂ hy
          · exact Set.disjoint_left.1 hd₁ hy₁ hy
        set γ := G.inh y₁ h with hγ
        have hγ₂ : ∀ b, S₂.toGraph.last = some b → G.inh (f₂ b) h = 1 - γ := by
          intro b hb
          have := hG.metric.inh_add_inh y₁ (f₂ b) h hy₁h ((hS₂.embeds.last_eq_some b).1 hb)
            (hy₁c₂ _ (hS₂.embeds.embeds.mem b).1) hhyb
          rw [hγ]
          linarith
        have hγ₂' : S₂.toGraph.last = none → G.inh v h = 1 - γ := by
          intro hl
          have hc₂h : c₂ = h := hS₂.embeds.last_eq_none.1 hl
          have hy₁v : y₁ ≠ v := by
            rcases hl₁ : S₁.toGraph.last with _ | a
            · exact absurd (hS₁.embeds.last_eq_none.1 hl₁) fun h' => hne (h'.trans hc₂h.symm)
            · rw [← hy₁s a hl₁]
              exact ne_of_mem_of_not_mem (hS₁.embeds.embeds.mem a).1 hv₁
          have := hG.metric.inh_add_inh y₁ v h hy₁h (hc₂h ▸ hvc₂) hy₁v hhyb
          rw [hγ]
          linarith
        have hside : ∀ {c' : V} {P : Set V}, G.IsSideNodes c' h P → c' ≠ h → ¬ G.IsHybrid c' :=
          fun hP hc' => not_isHybrid_of_indeg_eq_one (hP.indeg _ (hP.start.resolve_left hc'))
        refine ⟨.cycle γ S₁ S₂ (G.len h c) N, CycleVert.elim v f₁ f₂ h g, ⟨?_, ?_, ?_, rfl, ?_⟩⟩
        -- the term is metric
        · have hγ01 := hG.metric.inh_mem_Ioo y₁ h hy₁h hhyb
          refine ⟨hγ01.1, hγ01.2, hG.metric.len_pos h c hhc', hS₁.isMetric, hS₂.isMetric,
            hN.isMetric, ?_⟩
          rw [Ne, ← Side.toGraph_first_eq_none_iff, Ne, ← Side.toGraph_first_eq_none_iff,
            hS₁.embeds.first_eq_none, hS₂.embeds.first_eq_none]
          by_contra! h'
          exact hne (h'.1.trans h'.2.symm)
        -- distinct leaf labels
        · have hT₁T₂ : Disjoint (G.desc c₁ \ G.desc h) (G.desc c₂ \ G.desc h) :=
            hd₁.mono_right Set.sdiff_subset
          have hTc : ∀ c', Disjoint (G.desc c' \ G.desc h) (G.desc c) := fun c' =>
            Set.disjoint_left.2 fun x hx hxc => hx.2 (desc_subset (mem_desc_of_adj hhc') hxc)
          refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hS₁.nodup, hS₂.nodup,
            p8g2_disjoint_labels hG.labelled hT₁T₂ hS₁.label hS₂.label⟩, hN.nodup, ?_⟩
          intro x hx y hy
          rcases List.mem_append.1 hx with hx | hx
          · exact p8g2_disjoint_labels hG.labelled (hTc c₁) hS₁.label hN.label x hx y hy
          · exact p8g2_disjoint_labels hG.labelled (hTc c₂) hS₂.label hN.label x hx y hy
        -- the leaf labels are labels of descendants of `v`
        · intro x hx
          simp only [Net.leaves, List.mem_append] at hx
          rcases hx with (hx | hx) | hx
          · obtain ⟨w, hw, hwx⟩ := hS₁.label x hx
            exact ⟨w, desc_subset (mem_desc_of_adj hvc₁) hw.1, hwx⟩
          · obtain ⟨w, hw, hwx⟩ := hS₂.label x hx
            exact ⟨w, desc_subset (mem_desc_of_adj hvc₂) hw.1, hwx⟩
          · obtain ⟨w, hw, hwx⟩ := hN.label x hx
            exact ⟨w, desc_subset hcv hw, hwx⟩
        -- the embedding
        · exact hB.embeds_cycle hvc hhc hh₁ hh₂ hd₁ hd₂ he hlv
            (hG.labelled.label_eq_none_of_isHybrid hhyb) (hside hP₁) (hside hP₂)
            (not_isHybrid_of_indeg_eq_one (hB.indeg_eq_one_of_entersOnly he hhc'))
            hS₁.embeds hS₂.embeds hN.embeds hN.root (fun a ha => by rw [hγ, hy₁s a ha])
            (fun ha => by rw [hγ, hy₁n ha]) hγ₂ hγ₂'
      -- a tree node on no cycle
      · have hdisj : Disjoint (G.desc c₁) (G.desc c₂) :=
          Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hint)
        -- each child has `v` as only parent, and roots a subnetwork
        have hchild : ∀ {c c' : V}, G.Adj v c → Disjoint (G.desc c) (G.desc c') →
            (∀ x, G.Adj v x ↔ x = c ∨ x = c') → G.indeg c = 1 ∧ G.IsSubnetRoot c := by
          intro c c' hvc hdc hvx
          have hvc'' : v ∉ G.desc c := hB.notMem_desc_of_adj hvc
          have hcl : ∀ w ∈ G.desc c, ∀ x, G.Adj x w → x ∈ G.desc c ∨ (x = v ∧ w = c) := by
            intro w hw x hxw
            have hwv : w ≠ v := fun h' => hvc'' (h' ▸ hw)
            rcases (mem_desc_iff_of_adj_iff hvx).1
              (hv.closed w (desc_subset (mem_desc_of_adj hvc) hw) hwv x hxw) with rfl | hx | hx
            · rcases (hvx w).1 hxw with rfl | rfl
              · exact Or.inr ⟨rfl, rfl⟩
              · exact absurd (self_mem_desc w) (Set.disjoint_left.1 hdc hw)
            · exact Or.inl hx
            · exact absurd (mem_desc_of_mem_of_adj hx hxw) (Set.disjoint_left.1 hdc hw)
          have he : G.EntersOnly v c := hcl
          exact ⟨hB.indeg_eq_one_of_entersOnly he hvc, hB.isSubnetRoot_of_entersOnly he hvc⟩
        obtain ⟨hin₁, hsub₁⟩ := hchild hvc₁ hdisj hvc
        obtain ⟨hin₂, hsub₂⟩ := hchild hvc₂ hdisj.symm hvc'
        obtain ⟨N₁, f₁, hN₁⟩ := ih c₁ (hlt c₁ (mem_desc_of_adj hvc₁) (hB.ne_of_adj hvc₁).symm)
          hsub₁
        obtain ⟨N₂, f₂, hN₂⟩ := ih c₂ (hlt c₂ (mem_desc_of_adj hvc₂) (hB.ne_of_adj hvc₂).symm)
          hsub₂
        refine ⟨.tree (G.len v c₁) N₁ (G.len v c₂) N₂, TreeVert.elim v f₁ f₂,
          ⟨⟨hG.metric.len_pos v c₁ hvc₁, hG.metric.len_pos v c₂ hvc₂, hN₁.isMetric,
            hN₂.isMetric⟩, ?_, ?_, rfl, ?_⟩⟩
        · exact List.nodup_append.2 ⟨hN₁.nodup, hN₂.nodup,
            p8g2_disjoint_labels hG.labelled hdisj hN₁.label hN₂.label⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨w, hw, hwx⟩ := hN₁.label x hx
            exact ⟨w, desc_subset (mem_desc_of_adj hvc₁) hw, hwx⟩
          · obtain ⟨w, hw, hwx⟩ := hN₂.label x hx
            exact ⟨w, desc_subset (mem_desc_of_adj hvc₂) hw, hwx⟩
        · exact hB.embeds_tree hvc hdisj hlv (not_isHybrid_of_indeg_eq_one hin₁)
            (not_isHybrid_of_indeg_eq_one hin₂) hN₁.embeds hN₁.root hN₂.embeds hN₂.root

end MetricDigraph

/-- **Every rooted binary metric level-1 network is described by a network term.** A rooted
binary metric level-1 phylogenetic network `G` on the taxa `X` is isomorphic to the graph of a
well-formed term `N` with at least two leaves: there is a bijection from the vertices of `G` to
those of the graph of `N` that preserves the edges in both directions, the leaf labels, the edge
lengths and the inheritance probabilities of the hybrid edges (`MetricDigraph.Iso`).

The term describes the subnetwork below the root, which is all of `G`
(`Phylogenetics.MetricDigraph.IsNetwork.exists_describesNet`); it is not a leaf, as the root has two
children, so it has at least two leaves. -/
theorem MetricDigraph.IsNetwork.exists_net {V : Type*} {G : MetricDigraph V X}
    (hG : G.IsNetwork) :
    ∃ N : Net X, N.WellFormed ∧ 2 ≤ N.leaves.length ∧ Nonempty (G.Iso N.toGraph) := by
  have hB := hG.binary
  obtain ⟨r, hr, -⟩ := hB.exists_isRoot
  have hD : G.desc r = Set.univ := Set.eq_univ_of_forall (hB.reflTransGen_root hr.1)
  have hsub : G.IsSubnetRoot r := ⟨Or.inr hr.2, fun _ _ _ x _ => hD ▸ Set.mem_univ x⟩
  obtain ⟨N, f, hN⟩ := hG.exists_describesNet _ r le_rfl hsub
  have hemb : G.Embeds N.toGraph f Set.univ := hD ▸ hN.embeds
  refine ⟨N, ⟨hN.isMetric, hN.nodup⟩, ?_, hemb.nonempty_iso⟩
  obtain ⟨c₁, c₂, -, hrc⟩ := outdeg_eq_two_iff.1 hr.2
  have hN' := hN.isMetric
  cases N with
  | leaf x =>
    obtain ⟨a, ha⟩ := hemb.surj c₁ (Set.mem_univ _)
    have hrc₁ : G.Adj (f (Net.leaf x).root) (f a) := by
      rw [hN.root, ha]
      exact (hrc c₁).2 (Or.inl rfl)
    exact False.elim ((hemb.adj_iff _ a).1 hrc₁)
  | tree _ N₁ _ N₂ =>
    rw [Net.leaves, List.length_append]
    have h₁ := List.length_pos_of_ne_nil N₁.leaves_ne_nil
    have h₂ := List.length_pos_of_ne_nil N₂.leaves_ne_nil
    omega
  | cycle _ S₁ S₂ _ N' =>
    obtain ⟨-, -, -, -, -, -, hnodes⟩ := hN'
    have hside : ∀ S : Side X, S.nodes ≠ [] → 1 ≤ S.leaves.length := by
      rintro (_ | ⟨_, _, M, _⟩) hS
      · exact absurd rfl hS
      · rw [Side.leaves, List.length_append]
        have := List.length_pos_of_ne_nil M.leaves_ne_nil
        omega
    rw [Net.leaves, List.length_append, List.length_append]
    have := List.length_pos_of_ne_nil N'.leaves_ne_nil
    rcases hnodes with h | h
    · have := hside S₁ h
      omega
    · have := hside S₂ h
      omega

end Phylogenetics
