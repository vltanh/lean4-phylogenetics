module

public import Phylogenetics.Graph.CompleteDesc
/-!
# The cycle below a vertex of a binary level-1 network

Let `v` be a vertex of a binary level-1 network with two children `c₁` and `c₂` that have a common
descendant. Then `v` is the top node of a cycle
(`Phylogenetics.MetricDigraph.IsBinary.exists_cycle`), whose hybrid node `h` is a common descendant
of `c₁` and `c₂` with no proper ancestor among the common descendants:

* the directed paths from `v` through `c₁` and through `c₂` to `h` form a cycle of the undirected
  graph (`Phylogenetics.MetricDigraph.IsBinary.isCycle_append_reverse`);
* by `Phylogenetics.MetricDigraph.IsBinary.isBridge_of_isCycle`, the other edges at the vertices
  of the cycle are cut edges; hence the nodes of each side are tree nodes, whose second child
  roots a subnetwork entered only through its pendant edge and not containing `h`
  (`Phylogenetics.MetricDigraph.IsSideNodes`); and `h` is a hybrid node whose only child roots a
  subnetwork entered only through the child edge of `h`.

This is the overlapping case of the description of a network by a term
(`Phylogenetics.Graph.Complete`). -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v

open SimpleGraph

/-- An edge `s(v, y)` of a walk that starts with the edge `(v, c)` and does not visit `v` again is
that edge. -/
theorem eq_of_mem_edges_cons {W : Type*} {H : SimpleGraph W} {v c w y : W} {hvc : H.Adj v c}
    {P : H.Walk c w} (hv : v ∉ P.support) (hy : s(v, y) ∈ (Walk.cons hvc P).edges) : y = c := by
  rw [Walk.edges_cons, List.mem_cons] at hy
  rcases hy with hy | hy
  · exact Sym2.congr_right.1 hy
  · exact absurd (P.fst_mem_support_of_mem_edges hy) hv

namespace MetricDigraph

variable {V : Type u} {X : Type v} {G : MetricDigraph V X}

/-- The nodes `P` of a side of a cycle with hybrid node `h`, starting from the child `c` of the top
node: `P` contains `c` unless `c = h`; each node `p ∈ P` is a descendant of `c` and an ancestor of
`h` other than `h`, a vertex of in-degree one, with two children: the next node `s` of the side (in
`P`, or `h`) and the root `q` of a subnetwork that is entered only through the edge `(p, q)` and
does not contain `h`. -/
structure IsSideNodes (G : MetricDigraph V X) (c h : V) (P : Set V) : Prop where
  /-- The side starts at `c`, unless `c = h` (a side with no node). -/
  start : c = h ∨ c ∈ P
  /-- The hybrid node is not a node of the side. -/
  ne : ∀ p ∈ P, p ≠ h
  /-- The nodes are descendants of `c`. -/
  mem_desc : ∀ p ∈ P, p ∈ G.desc c
  /-- The nodes are ancestors of `h`. -/
  anc : ∀ p ∈ P, h ∈ G.desc p
  /-- The nodes have in-degree one. -/
  indeg : ∀ p ∈ P, G.indeg p = 1
  /-- Each node has two children: the next node of the side (or `h`), and the root of a
  subnetwork entered only through its pendant edge, not containing `h`. -/
  next : ∀ p ∈ P, ∃ s q, (∀ x, G.Adj p x ↔ x = s ∨ x = q) ∧ s ≠ q ∧ (s = h ∨ s ∈ P) ∧
    h ∉ G.desc q ∧ G.EntersOnly p q

namespace IsBinary

variable (hG : G.IsBinary)
include hG

/-- Two vertices with a common descendant have a minimal common descendant: one that is a
descendant of no other common descendant. -/
theorem exists_minimal_common_desc {c₁ c₂ : V} (hne : (G.desc c₁ ∩ G.desc c₂).Nonempty) :
    ∃ h ∈ G.desc c₁ ∩ G.desc c₂, ∀ y ∈ G.desc c₁ ∩ G.desc c₂, h ∈ G.desc y → y = h := by
  have := hG.finite
  have : IsTrans V (Relation.TransGen G.Adj) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen G.Adj) := ⟨hG.acyclic⟩
  obtain ⟨h, hh, hmin⟩ :=
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen G.Adj)).has_min _ hne
  refine ⟨h, hh, fun y hy hyh => ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hyh with h' | h'
  · exact h'.symm
  · exact absurd h' (hmin y hy)

/-- **The cycle below `v`.** The directed paths from `v` through its children `c₁` and `c₂` to a
minimal common descendant `h` of `c₁` and `c₂` meet only at `v` and `h`, and form a cycle. -/
theorem isCycle_append_reverse {v c₁ c₂ h : V} (hvc₁ : G.Adj v c₁) (hvc₂ : G.Adj v c₂)
    (hne : c₁ ≠ c₂) (hmin : ∀ y ∈ G.desc c₁ ∩ G.desc c₂, h ∈ G.desc y → y = h)
    {P₁ : G.undirected.Walk c₁ h} (hP₁ : P₁.IsPath)
    (hP₁s : ∀ x ∈ P₁.support, x ∈ G.desc c₁ ∧ h ∈ G.desc x)
    {P₂ : G.undirected.Walk c₂ h} (hP₂ : P₂.IsPath)
    (hP₂s : ∀ x ∈ P₂.support, x ∈ G.desc c₂ ∧ h ∈ G.desc x) :
    ((Walk.cons (hG.undirected_adj_of_adj hvc₁) P₁).append
      (Walk.cons (hG.undirected_adj_of_adj hvc₂) P₂).reverse).IsCycle := by
  have hv₁ : v ∉ P₁.support := fun hv => hG.notMem_desc_of_adj hvc₁ (hP₁s v hv).1
  have hv₂ : v ∉ P₂.support := fun hv => hG.notMem_desc_of_adj hvc₂ (hP₂s v hv).1
  have hW₁ : (Walk.cons (hG.undirected_adj_of_adj hvc₁) P₁).IsPath :=
    (Walk.cons_isPath_iff _ _).2 ⟨hP₁, hv₁⟩
  have hW₂ : (Walk.cons (hG.undirected_adj_of_adj hvc₂) P₂).IsPath :=
    (Walk.cons_isPath_iff _ _).2 ⟨hP₂, hv₂⟩
  refine hW₁.isCycle_append hW₂.reverse ?_ ?_
  · rw [Walk.support_cons, List.tail_cons]
    intro x hx₁ hx₂
    have hnd := hW₂.reverse.support_nodup
    rw [← Walk.cons_tail_support] at hnd
    have hxh : x ≠ h := fun hxh => (List.nodup_cons.1 hnd).1 (hxh ▸ hx₂)
    have hx : x ∈ (Walk.cons (hG.undirected_adj_of_adj hvc₂) P₂).support := by
      rw [← List.mem_reverse, ← Walk.support_reverse]
      exact List.mem_of_mem_tail hx₂
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv₁ hx₁
    · exact hxh (hmin x ⟨(hP₁s x hx₁).1, (hP₂s x hx).1⟩ (hP₁s x hx₁).2)
  · rw [Walk.length_reverse, Walk.length_cons, Walk.length_cons]
    by_cases h₁ : c₁ = h
    · right
      have : P₂.length ≠ 0 := fun h0 => hne (h₁.trans (Walk.eq_of_length_eq_zero h0).symm)
      omega
    · left
      have : P₁.length ≠ 0 := fun h0 => h₁ (Walk.eq_of_length_eq_zero h0)
      omega

/-- **A node of a side of the cycle.** Let `C` be a cycle, `W` a directed path from `v` to `h`
along it, through the child `c` of `v`, and `x₂` a parent of `h` that is not a descendant of `c`.
A vertex `p` of `W` other than `v` and `h` has in-degree one (another edge into `p` would be a cut
edge by `isBridge_of_isCycle`, while `p` is entered from its predecessor along `W`) and two
children: its successor `s` along `W`, and a vertex `q` such that `(p, q)` is a cut edge
(`isBridge_of_isCycle`), so that the descendants of `q` are entered only through `(p, q)`; they do
not contain `h`, which is entered from `x₂`. -/
theorem side_node (h1 : G.IsLevel1) {v c h x₂ : V} {C : G.undirected.Walk v v} (hC : C.IsCycle)
    {W : G.undirected.Walk v h} (hWd : ∀ d ∈ W.darts, G.Adj d.fst d.snd)
    (hWC : ∀ e ∈ W.edges, e ∈ C.edges) (hWs : ∀ x ∈ W.support, x ∈ C.support)
    (hWc : ∀ x ∈ W.support, x ≠ v → x ∈ G.desc c) (hx₂ : G.Adj x₂ h) (hx₂c : x₂ ∉ G.desc c)
    {p : V} (hp : p ∈ W.support) (hpv : p ≠ v) (hph : p ≠ h) :
    G.indeg p = 1 ∧ ∃ s q, (∀ x, G.Adj p x ↔ x = s ∨ x = q) ∧ s ≠ q ∧ s ∈ W.support ∧
      h ∉ G.desc q ∧ G.EntersOnly p q := by
  have := hG.finite
  obtain ⟨y, hyp, hyW⟩ := exists_adj_mem_edges_of_ne_start W hWd hp hpv
  obtain ⟨s, hps, hsW⟩ := exists_adj_mem_edges_of_ne_end W hWd hp hph
  have hpC : p ∈ C.support := hWs p hp
  have hyC : s(p, y) ∈ C.edges := Sym2.eq_swap ▸ hWC _ hyW
  have hsC : s(p, s) ∈ C.edges := hWC _ hsW
  have hys : y ≠ s := fun h' => hG.not_adj_of_adj hps (h' ▸ hyp)
  -- the neighbours of `p` along `C` are `y` and `s`
  have hnb : ∀ x, s(p, x) ∈ C.edges → x = y ∨ x = s :=
    fun x hx => eq_or_eq_of_mem_edges_of_isCycle hC hyC hsC hys hx
  -- `y` is the only parent of `p`
  have hpar : ∀ x, G.Adj x p ↔ x = y := by
    refine fun x => ⟨fun hxp => ?_, fun h' => h' ▸ hyp⟩
    by_contra hxy
    have hxC : s(p, x) ∉ C.edges := by
      intro hx
      rcases hnb x hx with h' | h'
      · exact hxy h'
      · exact hG.not_adj_of_adj hps (h' ▸ hxp)
    have hbr := hG.isBridge_of_isCycle h1 hC hpC (hG.undirected_adj_iff.2 (Or.inr hxp)) hxC
    rw [Sym2.eq_swap] at hbr
    rcases hG.entersOnly_of_isBridge hxp hbr p (self_mem_desc p) y hyp with h' | ⟨h', -⟩
    · exact hG.not_adj_of_mem_desc h' hyp
    · exact hxy h'.symm
  have hindeg : G.indeg p = 1 := indeg_eq_one_iff.2 ⟨y, hpar⟩
  refine ⟨hindeg, ?_⟩
  -- `p` is a tree node: its children are `s` and another vertex `q`
  have hout : G.outdeg p = 2 := by
    rcases hG.outdeg_of_indeg_eq_one hindeg with h' | h'
    · exact absurd hps (outdeg_eq_zero_iff.1 h' s)
    · exact h'
  obtain ⟨w, w', hww', hch⟩ := outdeg_eq_two_iff.1 hout
  obtain ⟨q, hsq, hch'⟩ : ∃ q, s ≠ q ∧ ∀ x, G.Adj p x ↔ x = s ∨ x = q := by
    rcases (hch s).1 hps with rfl | rfl
    · exact ⟨w', hww', hch⟩
    · exact ⟨w, hww'.symm, fun x => (hch x).trans or_comm⟩
  have hpq : G.Adj p q := (hch' q).2 (Or.inr rfl)
  -- `(p, q)` is a cut edge
  have hqC : s(p, q) ∉ C.edges := by
    intro hq
    rcases hnb q hq with h' | h'
    · exact hG.not_adj_of_adj hpq (h' ▸ hyp)
    · exact hsq h'.symm
  have he : G.EntersOnly p q := hG.entersOnly_of_isBridge hpq
    (hG.isBridge_of_isCycle h1 hC hpC (hG.undirected_adj_of_adj hpq) hqC)
  refine ⟨s, q, hch', hsq, W.snd_mem_support_of_mem_edges hsW, fun hhq => ?_, he⟩
  -- `h` is not below `q`: it is entered from `x₂`, which is not below `c`
  have hpc : p ∈ G.desc c := hWc p hp hpv
  rcases he h hhq x₂ hx₂ with h' | ⟨h', -⟩
  · exact hx₂c (desc_subset hpc (desc_subset (mem_desc_of_adj hpq) h'))
  · exact hx₂c (h' ▸ hpc)

/-- **The nodes of a side.** The vertices other than `h` of a directed path from the child `c` of
`v` to `h`, which with the edge `(v, c)` lies along a cycle `C`, are the nodes of a side of a cycle
with hybrid node `h` (`Phylogenetics.MetricDigraph.IsSideNodes`), given a parent `x₂` of `h` that is
not a descendant of `c`. -/
theorem isSideNodes (h1 : G.IsLevel1) {v c h x₂ : V} {C : G.undirected.Walk v v}
    (hC : C.IsCycle) (hvc : G.Adj v c) {P : G.undirected.Walk c h}
    (hPd : ∀ d ∈ P.darts, G.Adj d.fst d.snd) (hPs : ∀ x ∈ P.support, x ∈ G.desc c ∧ h ∈ G.desc x)
    (hWC : ∀ e ∈ (Walk.cons (hG.undirected_adj_of_adj hvc) P).edges, e ∈ C.edges)
    (hWs : ∀ x ∈ (Walk.cons (hG.undirected_adj_of_adj hvc) P).support, x ∈ C.support)
    (hx₂ : G.Adj x₂ h) (hx₂c : x₂ ∉ G.desc c) :
    G.IsSideNodes c h {p | p ∈ P.support ∧ p ≠ h} := by
  have hv : v ∉ P.support := fun hv => hG.notMem_desc_of_adj hvc (hPs v hv).1
  have hWd : ∀ d ∈ (Walk.cons (hG.undirected_adj_of_adj hvc) P).darts, G.Adj d.fst d.snd := by
    rw [Walk.darts_cons]
    rintro d (_ | ⟨_, hd⟩)
    · exact hvc
    · exact hPd d hd
  have hWc : ∀ x ∈ (Walk.cons (hG.undirected_adj_of_adj hvc) P).support, x ≠ v →
      x ∈ G.desc c := by
    intro x hx hxv
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact absurd rfl hxv
    · exact (hPs x hx).1
  have hnode : ∀ p ∈ {p | p ∈ P.support ∧ p ≠ h}, G.indeg p = 1 ∧ ∃ s q,
      (∀ x, G.Adj p x ↔ x = s ∨ x = q) ∧ s ≠ q ∧
        s ∈ (Walk.cons (hG.undirected_adj_of_adj hvc) P).support ∧
        h ∉ G.desc q ∧ G.EntersOnly p q := fun p ⟨hp, hph⟩ =>
    hG.side_node h1 hC hWd hWC hWs hWc hx₂ hx₂c
      (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hp)
      (fun h' => hv (h' ▸ hp)) hph
  refine ⟨?_, fun p hp => hp.2, fun p hp => (hPs p hp.1).1, fun p hp => (hPs p hp.1).2,
    fun p hp => (hnode p hp).1, fun p hp => ?_⟩
  · by_cases hch : c = h
    · exact Or.inl hch
    · exact Or.inr ⟨P.start_mem_support, hch⟩
  · obtain ⟨s, q, hch, hsq, hsW, hhq, he⟩ := (hnode p hp).2
    refine ⟨s, q, hch, hsq, ?_, hhq, he⟩
    rw [Walk.support_cons, List.mem_cons] at hsW
    rcases hsW with rfl | hsW
    · exact absurd (desc_subset (hPs p hp.1).1 (mem_desc_of_adj ((hch _).2 (Or.inl rfl))))
        (hG.notMem_desc_of_adj hvc)
    · by_cases hsh : s = h
      · exact Or.inl hsh
      · exact Or.inr ⟨hsW, hsh⟩

/-- **The hybrid node of the cycle.** A vertex `h` of a cycle `C` entered along `C` from two
distinct parents is a hybrid node; its only child `c` is not on `C`, so `(h, c)` is a cut edge
(`isBridge_of_isCycle`) and the descendants of `c` are entered only through `(h, c)`. -/
theorem hybrid_node (h1 : G.IsLevel1) {v h x₁ x₂ : V} {C : G.undirected.Walk v v}
    (hC : C.IsCycle) (hx₁ : G.Adj x₁ h) (hx₂ : G.Adj x₂ h) (hx₁₂ : x₁ ≠ x₂)
    (hx₁C : s(x₁, h) ∈ C.edges) (hx₂C : s(x₂, h) ∈ C.edges) :
    G.IsHybrid h ∧ ∃ c, (∀ x, G.Adj h x ↔ x = c) ∧ G.EntersOnly h c := by
  have := hG.finite
  have hin : 2 ≤ G.indeg h := by
    rw [indeg, ← Set.ncard_pair hx₁₂]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro x (rfl | rfl)
    · exact hx₁
    · exact hx₂
  have hhyb : G.IsHybrid h := by
    rcases hG.degrees h with h' | h' | h' | h'
    · have := h'.1; omega
    · have := h'.1; omega
    · have := h'.1; omega
    · exact h'
  obtain ⟨c, hc⟩ := outdeg_eq_one_iff.1 hhyb.2
  have hhc : G.Adj h c := (hc c).2 rfl
  have h₁C : s(h, x₁) ∈ C.edges := Sym2.eq_swap ▸ hx₁C
  have h₂C : s(h, x₂) ∈ C.edges := Sym2.eq_swap ▸ hx₂C
  have hcC : s(h, c) ∉ C.edges := by
    intro h'
    rcases eq_or_eq_of_mem_edges_of_isCycle hC h₁C h₂C hx₁₂ h' with rfl | rfl
    · exact hG.not_adj_of_adj hx₁ hhc
    · exact hG.not_adj_of_adj hx₂ hhc
  refine ⟨hhyb, c, hc, hG.entersOnly_of_isBridge hhc ?_⟩
  exact hG.isBridge_of_isCycle h1 hC (C.fst_mem_support_of_mem_edges h₁C)
    (hG.undirected_adj_of_adj hhc) hcC

end IsBinary

/-- **The cycle below a vertex.** In a binary level-1 network, let `v` have the children
`c₁ ≠ c₂`, with a common descendant. Then `v` is the top node of a cycle: there is a common
descendant `h` of `c₁` and `c₂`, a descendant of no other common descendant, which is a hybrid
node whose only child `c` roots a subnetwork entered only through `(h, c)`; the two sides of the
cycle, from `c₁` and from `c₂` to `h`, consist of nodes as described by
`Phylogenetics.MetricDigraph.IsSideNodes`. -/
theorem IsBinary.exists_cycle (hG : G.IsBinary) (h1 : G.IsLevel1) {v c₁ c₂ : V}
    (hvc : ∀ x, G.Adj v x ↔ x = c₁ ∨ x = c₂) (hne : c₁ ≠ c₂)
    (hint : (G.desc c₁ ∩ G.desc c₂).Nonempty) :
    ∃ h c, h ∈ G.desc c₁ ∧ h ∈ G.desc c₂ ∧
      (∀ y ∈ G.desc c₁ ∩ G.desc c₂, h ∈ G.desc y → y = h) ∧ G.IsHybrid h ∧
      (∀ x, G.Adj h x ↔ x = c) ∧ G.EntersOnly h c ∧
      (∃ P, G.IsSideNodes c₁ h P) ∧ ∃ P, G.IsSideNodes c₂ h P := by
  have hvc₁ : G.Adj v c₁ := (hvc c₁).2 (Or.inl rfl)
  have hvc₂ : G.Adj v c₂ := (hvc c₂).2 (Or.inr rfl)
  obtain ⟨h, ⟨hh₁, hh₂⟩, hmin⟩ := hG.exists_minimal_common_desc hint
  have hmin' : ∀ y ∈ G.desc c₂ ∩ G.desc c₁, h ∈ G.desc y → y = h :=
    fun y hy => hmin y ⟨hy.2, hy.1⟩
  have hvh : h ≠ v := fun h' => hG.notMem_desc_of_adj hvc₁ (h' ▸ hh₁)
  obtain ⟨P₁, hP₁, hP₁d, hP₁s⟩ := hG.exists_isPath_of_reflTransGen hh₁
  obtain ⟨P₂, hP₂, hP₂d, hP₂s⟩ := hG.exists_isPath_of_reflTransGen hh₂
  have hP₁s' : ∀ x ∈ P₁.support, x ∈ G.desc c₁ ∧ h ∈ G.desc x := hP₁s
  have hP₂s' : ∀ x ∈ P₂.support, x ∈ G.desc c₂ ∧ h ∈ G.desc x := hP₂s
  have hv₁ : v ∉ P₁.support := fun hv => hG.notMem_desc_of_adj hvc₁ (hP₁s' v hv).1
  have hv₂ : v ∉ P₂.support := fun hv => hG.notMem_desc_of_adj hvc₂ (hP₂s' v hv).1
  set W₁ := Walk.cons (hG.undirected_adj_of_adj hvc₁) P₁ with hW₁
  set W₂ := Walk.cons (hG.undirected_adj_of_adj hvc₂) P₂ with hW₂
  have hW₁d : ∀ d ∈ W₁.darts, G.Adj d.fst d.snd := by
    rw [hW₁, Walk.darts_cons]
    rintro d (_ | ⟨_, hd⟩)
    · exact hvc₁
    · exact hP₁d d hd
  have hW₂d : ∀ d ∈ W₂.darts, G.Adj d.fst d.snd := by
    rw [hW₂, Walk.darts_cons]
    rintro d (_ | ⟨_, hd⟩)
    · exact hvc₂
    · exact hP₂d d hd
  have hC₁ : (W₁.append W₂.reverse).IsCycle :=
    hG.isCycle_append_reverse hvc₁ hvc₂ hne hmin hP₁ hP₁s' hP₂ hP₂s'
  have hC₂ : (W₂.append W₁.reverse).IsCycle :=
    hG.isCycle_append_reverse hvc₂ hvc₁ hne.symm hmin' hP₂ hP₂s' hP₁ hP₁s'
  -- the parents of `h` along the two paths
  obtain ⟨x₁, hx₁, hx₁W⟩ := exists_adj_mem_edges_of_ne_start W₁ hW₁d W₁.end_mem_support hvh
  obtain ⟨x₂, hx₂, hx₂W⟩ := exists_adj_mem_edges_of_ne_start W₂ hW₂d W₂.end_mem_support hvh
  -- a parent of `h` along the path through `c₂` is not a descendant of `c₁`, and conversely
  have hx₂c : x₂ ∉ G.desc c₁ := by
    intro hx
    have hxW := W₂.fst_mem_support_of_mem_edges hx₂W
    rw [hW₂, Walk.support_cons, List.mem_cons] at hxW
    rcases hxW with rfl | hxW
    · exact hG.notMem_desc_of_adj hvc₁ hx
    · exact hG.ne_of_adj hx₂ (hmin x₂ ⟨hx, (hP₂s' x₂ hxW).1⟩ (hP₂s' x₂ hxW).2)
  have hx₁c : x₁ ∉ G.desc c₂ := by
    intro hx
    have hxW := W₁.fst_mem_support_of_mem_edges hx₁W
    rw [hW₁, Walk.support_cons, List.mem_cons] at hxW
    rcases hxW with rfl | hxW
    · exact hG.notMem_desc_of_adj hvc₂ hx
    · exact hG.ne_of_adj hx₁ (hmin' x₁ ⟨hx, (hP₁s' x₁ hxW).1⟩ (hP₁s' x₁ hxW).2)
  have hx₁₂ : x₁ ≠ x₂ := by
    intro h₁₂
    have hxW := W₁.fst_mem_support_of_mem_edges hx₁W
    rw [hW₁, Walk.support_cons, List.mem_cons] at hxW
    rcases hxW with hxv | hxW
    · subst hxv
      subst h₁₂
      exact hne ((eq_of_mem_edges_cons hv₁ hx₁W).symm.trans (eq_of_mem_edges_cons hv₂ hx₂W))
    · exact hx₂c (h₁₂ ▸ (hP₁s' x₁ hxW).1)
  have hW₁C₁ : ∀ e ∈ W₁.edges, e ∈ (W₁.append W₂.reverse).edges := fun e he => by
    rw [Walk.edges_append]
    exact List.mem_append_left _ he
  have hW₂C₁ : ∀ e ∈ W₂.edges, e ∈ (W₁.append W₂.reverse).edges := fun e he => by
    rw [Walk.edges_append, Walk.edges_reverse]
    exact List.mem_append_right _ (List.mem_reverse.2 he)
  have hW₂C₂ : ∀ e ∈ W₂.edges, e ∈ (W₂.append W₁.reverse).edges := fun e he => by
    rw [Walk.edges_append]
    exact List.mem_append_left _ he
  obtain ⟨hhyb, c, hc, he⟩ :=
    hG.hybrid_node h1 hC₁ hx₁ hx₂ hx₁₂ (hW₁C₁ _ hx₁W) (hW₂C₁ _ hx₂W)
  refine ⟨h, c, hh₁, hh₂, hmin, hhyb, hc, he, ⟨_, hG.isSideNodes h1 hC₁ hvc₁ hP₁d hP₁s' hW₁C₁
    (fun x hx => ?_) hx₂ hx₂c⟩, ⟨_, hG.isSideNodes h1 hC₂ hvc₂ hP₂d hP₂s' hW₂C₂
    (fun x hx => ?_) hx₁ hx₁c⟩⟩
  · rw [Walk.support_append]
    exact List.mem_append_left _ hx
  · rw [Walk.support_append]
    exact List.mem_append_left _ hx

end MetricDigraph

end Phylogenetics
