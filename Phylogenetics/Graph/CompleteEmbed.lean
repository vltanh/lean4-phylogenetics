module

public import Phylogenetics.Graph.CompleteDesc
public import Phylogenetics.Graph.OfNet
/-!
# Embedding the constructions of `Phylogenetics.Graph.OfNet` in a network

`Phylogenetics.Graph.Complete` describes a rooted binary metric level-1 network `G` by a network
term, going down from the root, and finds the graph of the term inside `G`. This module provides
the steps.

* `Phylogenetics.MetricDigraph.Embeds G H f S`: the map `f` embeds the graph `H` in `G`, onto the
  set `S` of vertices: it is injective with image `S`, and preserves the edges in both directions,
  the labels, the lengths of the edges and the inheritance probabilities of the edges ending at a
  hybrid node of `G`. Onto all the vertices of `G`, the inverse of `f` is an isomorphism
  (`Phylogenetics.MetricDigraph.Embeds.nonempty_iso`).
* `Phylogenetics.MetricDigraph.SideEmbeds G S f h u p`: the same for the graph of a side of a cycle
  with hybrid node `h`, from the first node `p` of the side (whose parent is `u`), onto the
  descendants of `p` that are not descendants of `h`, with its first and last nodes and the lengths
  of its edges to `u` and to `h`.
* The constructions of `Phylogenetics.Graph.OfNet` embed in `G` when their parts do and the vertices
  of `G` around them are arranged as in the construction: `Phylogenetics.MetricDigraph.embeds_leaf`,
  `Phylogenetics.MetricDigraph.IsBinary.embeds_tree`, `Phylogenetics.MetricDigraph.sideEmbeds_hyb`,
  `Phylogenetics.MetricDigraph.IsBinary.sideEmbeds_node` and
  `Phylogenetics.MetricDigraph.IsBinary.embeds_cycle`. -/

@[expose] public noncomputable section

namespace Phylogenetics

universe u v w

/-- The map on the vertices of a tree node with two subnetworks (`Phylogenetics.TreeVert`) that
sends the node to `v` and the vertices of the subnetworks along `f₁` and `f₂`. -/
def TreeVert.elim {A B : Type} {V : Sort*} (v : V) (f₁ : A → V) (f₂ : B → V) :
    TreeVert A B → V
  | .root => v
  | .left a => f₁ a
  | .right b => f₂ b

/-- The map on the vertices of a side `Side.node ℓ b N S` (`Phylogenetics.NodeVert`) that sends its
first node to `p`, the vertices of `N` along `g` and those of the rest `S` along `f`. -/
def NodeVert.elim {A B : Type} {V : Sort*} (p : V) (g : A → V) (f : B → V) : NodeVert A B → V
  | .node => p
  | .pendant a => g a
  | .rest c => f c

/-- The map on the vertices of a cycle with its sides and the network below its hybrid node
(`Phylogenetics.CycleVert`) that sends the top node to `v`, the vertices of the sides along `f₁` and
`f₂`, the hybrid node to `h` and the vertices below it along `g`. -/
def CycleVert.elim {A B C : Type} {V : Sort*} (v : V) (f₁ : A → V) (f₂ : B → V) (h : V)
    (g : C → V) : CycleVert A B C → V
  | .top => v
  | .side₁ a => f₁ a
  | .side₂ b => f₂ b
  | .hyb => h
  | .below c => g c

namespace MetricDigraph

variable {V : Type u} {X : Type v} {G : MetricDigraph V X}

/-- The map `f` embeds the graph `H` in `G`, onto the set `S` of vertices of `G`: `f` is injective
with image `S`, and preserves the edges in both directions, the labels, the lengths of the edges,
and the inheritance probabilities of the edges whose end is a hybrid node of `G`. -/
structure Embeds {W : Type w} (G : MetricDigraph V X) (H : MetricDigraph W X) (f : W → V)
    (S : Set V) : Prop where
  /-- The map is injective. -/
  injective : Function.Injective f
  /-- The image lies in `S`. -/
  mem : ∀ a, f a ∈ S
  /-- Every vertex of `S` is in the image. -/
  surj : ∀ x ∈ S, ∃ a, f a = x
  /-- The edges are preserved in both directions. -/
  adj_iff : ∀ a b, G.Adj (f a) (f b) ↔ H.Adj a b
  /-- The labels are preserved. -/
  label_eq : ∀ a, G.label (f a) = H.label a
  /-- The lengths of the edges are preserved. -/
  len_eq : ∀ a b, H.Adj a b → G.len (f a) (f b) = H.len a b
  /-- The inheritance probabilities of the edges ending at hybrid nodes of `G` are preserved. -/
  inh_eq : ∀ a b, H.Adj a b → G.IsHybrid (f b) → G.inh (f a) (f b) = H.inh a b

/-- The map `f` embeds the graph of a side `S` of a cycle with hybrid node `h` in `G`: the graph
of the side onto the descendants of `p` that are not descendants of `h`, where `p` is the first
node of the side (`p = h` for a side that is a single hybrid edge, from `u` to `h`) and `u` its
parent (the top node of the cycle, or the previous node of the side). The first node of `S` is
sent to `p`, its last node to the parent of `h` in the side; the length of the edge from the top
is that of `(u, p)`, the length of the hybrid edge that of the edge from the last node (or from
`u`) to `h`. -/
structure SideEmbeds {W : Type} (G : MetricDigraph V X) (S : SideGraph W X) (f : W → V)
    (h u p : V) : Prop where
  /-- The graph of the side embeds onto the descendants of `p` that are not below `h`. -/
  embeds : G.Embeds S.graph f (G.desc p \ G.desc h)
  /-- The side has no node exactly when `p = h`. -/
  first_eq_none : S.first = none ↔ p = h
  /-- The first node is sent to `p`. -/
  first_eq_some : ∀ a, S.first = some a ↔ f a = p
  /-- The side has no last node exactly when `p = h`. -/
  last_eq_none : S.last = none ↔ p = h
  /-- The last node is sent to the parent of `h` in the side. -/
  last_eq_some : ∀ a, S.last = some a ↔ G.Adj (f a) h
  /-- The edge from the top has the length of `(u, p)`. -/
  topLen_eq : S.topLen = G.len u p
  /-- For a side with no node, the hybrid edge has the length of `(u, h)`. -/
  hybLen_eq_of_none : S.last = none → S.hybLen = G.len u h
  /-- The hybrid edge has the length of the edge from the last node to `h`. -/
  hybLen_eq : ∀ a, S.last = some a → S.hybLen = G.len (f a) h

/-! ### A leaf -/

/-- A vertex without children, labelled `x`, is the image of the graph of the leaf `x`. -/
theorem embeds_leaf {v : V} {x : X} (hv : ∀ w, ¬ G.Adj v w) (hl : G.label v = some x) :
    G.Embeds (MetricDigraph.leaf x) (fun _ => v) (G.desc v) where
  injective _ _ _ := rfl
  mem _ := self_mem_desc v
  surj _ hw := ⟨(), ((mem_desc_iff_of_forall_not_adj hv).1 hw).symm⟩
  adj_iff _ _ := iff_of_false (hv v) id
  label_eq _ := hl
  len_eq _ _ h := False.elim h
  inh_eq _ _ h := False.elim h

/-! ### A side with no node -/

/-- A side with no node, a single hybrid edge from `u` to `h`: the graph of `Side.hyb` with the
length of `(u, h)`. -/
theorem sideEmbeds_hyb {h u : V} :
    G.SideEmbeds (SideGraph.hyb (G.len u h)) (Empty.elim : Empty → V) h u h where
  embeds :=
    { injective := fun a => a.elim
      mem := fun a => a.elim
      surj := fun _ hw => absurd hw.1 hw.2
      adj_iff := fun a => a.elim
      label_eq := fun a => a.elim
      len_eq := fun a => a.elim
      inh_eq := fun a => a.elim }
  first_eq_none := iff_of_true rfl rfl
  first_eq_some a := a.elim
  last_eq_none := iff_of_true rfl rfl
  last_eq_some a := a.elim
  topLen_eq := rfl
  hybLen_eq_of_none _ := rfl
  hybLen_eq a := a.elim

namespace IsBinary

variable (hG : G.IsBinary)
include hG

/-! ### A tree node on no cycle -/

/-- **A tree node on no cycle.** If `v` has the children `c₁` and `c₂`, with disjoint sets of
descendants, and the graphs `G₁` and `G₂` embed onto the descendants of `c₁` and `c₂` with their
roots `r₁` and `r₂` sent to `c₁` and `c₂`, the graph of the tree node with the subnetworks `G₁`
and `G₂` embeds onto the descendants of `v`. -/
theorem embeds_tree {v c₁ c₂ : V} (hc : ∀ x, G.Adj v x ↔ x = c₁ ∨ x = c₂)
    (hdisj : Disjoint (G.desc c₁) (G.desc c₂)) (hlabel : G.label v = none)
    (hhyb₁ : ¬ G.IsHybrid c₁) (hhyb₂ : ¬ G.IsHybrid c₂)
    {A B : Type} {G₁ : MetricDigraph A X} {r₁ : A} {G₂ : MetricDigraph B X} {r₂ : B}
    {f₁ : A → V} {f₂ : B → V} (h₁ : G.Embeds G₁ f₁ (G.desc c₁)) (hr₁ : f₁ r₁ = c₁)
    (h₂ : G.Embeds G₂ f₂ (G.desc c₂)) (hr₂ : f₂ r₂ = c₂) :
    G.Embeds (MetricDigraph.tree (G.len v c₁) G₁ r₁ (G.len v c₂) G₂ r₂) (TreeVert.elim v f₁ f₂)
      (G.desc v) := by
  have hvc₁ : G.Adj v c₁ := (hc c₁).2 (Or.inl rfl)
  have hvc₂ : G.Adj v c₂ := (hc c₂).2 (Or.inr rfl)
  have hsub₁ : G.desc c₁ ⊆ G.desc v := desc_subset (mem_desc_of_adj hvc₁)
  have hsub₂ : G.desc c₂ ⊆ G.desc v := desc_subset (mem_desc_of_adj hvc₂)
  have hne₁ : ∀ a, f₁ a ≠ v := fun a h => hG.notMem_desc_of_adj hvc₁ (h ▸ h₁.mem a)
  have hne₂ : ∀ b, f₂ b ≠ v := fun b h => hG.notMem_desc_of_adj hvc₂ (h ▸ h₂.mem b)
  have hd : ∀ a b, f₁ a ≠ f₂ b := fun a b h =>
    Set.disjoint_left.1 hdisj (h₁.mem a) (h ▸ h₂.mem b)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (_ | a | b) (_ | a' | b') h
    · rfl
    · exact absurd h.symm (hne₁ a')
    · exact absurd h.symm (hne₂ b')
    · exact absurd h (hne₁ a)
    · exact congrArg _ (h₁.injective h)
    · exact absurd h (hd a b')
    · exact absurd h (hne₂ b)
    · exact absurd h.symm (hd a' b)
    · exact congrArg _ (h₂.injective h)
  · rintro (_ | a | b)
    · exact self_mem_desc v
    · exact hsub₁ (h₁.mem a)
    · exact hsub₂ (h₂.mem b)
  · intro x hx
    rcases (mem_desc_iff_of_adj_iff hc).1 hx with rfl | hx | hx
    · exact ⟨.root, rfl⟩
    · obtain ⟨a, rfl⟩ := h₁.surj x hx
      exact ⟨.left a, rfl⟩
    · obtain ⟨b, rfl⟩ := h₂.surj x hx
      exact ⟨.right b, rfl⟩
  · rintro (_ | a | b) (_ | a' | b')
    · exact iff_of_false (hG.not_adj_self v) id
    · show G.Adj v (f₁ a') ↔ a' = r₁
      refine ⟨fun h => ?_, fun h => h ▸ hr₁ ▸ hvc₁⟩
      rcases (hc _).1 h with h | h
      · exact h₁.injective (h.trans hr₁.symm)
      · exact absurd (h₁.mem a') (Set.disjoint_right.1 hdisj (by rw [h]; exact self_mem_desc c₂))
    · show G.Adj v (f₂ b') ↔ b' = r₂
      refine ⟨fun h => ?_, fun h => h ▸ hr₂ ▸ hvc₂⟩
      rcases (hc _).1 h with h | h
      · exact absurd (h₂.mem b') (Set.disjoint_left.1 hdisj (by rw [h]; exact self_mem_desc c₁))
      · exact h₂.injective (h.trans hr₂.symm)
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₁ (h₁.mem a))) id
    · exact h₁.adj_iff a a'
    · exact iff_of_false (fun h => Set.disjoint_left.1 hdisj
        (mem_desc_of_mem_of_adj (h₁.mem a) h) (h₂.mem b')) id
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₂ (h₂.mem b))) id
    · exact iff_of_false (fun h => Set.disjoint_left.1 hdisj (h₁.mem a')
        (mem_desc_of_mem_of_adj (h₂.mem b) h)) id
    · exact h₂.adj_iff b b'
  · rintro (_ | a | b)
    · exact hlabel
    · exact h₁.label_eq a
    · exact h₂.label_eq b
  · rintro (_ | a | b) (_ | a' | b') hadj
    all_goals first
      | exact False.elim hadj
      | exact h₁.len_eq _ _ hadj
      | exact h₂.len_eq _ _ hadj
      | skip
    · show G.len v (f₁ a') = G.len v c₁
      rw [show a' = r₁ from hadj, hr₁]
    · show G.len v (f₂ b') = G.len v c₂
      rw [show b' = r₂ from hadj, hr₂]
  · rintro (_ | a | b) (_ | a' | b') hadj hhyb
    all_goals first
      | exact False.elim hadj
      | exact h₁.inh_eq _ _ hadj hhyb
      | exact h₂.inh_eq _ _ hadj hhyb
      | skip
    · change G.IsHybrid (f₁ a') at hhyb
      rw [show a' = r₁ from hadj, hr₁] at hhyb
      exact absurd hhyb hhyb₁
    · change G.IsHybrid (f₂ b') at hhyb
      rw [show b' = r₂ from hadj, hr₂] at hhyb
      exact absurd hhyb hhyb₂

/-! ### A node of a side of a cycle -/

/-- **A node of a side of a cycle.** Let `p` be a node of a side of a cycle with hybrid node `h`,
with parent `u`, children `s` (the next node of the side, or `h`) and `q` (the root of the
network hanging from `p`), the descendants of `q` entered only through `(p, q)` and disjoint from
those of `s` and `h`. If the graph `H` embeds onto the descendants of `q`, its root `r` sent to `q`,
and the rest of the side embeds from `s`, the side `Side.node` with the lengths of `(u, p)` and
`(p, q)` embeds from `p`. -/
theorem sideEmbeds_node {h u p s q : V} (hc : ∀ x, G.Adj p x ↔ x = s ∨ x = q)
    (hph : p ∉ G.desc h) (hqh : Disjoint (G.desc q) (G.desc h))
    (hqs : Disjoint (G.desc q) (G.desc s)) (he : G.EntersOnly p q) (hlabel : G.label p = none)
    (hq : ¬ G.IsHybrid q) (hs : s ≠ h → ¬ G.IsHybrid s)
    {A B : Type} {H : MetricDigraph A X} {r : A} {S : SideGraph B X} {g : A → V} {f : B → V}
    (hH : G.Embeds H g (G.desc q)) (hr : g r = q) (hS : G.SideEmbeds S f h p s) :
    G.SideEmbeds (SideGraph.node (G.len u p) (G.len p q) H r S) (NodeVert.elim p g f) h u p := by
  have hps : G.Adj p s := (hc s).2 (Or.inl rfl)
  have hpq : G.Adj p q := (hc q).2 (Or.inr rfl)
  have hsubq : G.desc q ⊆ G.desc p := desc_subset (mem_desc_of_adj hpq)
  have hsubs : G.desc s ⊆ G.desc p := desc_subset (mem_desc_of_adj hps)
  have hf : ∀ c, f c ∈ G.desc s ∧ f c ∉ G.desc h := fun c => hS.embeds.mem c
  have hneg : ∀ a, g a ≠ p := fun a =>
    ne_of_mem_of_not_mem (hH.mem a) (hG.notMem_desc_of_adj hpq)
  have hnef : ∀ c, f c ≠ p := fun c =>
    ne_of_mem_of_not_mem (hf c).1 (hG.notMem_desc_of_adj hps)
  have hd : ∀ a c, g a ≠ f c := fun a c =>
    ne_of_mem_of_not_mem (hH.mem a) (Set.disjoint_right.1 hqs (hf c).1)
  have hp_ne_h : p ≠ h := (ne_of_mem_of_not_mem (self_mem_desc h) hph).symm
  have hfirst : ∀ c, S.first = some c → s ≠ h := fun c h₁ h₂ => by
    rw [hS.first_eq_none.2 h₂] at h₁
    exact Option.some_ne_none _ h₁.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  -- the embedding: injective
  · rintro (_ | a | c) (_ | a' | c') h'
    · rfl
    · exact absurd h'.symm (hneg a')
    · exact absurd h'.symm (hnef c')
    · exact absurd h' (hneg a)
    · exact congrArg _ (hH.injective h')
    · exact absurd h' (hd a c')
    · exact absurd h' (hnef c)
    · exact absurd h'.symm (hd a' c)
    · exact congrArg _ (hS.embeds.injective h')
  -- onto the descendants of `p` not below `h`
  · rintro (_ | a | c)
    · exact ⟨self_mem_desc p, hph⟩
    · exact ⟨hsubq (hH.mem a), Set.disjoint_left.1 hqh (hH.mem a)⟩
    · exact ⟨hsubs (hf c).1, (hf c).2⟩
  · rintro x ⟨hx, hxh⟩
    rcases (mem_desc_iff_of_adj_iff hc).1 hx with rfl | hx | hx
    · exact ⟨.node, rfl⟩
    · obtain ⟨c, rfl⟩ := hS.embeds.surj x ⟨hx, hxh⟩
      exact ⟨.rest c, rfl⟩
    · obtain ⟨a, rfl⟩ := hH.surj x hx
      exact ⟨.pendant a, rfl⟩
  -- the edges
  · rintro (_ | a | c) (_ | a' | c')
    · exact iff_of_false (hG.not_adj_self p) id
    · show G.Adj p (g a') ↔ a' = r
      refine ⟨fun h' => ?_, fun h' => h' ▸ hr ▸ hpq⟩
      rcases (hc _).1 h' with h' | h'
      · exact absurd (hH.mem a') (Set.disjoint_right.1 hqs (by rw [h']; exact self_mem_desc s))
      · exact hH.injective (h'.trans hr.symm)
    · show G.Adj p (f c') ↔ S.first = some c'
      rw [hS.first_eq_some]
      refine ⟨fun h' => ?_, fun h' => h' ▸ hps⟩
      rcases (hc _).1 h' with h' | h'
      · exact h'
      · exact absurd (hf c').1 (Set.disjoint_left.1 hqs (by rw [h']; exact self_mem_desc q))
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsubq (hH.mem a))) id
    · exact hH.adj_iff a a'
    · exact iff_of_false (fun h' => Set.disjoint_left.1 hqs
        (mem_desc_of_mem_of_adj (hH.mem a) h') (hf c').1) id
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsubs (hf c).1)) id
    · refine iff_of_false (fun h' => ?_) id
      rcases he _ (hH.mem a') _ h' with h'' | ⟨h'', -⟩
      · exact Set.disjoint_left.1 hqs h'' (hf c).1
      · exact hnef c h''
    · exact hS.embeds.adj_iff c c'
  -- the labels
  · rintro (_ | a | c)
    · exact hlabel
    · exact hH.label_eq a
    · exact hS.embeds.label_eq c
  -- the lengths
  · rintro (_ | a | c) (_ | a' | c') hadj
    all_goals first
      | exact False.elim hadj
      | exact hH.len_eq _ _ hadj
      | exact hS.embeds.len_eq _ _ hadj
      | skip
    · show G.len p (g a') = G.len p q
      rw [show a' = r from hadj, hr]
    · show G.len p (f c') = S.topLen
      rw [(hS.first_eq_some c').1 hadj, hS.topLen_eq]
  -- the inheritance probabilities
  · rintro (_ | a | c) (_ | a' | c') hadj hhyb
    all_goals first
      | exact False.elim hadj
      | exact hH.inh_eq _ _ hadj hhyb
      | exact hS.embeds.inh_eq _ _ hadj hhyb
      | skip
    · change G.IsHybrid (g a') at hhyb
      rw [show a' = r from hadj, hr] at hhyb
      exact absurd hhyb hq
    · change G.IsHybrid (f c') at hhyb
      rw [(hS.first_eq_some c').1 hadj] at hhyb
      exact absurd hhyb (hs (hfirst c' hadj))
  -- the first node
  · exact iff_of_false (Option.some_ne_none _) hp_ne_h
  · rintro (_ | a | c)
    · exact iff_of_true rfl rfl
    · exact iff_of_false (by simp [SideGraph.node]) (hneg a)
    · exact iff_of_false (by simp [SideGraph.node]) (hnef c)
  -- the last node
  · exact iff_of_false (Option.some_ne_none _) hp_ne_h
  · intro x
    show some ((S.last.map NodeVert.rest).getD NodeVert.node) = some x ↔ _
    rw [Option.some_inj]
    rcases hlast : S.last with _ | c
    · have hsh : s = h := hS.last_eq_none.1 hlast
      rcases x with _ | a | c'
      · exact iff_of_true rfl (hsh ▸ hps)
      · refine iff_of_false (by simp) fun h' => ?_
        exact Set.disjoint_left.1 hqh (mem_desc_of_mem_of_adj (hH.mem a) h') (self_mem_desc h)
      · refine iff_of_false (by simp) fun _ => ?_
        have := (hf c').1
        rw [hsh] at this
        exact (hf c').2 this
    · rcases x with _ | a | c'
      · refine iff_of_false (by simp) fun h' => ?_
        rcases (hc h).1 h' with h'' | h''
        · rw [hS.last_eq_none.2 h''.symm] at hlast
          exact Option.some_ne_none _ hlast.symm
        · exact Set.disjoint_left.1 hqh (self_mem_desc q) (by rw [← h'']; exact self_mem_desc h)
      · refine iff_of_false (by simp) fun h' => ?_
        exact Set.disjoint_left.1 hqh (mem_desc_of_mem_of_adj (hH.mem a) h') (self_mem_desc h)
      · show NodeVert.rest c = NodeVert.rest c' ↔ G.Adj (f c') h
        rw [← hS.last_eq_some, hlast]
        simp
  -- the length of the hybrid edge
  · exact fun h' => absurd h' (Option.some_ne_none _)
  · intro x hx
    change some ((S.last.map NodeVert.rest).getD NodeVert.node) = some x at hx
    rw [Option.some_inj] at hx
    rcases hlast : S.last with _ | c
    · rw [hlast] at hx
      subst hx
      exact hS.hybLen_eq_of_none hlast
    · rw [hlast] at hx
      subst hx
      exact hS.hybLen_eq c hlast

/-! ### A cycle -/

/-- **A cycle.** Let `v` be the top node of a cycle with hybrid node `h`: `v` has the children `c₁`
and `c₂`, both ancestors of `h`; the descendants of `c₁` not below `h` are not descendants of `c₂`,
and the other way around; `h` has the only child `c`, the descendants of `c` being entered only
through `(h, c)`. If the two sides embed from `c₁` and `c₂`, and the graph `H` onto the
descendants of `c` with its root `r` sent to `c`, and `γ` and `1 - γ` are the inheritance
probabilities of the hybrid edges ending the two sides, the graph of the cycle embeds onto the
descendants of `v`. -/
theorem embeds_cycle {v c₁ c₂ h c : V} {γ : ℝ} (hvc : ∀ x, G.Adj v x ↔ x = c₁ ∨ x = c₂)
    (hhc : ∀ x, G.Adj h x ↔ x = c) (hh₁ : h ∈ G.desc c₁) (hh₂ : h ∈ G.desc c₂)
    (hd₁ : Disjoint (G.desc c₁ \ G.desc h) (G.desc c₂))
    (hd₂ : Disjoint (G.desc c₂ \ G.desc h) (G.desc c₁))
    (he : G.EntersOnly h c) (hlv : G.label v = none) (hlh : G.label h = none)
    (hc₁ : c₁ ≠ h → ¬ G.IsHybrid c₁) (hc₂ : c₂ ≠ h → ¬ G.IsHybrid c₂) (hc : ¬ G.IsHybrid c)
    {A B C : Type} {S₁ : SideGraph A X} {S₂ : SideGraph B X} {H : MetricDigraph C X} {r : C}
    {f₁ : A → V} {f₂ : B → V} {g : C → V}
    (hS₁ : G.SideEmbeds S₁ f₁ h v c₁) (hS₂ : G.SideEmbeds S₂ f₂ h v c₂)
    (hH : G.Embeds H g (G.desc c)) (hr : g r = c)
    (hγ₁ : ∀ a, S₁.last = some a → G.inh (f₁ a) h = γ) (hγ₁' : S₁.last = none → G.inh v h = γ)
    (hγ₂ : ∀ b, S₂.last = some b → G.inh (f₂ b) h = 1 - γ)
    (hγ₂' : S₂.last = none → G.inh v h = 1 - γ) :
    G.Embeds (MetricDigraph.cycle γ S₁ S₂ (G.len h c) H r) (CycleVert.elim v f₁ f₂ h g)
      (G.desc v) := by
  have hvc₁ : G.Adj v c₁ := (hvc c₁).2 (Or.inl rfl)
  have hvc₂ : G.Adj v c₂ := (hvc c₂).2 (Or.inr rfl)
  have hhc' : G.Adj h c := (hhc c).2 rfl
  have hsub₁ : G.desc c₁ ⊆ G.desc v := desc_subset (mem_desc_of_adj hvc₁)
  have hsub₂ : G.desc c₂ ⊆ G.desc v := desc_subset (mem_desc_of_adj hvc₂)
  have hsubh : G.desc h ⊆ G.desc c₁ := desc_subset hh₁
  have hsubc : G.desc c ⊆ G.desc h := desc_subset (mem_desc_of_adj hhc')
  have hv₁ : v ∉ G.desc c₁ := hG.notMem_desc_of_adj hvc₁
  have hv₂ : v ∉ G.desc c₂ := hG.notMem_desc_of_adj hvc₂
  have hhc_ : h ∉ G.desc c := hG.notMem_desc_of_adj hhc'
  have hf₁ : ∀ a, f₁ a ∈ G.desc c₁ ∧ f₁ a ∉ G.desc h := fun a => hS₁.embeds.mem a
  have hf₂ : ∀ b, f₂ b ∈ G.desc c₂ ∧ f₂ b ∉ G.desc h := fun b => hS₂.embeds.mem b
  have hg : ∀ x, g x ∈ G.desc c := hH.mem
  have hv_h : v ≠ h := (ne_of_mem_of_not_mem hh₁ hv₁).symm
  have h1v : ∀ a, f₁ a ≠ v := fun a => ne_of_mem_of_not_mem (hf₁ a).1 hv₁
  have h2v : ∀ b, f₂ b ≠ v := fun b => ne_of_mem_of_not_mem (hf₂ b).1 hv₂
  have hgv : ∀ x, g x ≠ v := fun x => ne_of_mem_of_not_mem (hsubh (hsubc (hg x))) hv₁
  have h12 : ∀ a b, f₁ a ≠ f₂ b := fun a b =>
    (ne_of_mem_of_not_mem (hf₂ b).1 (Set.disjoint_left.1 hd₁ (hf₁ a))).symm
  have h1h : ∀ a, f₁ a ≠ h := fun a =>
    (ne_of_mem_of_not_mem (self_mem_desc h) (hf₁ a).2).symm
  have h2h : ∀ b, f₂ b ≠ h := fun b =>
    (ne_of_mem_of_not_mem (self_mem_desc h) (hf₂ b).2).symm
  have h1g : ∀ a x, f₁ a ≠ g x := fun a x =>
    (ne_of_mem_of_not_mem (hsubc (hg x)) (hf₁ a).2).symm
  have h2g : ∀ b x, f₂ b ≠ g x := fun b x =>
    (ne_of_mem_of_not_mem (hsubc (hg x)) (hf₂ b).2).symm
  have hgh : ∀ x, g x ≠ h := fun x => ne_of_mem_of_not_mem (hg x) hhc_
  have hfirst₁ : ∀ a, S₁.first = some a → c₁ ≠ h := fun a h₁ h₂ => by
    rw [hS₁.first_eq_none.2 h₂] at h₁
    exact Option.some_ne_none _ h₁.symm
  have hfirst₂ : ∀ b, S₂.first = some b → c₂ ≠ h := fun b h₁ h₂ => by
    rw [hS₂.first_eq_none.2 h₂] at h₁
    exact Option.some_ne_none _ h₁.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- injective
  · rintro (_ | a | b | _ | x) (_ | a' | b' | _ | x') h'
    · rfl
    · exact absurd h'.symm (h1v a')
    · exact absurd h'.symm (h2v b')
    · exact absurd h' hv_h
    · exact absurd h'.symm (hgv x')
    · exact absurd h' (h1v a)
    · exact congrArg _ (hS₁.embeds.injective h')
    · exact absurd h' (h12 a b')
    · exact absurd h' (h1h a)
    · exact absurd h' (h1g a x')
    · exact absurd h' (h2v b)
    · exact absurd h'.symm (h12 a' b)
    · exact congrArg _ (hS₂.embeds.injective h')
    · exact absurd h' (h2h b)
    · exact absurd h' (h2g b x')
    · exact absurd h'.symm hv_h
    · exact absurd h'.symm (h1h a')
    · exact absurd h'.symm (h2h b')
    · rfl
    · exact absurd h'.symm (hgh x')
    · exact absurd h' (hgv x)
    · exact absurd h'.symm (h1g a' x)
    · exact absurd h'.symm (h2g b' x)
    · exact absurd h' (hgh x)
    · exact congrArg _ (hH.injective h')
  -- onto the descendants of `v`
  · rintro (_ | a | b | _ | x)
    · exact self_mem_desc v
    · exact hsub₁ (hf₁ a).1
    · exact hsub₂ (hf₂ b).1
    · exact hsub₁ hh₁
    · exact hsub₁ (hsubh (hsubc (hg x)))
  · intro x hx
    by_cases hxh : x ∈ G.desc h
    · rcases (mem_desc_iff_of_adj_iff_eq hhc).1 hxh with rfl | hxc
      · exact ⟨.hyb, rfl⟩
      · obtain ⟨y, rfl⟩ := hH.surj x hxc
        exact ⟨.below y, rfl⟩
    · rcases (mem_desc_iff_of_adj_iff hvc).1 hx with rfl | hx | hx
      · exact ⟨.top, rfl⟩
      · obtain ⟨a, rfl⟩ := hS₁.embeds.surj x ⟨hx, hxh⟩
        exact ⟨.side₁ a, rfl⟩
      · obtain ⟨b, rfl⟩ := hS₂.embeds.surj x ⟨hx, hxh⟩
        exact ⟨.side₂ b, rfl⟩
  -- the edges
  · rintro (_ | a | b | _ | x) (_ | a' | b' | _ | x')
    · exact iff_of_false (hG.not_adj_self v) id
    · show G.Adj v (f₁ a') ↔ S₁.first = some a'
      rw [hS₁.first_eq_some]
      refine ⟨fun h' => ((hvc _).1 h').resolve_right fun h'' => ?_, fun h' => h' ▸ hvc₁⟩
      exact Set.disjoint_left.1 hd₁ (hf₁ a') (by rw [h'']; exact self_mem_desc c₂)
    · show G.Adj v (f₂ b') ↔ S₂.first = some b'
      rw [hS₂.first_eq_some]
      refine ⟨fun h' => ((hvc _).1 h').resolve_left fun h'' => ?_, fun h' => h' ▸ hvc₂⟩
      exact Set.disjoint_left.1 hd₂ (hf₂ b') (by rw [h'']; exact self_mem_desc c₁)
    · show G.Adj v h ↔ S₁.first = none ∨ S₂.first = none
      rw [hS₁.first_eq_none, hS₂.first_eq_none, hvc, @eq_comm _ h c₁, @eq_comm _ h c₂]
    · refine iff_of_false (fun h' => ?_) id
      change G.Adj v (g x') at h'
      rcases (hvc _).1 h' with h'' | h''
      · exact hhc_ (desc_subset (hg x') (by rw [h'']; exact hh₁))
      · exact hhc_ (desc_subset (hg x') (by rw [h'']; exact hh₂))
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₁ (hf₁ a).1)) id
    · exact hS₁.embeds.adj_iff a a'
    · exact iff_of_false (fun h' => Set.disjoint_left.1 hd₂ (hf₂ b')
        (mem_desc_of_mem_of_adj (hf₁ a).1 h')) id
    · exact (hS₁.last_eq_some a).symm
    · refine iff_of_false (fun h' => ?_) id
      rcases he _ (hg x') _ h' with h'' | ⟨h'', -⟩
      · exact (hf₁ a).2 (hsubc h'')
      · exact h1h a h''
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₂ (hf₂ b).1)) id
    · exact iff_of_false (fun h' => Set.disjoint_left.1 hd₁ (hf₁ a')
        (mem_desc_of_mem_of_adj (hf₂ b).1 h')) id
    · exact hS₂.embeds.adj_iff b b'
    · exact (hS₂.last_eq_some b).symm
    · refine iff_of_false (fun h' => ?_) id
      rcases he _ (hg x') _ h' with h'' | ⟨h'', -⟩
      · exact (hf₂ b).2 (hsubc h'')
      · exact h2h b h''
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₁ hh₁)) id
    · refine iff_of_false (fun h' => ?_) id
      change G.Adj h (f₁ a') at h'
      exact (hf₁ a').2 (by rw [(hhc _).1 h']; exact mem_desc_of_adj hhc')
    · refine iff_of_false (fun h' => ?_) id
      change G.Adj h (f₂ b') at h'
      exact (hf₂ b').2 (by rw [(hhc _).1 h']; exact mem_desc_of_adj hhc')
    · exact iff_of_false (hG.not_adj_self h) id
    · show G.Adj h (g x') ↔ x' = r
      rw [hhc]
      exact ⟨fun h' => hH.injective (h'.trans hr.symm), fun h' => h' ▸ hr⟩
    · exact iff_of_false (hG.not_adj_of_mem_desc (hsub₁ (hsubh (hsubc (hg x))))) id
    · exact iff_of_false (fun h' => (hf₁ a').2 (hsubc (mem_desc_of_mem_of_adj (hg x) h'))) id
    · exact iff_of_false (fun h' => (hf₂ b').2 (hsubc (mem_desc_of_mem_of_adj (hg x) h'))) id
    · exact iff_of_false (fun h' => hhc_ (mem_desc_of_mem_of_adj (hg x) h')) id
    · exact hH.adj_iff x x'
  -- the labels
  · rintro (_ | a | b | _ | x)
    · exact hlv
    · exact hS₁.embeds.label_eq a
    · exact hS₂.embeds.label_eq b
    · exact hlh
    · exact hH.label_eq x
  -- the lengths
  · rintro (_ | a | b | _ | x) (_ | a' | b' | _ | x') hadj
    all_goals first
      | exact False.elim hadj
      | exact hS₁.embeds.len_eq _ _ hadj
      | exact hS₂.embeds.len_eq _ _ hadj
      | exact hH.len_eq _ _ hadj
      | skip
    · show G.len v (f₁ a') = S₁.topLen
      rw [(hS₁.first_eq_some a').1 hadj, hS₁.topLen_eq]
    · show G.len v (f₂ b') = S₂.topLen
      rw [(hS₂.first_eq_some b').1 hadj, hS₂.topLen_eq]
    · change S₁.first = none ∨ S₂.first = none at hadj
      dsimp only [MetricDigraph.cycle, CycleVert.elim]
      split
      · next heq =>
        exact (hS₁.hybLen_eq_of_none (hS₁.last_eq_none.2 (hS₁.first_eq_none.1 heq))).symm
      · next a heq =>
        have h₂ : S₂.first = none := hadj.resolve_left (by rw [heq]; exact Option.some_ne_none _)
        exact (hS₂.hybLen_eq_of_none (hS₂.last_eq_none.2 (hS₂.first_eq_none.1 h₂))).symm
    · exact (hS₁.hybLen_eq a hadj).symm
    · exact (hS₂.hybLen_eq b hadj).symm
    · show G.len h (g x') = G.len h c
      rw [show x' = r from hadj, hr]
  -- the inheritance probabilities
  · rintro (_ | a | b | _ | x) (_ | a' | b' | _ | x') hadj hhyb
    all_goals first
      | exact False.elim hadj
      | exact hS₁.embeds.inh_eq _ _ hadj hhyb
      | exact hS₂.embeds.inh_eq _ _ hadj hhyb
      | exact hH.inh_eq _ _ hadj hhyb
      | skip
    · change G.IsHybrid (f₁ a') at hhyb
      rw [(hS₁.first_eq_some a').1 hadj] at hhyb
      exact absurd hhyb (hc₁ (hfirst₁ a' hadj))
    · change G.IsHybrid (f₂ b') at hhyb
      rw [(hS₂.first_eq_some b').1 hadj] at hhyb
      exact absurd hhyb (hc₂ (hfirst₂ b' hadj))
    · change S₁.first = none ∨ S₂.first = none at hadj
      dsimp only [MetricDigraph.cycle, CycleVert.elim]
      split
      · next heq => exact hγ₁' (hS₁.last_eq_none.2 (hS₁.first_eq_none.1 heq))
      · next a heq =>
        have h₂ : S₂.first = none := hadj.resolve_left (by rw [heq]; exact Option.some_ne_none _)
        exact hγ₂' (hS₂.last_eq_none.2 (hS₂.first_eq_none.1 h₂))
    · exact hγ₁ a hadj
    · exact hγ₂ b hadj
    · change G.IsHybrid (g x') at hhyb
      rw [show x' = r from hadj, hr] at hhyb
      exact absurd hhyb hc

end IsBinary

/-! ### From an embedding onto all the vertices to an isomorphism -/

/-- An embedding of `H` onto all the vertices of `G` is inverse to an isomorphism from `G` to
`H`. -/
theorem Embeds.nonempty_iso {W : Type w} {H : MetricDigraph W X} {f : W → V}
    (hf : G.Embeds H f Set.univ) : Nonempty (G.Iso H) := by
  let e : W ≃ V := Equiv.ofBijective f ⟨hf.injective, fun x => hf.surj x trivial⟩
  refine ⟨{ toEquiv := e.symm, adj_iff := ?_, label_eq := ?_, len_eq := ?_, inh_eq := ?_ }⟩
  · intro x y
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    exact (hf.adj_iff a b).symm
  · intro x
    obtain ⟨a, rfl⟩ := e.surjective x
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    exact (hf.label_eq a).symm
  · intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    exact (hf.len_eq a b ((hf.adj_iff a b).1 hxy)).symm
  · intro x y hxy hy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    simp only [Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    exact (hf.inh_eq a b ((hf.adj_iff a b).1 hxy) hy).symm

end MetricDigraph

end Phylogenetics
