module

public import Phylogenetics.Graph.Degree
public import Phylogenetics.Network.Cuts

/-!
# The network induced on a set of taxa

The induced subnetwork on a taxon set `Y`, with `|Y| ≥ 2` (Rhodes, Allman, Ané, Baños 2026, Section 2):
keep the arcs and vertices
ancestral to `Y` below the least stable ancestor of `Y`, then suppress the vertices of indegree one
and outdegree one. This module constructs it and proves that the predicate `HasCutSplitOn`, stated on
the induced subgraph (which keeps everything above the LSA and the degree-two vertices), is the
cut-edge split of the induced network.

Main results:

* `exists_isLeastStableAncestor`, `IsLeastStableAncestor.unique`: the LSA of a nonempty taxon set;
* `lsaNetwork`, `lsaNetwork_isPhylogenetic`: the part of the induced subgraph below the LSA;
* `suppress`, `suppress_isPhylogenetic`, `suppress_hasCutSplit_iff`, `suppress_not_isChainVertex`,
  `suppress_degree_two_eq_root`: suppression of the vertices of indegree and outdegree one, which
  keeps the network laws and the cut-edge splits and leaves degree two only at the root;
* `inducedNetwork`, `inducedNetwork_isPhylogenetic`,
  `hasCutSplitOn_iff_inducedNetwork_hasCutSplit`: the induced network and the theorem above.

## References

* J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*, bioRxiv 10.64898/2026.05.28.728501.
-/

@[expose] public noncomputable section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### The least stable ancestor -/

/-- A vertex that a path cannot avoid lies on it. -/
theorem reaches_of_not_hasPathAvoiding {u t w : V} (h : N.graph.Reaches u t)
    (hn : ¬ N.HasPathAvoiding u t w) : N.graph.Reaches u w ∧ N.graph.Reaches w t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have : t = w := by
      by_contra hne
      exact hn ⟨hne, hne, .refl⟩
    subst this
    exact ⟨.refl, .refl⟩
  | @head a b hab hbt ih =>
    by_cases ha : a = w
    · subst ha
      exact ⟨.refl, hbt.head hab⟩
    · by_cases hb : N.HasPathAvoiding b t w
      · obtain ⟨hbw, htw, hp⟩ := hb
        exact absurd ⟨ha, htw, hp.head ⟨hab, ha, hbw⟩⟩ hn
      · obtain ⟨h₁, h₂⟩ := ih hb
        exact ⟨h₁.head hab, h₂⟩

/-- Extending a path avoiding a vertex by an arc from a different vertex. -/
theorem hasPathAvoiding_head {a b t w : V} (hab : N.graph.Adj a b) (ha : a ≠ w)
    (hb : N.HasPathAvoiding b t w) : N.HasPathAvoiding a t w :=
  ⟨ha, hb.2.1, hb.2.2.head ⟨hab, ha, hb.1⟩⟩

/-- Two vertices that a path cannot avoid are comparable. -/
theorem reaches_or_reaches_of_not_hasPathAvoiding {u t v w : V} (h : N.graph.Reaches u t)
    (hv : ¬ N.HasPathAvoiding u t v) (hw : ¬ N.HasPathAvoiding u t w) :
    N.graph.Reaches v w ∨ N.graph.Reaches w v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨-, h₁⟩ := reaches_of_not_hasPathAvoiding .refl hv
    obtain ⟨h₂, -⟩ := reaches_of_not_hasPathAvoiding .refl hw
    exact Or.inl (h₁.trans h₂)
  | @head a b hab hbt ih =>
    by_cases hav : a = v
    · subst hav
      exact Or.inl (reaches_of_not_hasPathAvoiding (hbt.head hab) hw).1
    · by_cases haw : a = w
      · subst haw
        exact Or.inr (reaches_of_not_hasPathAvoiding (hbt.head hab) hv).1
      · exact ih (fun h => hv (hasPathAvoiding_head hab hav h))
          (fun h => hw (hasPathAvoiding_head hab haw h))

/-- A stable ancestor of `Y` lies above every taxon of `Y`. -/
theorem IsStableAncestor.reaches_leaf (hN : N.IsPhylogenetic) {Y : Set X} {v : V}
    (h : N.IsStableAncestor Y v) {x : X} (hx : x ∈ Y) : N.graph.Reaches v (N.leaf x) :=
  (reaches_of_not_hasPathAvoiding (hN.root_reaches _) (h x hx)).2

/-- In an acyclic graph, mutual reachability is equality. -/
theorem eq_of_reaches_of_reaches (hA : N.graph.IsAcyclic) {u v : V}
    (h : N.graph.Reaches u v) (h' : N.graph.Reaches v u) : u = v := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | ht
  · rfl
  · exact absurd (ht.trans_left h') (hA u)

/-- **Existence of the least stable ancestor** of a nonempty set of taxa. -/
theorem exists_isLeastStableAncestor (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nonempty) :
    ∃ v, N.IsLeastStableAncestor Y v := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  obtain ⟨v, hv, hmin⟩ := hwf.has_min {v | N.IsStableAncestor Y v}
    ⟨N.root, N.root_isStableAncestor Y⟩
  refine ⟨v, hv, fun w hw => ?_⟩
  obtain ⟨x, hx⟩ := hY
  rcases reaches_or_reaches_of_not_hasPathAvoiding (hN.root_reaches (N.leaf x)) (hw x hx) (hv x hx)
    with h | h
  · exact h
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | ht
    · exact .refl
    · exact absurd ht (hmin w hw)

/-- **Uniqueness of the least stable ancestor.** -/
theorem IsLeastStableAncestor.unique (hN : N.IsPhylogenetic) {Y : Set X} {v w : V}
    (hv : N.IsLeastStableAncestor Y v) (hw : N.IsLeastStableAncestor Y w) : v = w :=
  eq_of_reaches_of_reaches hN.acyclic (hw.2 v hv.1) (hv.2 w hw.1)

/-- The least stable ancestor of a nonempty set of taxa. -/
def lsa (hN : N.IsPhylogenetic) (Y : Set X) (hY : Y.Nonempty) : V :=
  Classical.choose (exists_isLeastStableAncestor hN hY)

theorem lsa_spec (hN : N.IsPhylogenetic) (Y : Set X) (hY : Y.Nonempty) :
    N.IsLeastStableAncestor Y (lsa hN Y hY) :=
  Classical.choose_spec (exists_isLeastStableAncestor hN hY)

/-- A stable ancestor of two distinct taxa is not a taxon. -/
theorem IsStableAncestor.leaf_ne (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial) {v : V}
    (h : N.IsStableAncestor Y v) (x : X) : N.leaf x ≠ v := by
  have : Finite E := hN.finite_arcs
  rintro rfl
  obtain ⟨y, hy, hxy⟩ := hY.exists_ne x
  have hr := h.reaches_leaf hN hy
  have hz := N.graph.eq_of_reaches_of_outdegree_eq_zero hr ((hN.leaves _).mpr ⟨x, rfl⟩)
  exact hxy (hN.leaf_injective hz)

/-- A path avoiding `e` that cannot avoid the vertex `w` continues from `w` avoiding `e`. -/
theorem AvoidingReach.suffix_of_not_hasPathAvoiding {e : E} {u t w : V}
    (h : N.AvoidingReach e u t) (hw : ¬ N.HasPathAvoiding u t w) : N.AvoidingReach e w t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨-, h₁⟩ := reaches_of_not_hasPathAvoiding (N := N) .refl hw
    have : t = w := by
      by_contra hne
      exact hw ⟨hne, hne, .refl⟩
    subst this
    exact .refl
  | @head a b hab hbt ih =>
    by_cases ha : a = w
    · subst ha
      exact hbt.head hab
    · obtain ⟨f, _, hs, ht⟩ := hab
      exact ih fun h => hw (hasPathAvoiding_head ⟨f, hs, ht⟩ ha h)

/-- An arc dominating a taxon and a vertex that paths to the taxon cannot avoid are comparable. -/
theorem reaches_source_or_target_reaches_of_not_hasPathAvoiding {e : E} {u t w : V}
    (h : N.graph.Reaches u t) (he : ¬ N.AvoidingReach e u t) (hw : ¬ N.HasPathAvoiding u t w) :
    N.graph.Reaches w (N.graph.source e) ∨ N.graph.Reaches (N.graph.target e) w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd .refl he
  | @head a b hab hbt ih =>
    by_cases ha : a = w
    · subst ha
      exact Or.inl (reaches_source_of_not_avoidingReach (hbt.head hab) he)
    · have hb : ¬ N.HasPathAvoiding b t w := fun h => hw (hasPathAvoiding_head hab ha h)
      obtain ⟨f, hs, ht⟩ := hab
      by_cases hfe : f = e
      · subst hfe
        rw [ht]
        exact Or.inr (reaches_of_not_hasPathAvoiding hbt hb).1
      · exact ih (fun h => he (h.head ⟨f, hfe, hs, ht⟩)) hb

/-! ### The induced subgraph below a vertex -/

/-- The vertices of the induced subgraph on `Y` below `l`. -/
def belowVertices (N : RootedNetwork V E X) (l : V) (Y : Set X) : Set V :=
  {v | N.graph.Reaches l v ∧ v ∈ N.ancestralVertices Y}

/-- The arcs of the induced subgraph on `Y` below `l`. -/
def belowArcs (N : RootedNetwork V E X) (l : V) (Y : Set X) : Set E :=
  {e | N.graph.Reaches l (N.graph.source e) ∧ e ∈ N.ancestralArcs Y}

/-- The induced subgraph on `Y` below the vertex `l`, rooted at `l`, for a stable ancestor `l`. -/
def belowNetwork (N : RootedNetwork V E X) (l : V) (Y : Set X)
    (hl : l ∈ N.ancestralVertices Y) (hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)) :
    RootedNetwork (N.belowVertices l Y) (N.belowArcs l Y) Y where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, e.2.1, N.source_mem_ancestralVertices e.2.2⟩
      target := fun e => ⟨N.graph.target e.1, e.2.1.tail ⟨e.1, rfl, rfl⟩, e.2.2⟩ }
  root := ⟨l, .refl, hl⟩
  leaf x := ⟨N.leaf x.1, hleaf x.1 x.2, N.leaf_mem_ancestralVertices x.2⟩

section Below

variable {l : V} {Y : Set X} {hl : l ∈ N.ancestralVertices Y}
  {hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)}

theorem belowNetwork_adj_iff {u v : N.belowVertices l Y} :
    (N.belowNetwork l Y hl hleaf).graph.Adj u v ↔ N.graph.Adj u.1 v.1 := by
  constructor
  · rintro ⟨e, hs, ht⟩
    exact ⟨e.1, congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · rintro ⟨e, hs, ht⟩
    have he : e ∈ N.belowArcs l Y := ⟨hs ▸ u.2.1, by
      change N.graph.target e ∈ N.ancestralVertices Y
      rw [ht]
      exact v.2.2⟩
    exact ⟨⟨e, he⟩, Subtype.ext hs, Subtype.ext ht⟩

/-- Reachability in the induced subgraph below `l` is reachability in the network. -/
theorem belowNetwork_reaches_iff {u v : N.belowVertices l Y} :
    (N.belowNetwork l Y hl hleaf).graph.Reaches u v ↔ N.graph.Reaches u.1 v.1 := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift Subtype.val
      (fun a b h => (belowNetwork_adj_iff (hl := hl) (hleaf := hleaf)).mp h) u v h
  · obtain ⟨v, hv⟩ := v
    intro h
    change N.graph.Reaches u.1 v at h
    induction h with
    | refl => exact .refl
    | @tail a b hua hab ih =>
      have ha : a ∈ N.belowVertices l Y :=
        ⟨u.2.1.trans hua, N.mem_ancestralVertices_of_reaches (.single hab) hv.2⟩
      exact (ih ha).tail (belowNetwork_adj_iff.mpr hab)

/-- Paths avoiding an arc in the induced subgraph below `l` are those in the network. -/
theorem belowNetwork_avoidingReach_iff {e : N.belowArcs l Y} {u v : N.belowVertices l Y} :
    (N.belowNetwork l Y hl hleaf).AvoidingReach e u v ↔ N.AvoidingReach e.1 u.1 v.1 := by
  constructor
  · intro h
    refine Relation.ReflTransGen.lift Subtype.val ?_ u v h
    rintro a b ⟨f, hfe, hs, ht⟩
    exact ⟨f.1, fun h => hfe (Subtype.ext h), congrArg Subtype.val hs, congrArg Subtype.val ht⟩
  · obtain ⟨v, hv⟩ := v
    intro h
    change N.AvoidingReach e.1 u.1 v at h
    induction h with
    | refl => exact .refl
    | @tail a b hua hab ih =>
      obtain ⟨f, hfe, hs, ht⟩ := hab
      have ha : a ∈ N.belowVertices l Y :=
        ⟨u.2.1.trans (AvoidingReach.reaches hua),
          N.mem_ancestralVertices_of_reaches (.single ⟨f, hs, ht⟩) hv.2⟩
      have hf : f ∈ N.belowArcs l Y := ⟨hs ▸ ha.1, by
        change N.graph.target f ∈ N.ancestralVertices Y
        rw [ht]
        exact hv.2⟩
      exact (ih ha).tail ⟨⟨f, hf⟩, fun h => hfe (congrArg Subtype.val h),
        Subtype.ext hs, Subtype.ext ht⟩

theorem belowNetwork_isBelow_iff {e : N.belowArcs l Y} {x : Y} :
    (N.belowNetwork l Y hl hleaf).IsBelow e x ↔ N.IsBelow e.1 x.1 :=
  belowNetwork_reaches_iff

/-- Domination below a stable ancestor is domination in the network. -/
theorem belowNetwork_dominates_iff (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    {e : N.belowArcs l Y} {x : Y} :
    (N.belowNetwork l Y hl hleaf).Dominates e x ↔ N.Dominates e.1 x.1 := by
  refine not_congr (belowNetwork_avoidingReach_iff.trans ?_)
  constructor
  · intro h
    exact (avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches l) e.2.1).trans h
  · intro h
    exact h.suffix_of_not_hasPathAvoiding (hst x.1 x.2)

/-- The induced subgraph below a stable ancestor of at least two taxa is a phylogenetic network. -/
theorem belowNetwork_isPhylogenetic (hN : N.IsPhylogenetic) (hY : Y.Nontrivial)
    (hst : N.IsStableAncestor Y l) : (N.belowNetwork l Y hl hleaf).IsPhylogenetic := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have : Finite X := hN.finite_taxa
  have hroot : ∀ v, (N.belowNetwork l Y hl hleaf).graph.Reaches
      (N.belowNetwork l Y hl hleaf).root v := fun v => belowNetwork_reaches_iff.mpr v.2.1
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, hroot, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    refine hN.acyclic v.1 (Relation.TransGen.lift Subtype.val ?_ v v h)
    exact fun a b h => (belowNetwork_adj_iff (hl := hl) (hleaf := hleaf)).mp h
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    intro e he
    have heq : N.graph.target e.1 = l := congrArg Subtype.val he
    exact not_reaches_target_source hN.acyclic e.1 (by rw [heq]; exact e.2.1)
  · intro v hv
    rw [DirectedMultigraph.one_le_indegree_iff]
    rcases Relation.ReflTransGen.cases_tail (hroot v) with h | ⟨a, -, e, -, he⟩
    · exact absurd h hv
    · exact ⟨e, he⟩
  · intro x y h
    exact Subtype.ext (hN.leaf_injective (congrArg Subtype.val h))
  · intro x
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp (hN.leaf_indegree x.1)
    have hne : l ≠ N.leaf x.1 := (hst.leaf_ne hN hY x.1).symm
    rcases Relation.ReflTransGen.cases_tail (hleaf x.1 x.2) with h | ⟨a, ha, f, hs, ht⟩
    · exact absurd h.symm hne
    · have hfg : f = g := (hg f).mp ht
      subst hfg
      have hf : f ∈ N.belowArcs l Y := ⟨hs ▸ ha, by
        change N.graph.target f ∈ N.ancestralVertices Y
        rw [ht]
        exact N.leaf_mem_ancestralVertices x.2⟩
      refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨⟨f, hf⟩, fun e => ?_⟩
      constructor
      · intro he
        exact Subtype.ext ((hg e.1).mp (congrArg Subtype.val he))
      · rintro rfl
        exact Subtype.ext ht
  · intro v
    rw [DirectedMultigraph.outdegree_eq_zero_iff]
    constructor
    · intro hv
      obtain ⟨x, hx, hpath⟩ := v.2.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      rcases Relation.ReflTransGen.cases_head hpath with h | ⟨a, ⟨f, hs, ht⟩, hat⟩
      · exact h.symm
      · have hf : f ∈ N.belowArcs l Y := ⟨hs ▸ v.2.1, by
          change N.graph.target f ∈ N.ancestralVertices Y
          rw [ht]
          exact N.mem_ancestralVertices_of_reaches hat (N.leaf_mem_ancestralVertices hx)⟩
        exact absurd (Subtype.ext hs) (hv ⟨f, hf⟩)
    · rintro ⟨x, rfl⟩ e he
      have hz := (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves (N.leaf x.1)).mpr ⟨x.1, rfl⟩)
      exact hz e.1 (congrArg Subtype.val he)

end Below

/-- The stable ancestor `lsa` lies in the induced subgraph. -/
theorem lsa_mem_ancestralVertices (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nonempty) :
    lsa hN Y hY ∈ N.ancestralVertices Y := by
  obtain ⟨x, hx⟩ := hY
  exact ⟨x, hx, (lsa_spec hN Y ⟨x, hx⟩).1.reaches_leaf hN hx⟩

/-- The induced subgraph on `Y` restricted to the vertices and arcs below the LSA of `Y`, rooted at
the LSA, retaining the degree-two vertices. -/
def lsaNetwork (hN : N.IsPhylogenetic) (Y : Set X) (hY : Y.Nonempty) :
    RootedNetwork (N.belowVertices (lsa hN Y hY) Y) (N.belowArcs (lsa hN Y hY) Y) Y :=
  N.belowNetwork (lsa hN Y hY) Y (lsa_mem_ancestralVertices hN hY)
    fun _ hx => (lsa_spec hN Y hY).1.reaches_leaf hN hx

/-- For at least two taxa, the part of the induced subgraph below the LSA satisfies the network
laws. -/
theorem lsaNetwork_isPhylogenetic (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial) :
    (lsaNetwork hN Y hY.nonempty).IsPhylogenetic :=
  belowNetwork_isPhylogenetic hN hY (lsa_spec hN Y hY.nonempty).1

/-- **Removing what lies above the LSA does not change a split with both sides nonempty.** -/
theorem hasCutSplitOn_iff_lsaNetwork_hasCutSplit (hN : N.IsPhylogenetic) {Y A : Set X}
    (hY : Y.Nontrivial) (h₁ : (Y ∩ A).Nonempty) (h₂ : (Y \ A).Nonempty) :
    N.HasCutSplitOn Y A ↔ (lsaNetwork hN Y hY.nonempty).HasCutSplit (Subtype.val ⁻¹' A) := by
  have hst := (lsa_spec hN Y hY.nonempty).1
  have hNet := lsaNetwork_isPhylogenetic hN hY
  -- the arcs of a split with nonempty sides are below the LSA
  have hbelow : ∀ (e : E) (P Q : Set X), P ⊆ Y → Q ⊆ Y → P.Nonempty → Q.Nonempty →
      N.Separates e P Q → e ∈ N.belowArcs (lsa hN Y hY.nonempty) Y := by
    rintro e P Q hP hQ ⟨x, hx⟩ ⟨y, hy⟩ ⟨hd, hn⟩
    refine ⟨?_, ⟨x, hP hx, (hd x hx).isBelow hN⟩⟩
    rcases reaches_source_or_target_reaches_of_not_hasPathAvoiding (hN.root_reaches _) (hd x hx)
      (hst x (hP hx)) with h | h
    · exact h
    · exact absurd (h.trans (hst.reaches_leaf hN (hQ hy))) (hn y hy)
  rw [hasCutSplit_iff_hasCutSplitOn_univ hNet, hasCutSplitOn_iff_separates hNet,
    hasCutSplitOn_iff_separates hN]
  have htransfer : ∀ (e : N.belowArcs (lsa hN Y hY.nonempty) Y) (P Q : Set X),
      (lsaNetwork hN Y hY.nonempty).Separates e (Subtype.val ⁻¹' P) (Subtype.val ⁻¹' Q) ↔
        N.Separates e.1 (Y ∩ P) (Y ∩ Q) := by
    intro e P Q
    constructor
    · rintro ⟨hd, hn⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact (belowNetwork_dominates_iff hN hst (x := ⟨x, hx.1⟩)).mp (hd ⟨x, hx.1⟩ hx.2)
      · exact fun hb => hn ⟨x, hx.1⟩ hx.2 (belowNetwork_isBelow_iff (x := ⟨x, hx.1⟩) |>.mpr hb)
    · rintro ⟨hd, hn⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · exact (belowNetwork_dominates_iff hN hst).mpr (hd x.1 ⟨x.2, hx⟩)
      · exact fun hb => hn x.1 ⟨x.2, hx⟩ (belowNetwork_isBelow_iff.mp hb)
  have hU₁ : (Set.univ ∩ Subtype.val ⁻¹' A : Set Y) = Subtype.val ⁻¹' A := Set.univ_inter _
  have hU₂ : (Set.univ \ Subtype.val ⁻¹' A : Set Y) = Subtype.val ⁻¹' Aᶜ := by
    ext x
    simp
  have hY₂ : Y \ A = Y ∩ Aᶜ := rfl
  have hne₁ : (Set.univ ∩ Subtype.val ⁻¹' A : Set Y).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := h₁
    exact ⟨⟨x, hx⟩, Set.mem_univ _, hxA⟩
  have hne₂ : (Set.univ \ Subtype.val ⁻¹' A : Set Y).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := h₂
    exact ⟨⟨x, hx⟩, Set.mem_univ _, hxA⟩
  rw [hU₁] at hne₁ ⊢
  rw [hU₂] at hne₂ ⊢
  rw [hY₂] at h₂ ⊢
  constructor
  · rintro ⟨e, ⟨-, hs⟩ | ⟨-, hs⟩⟩
    · have he := hbelow e _ _ Set.inter_subset_left Set.inter_subset_left h₁ h₂ hs
      exact ⟨⟨e, he⟩, Or.inl ⟨hne₁, (htransfer ⟨e, he⟩ A Aᶜ).mpr hs⟩⟩
    · have he := hbelow e _ _ Set.inter_subset_left Set.inter_subset_left h₂ h₁ hs
      exact ⟨⟨e, he⟩, Or.inr ⟨hne₂, (htransfer ⟨e, he⟩ Aᶜ A).mpr hs⟩⟩
  · rintro ⟨e, ⟨-, hs⟩ | ⟨-, hs⟩⟩
    · exact ⟨e.1, Or.inl ⟨h₁, (htransfer e A Aᶜ).mp hs⟩⟩
    · exact ⟨e.1, Or.inr ⟨h₂, (htransfer e Aᶜ A).mp hs⟩⟩

/-! ### Suppression of the vertices of indegree one and outdegree one -/

/-- A vertex of indegree one and outdegree one: the degree-two vertices of a rooted network other
than a root of outdegree two. -/
def IsChainVertex (N : RootedNetwork V E X) (v : V) : Prop :=
  N.graph.indegree v = 1 ∧ N.graph.outdegree v = 1

/-- `v` is reachable from `u` by arcs leaving chain vertices. -/
def ChainReach (N : RootedNetwork V E X) : V → V → Prop :=
  Relation.ReflTransGen fun a b => N.IsChainVertex a ∧ N.graph.Adj a b

theorem ChainReach.reaches {u v : V} (h : N.ChainReach u v) : N.graph.Reaches u v := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  exact fun _ _ h => h.2

theorem not_isChainVertex_root (hN : N.IsPhylogenetic) : ¬ N.IsChainVertex N.root := fun h => by
  have := h.1
  rw [hN.root_indegree] at this
  exact Nat.zero_ne_one this

theorem not_isChainVertex_leaf (hN : N.IsPhylogenetic) (x : X) : ¬ N.IsChainVertex (N.leaf x) :=
  fun h => by
    have := h.2
    rw [(hN.leaves _).mpr ⟨x, rfl⟩] at this
    exact Nat.zero_ne_one this

/-- Every vertex has a chain ending at a vertex that is not a chain vertex. -/
theorem exists_chainEnd (hN : N.IsPhylogenetic) (v : V) :
    ∃ w, N.ChainReach v w ∧ ¬ N.IsChainVertex w := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  induction v using hwf.induction with
  | _ v ih =>
    by_cases hv : N.IsChainVertex v
    · obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff v).mp hv.2
      have hadj : N.graph.Adj v (N.graph.target e) := ⟨e, (he e).mpr rfl, rfl⟩
      obtain ⟨w, hw, hnw⟩ := ih _ (.single hadj)
      exact ⟨w, Relation.ReflTransGen.head ⟨hv, hadj⟩ hw, hnw⟩
    · exact ⟨v, .refl, hv⟩

/-- A chain vertex has only one successor. -/
theorem IsChainVertex.adj_unique {v a b : V} (hv : N.IsChainVertex v) (ha : N.graph.Adj v a)
    (hb : N.graph.Adj v b) : a = b := by
  obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff v).mp hv.2
  obtain ⟨f, hfs, rfl⟩ := ha
  obtain ⟨g, hgs, rfl⟩ := hb
  rw [(he f).mp hfs, (he g).mp hgs]

/-- A chain has only one end. -/
theorem ChainReach.end_unique {v w w' : V} (h : N.ChainReach v w) (h' : N.ChainReach v w')
    (hw : ¬ N.IsChainVertex w) (hw' : ¬ N.IsChainVertex w') : w = w' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rcases Relation.ReflTransGen.cases_head h' with h | ⟨a, ha, -⟩
    · exact h
    · exact absurd ha.1 hw
  | @head a b hab _ ih =>
    rcases Relation.ReflTransGen.cases_head h' with h | ⟨c, hc, hcw⟩
    · exact absurd (h ▸ hab.1) hw'
    · have hbc : b = c := hab.1.adj_unique hab.2 hc.2
      subst hbc
      exact ih hcw

/-- The end of the chain from a vertex: the first vertex along it that is not a chain vertex. -/
def chainEnd (hN : N.IsPhylogenetic) (v : V) : V := Classical.choose (exists_chainEnd hN v)

theorem chainReach_chainEnd (hN : N.IsPhylogenetic) (v : V) : N.ChainReach v (chainEnd hN v) :=
  (Classical.choose_spec (exists_chainEnd hN v)).1

theorem not_isChainVertex_chainEnd (hN : N.IsPhylogenetic) (v : V) :
    ¬ N.IsChainVertex (chainEnd hN v) :=
  (Classical.choose_spec (exists_chainEnd hN v)).2

theorem chainEnd_eq_of_chainReach (hN : N.IsPhylogenetic) {v w : V} (h : N.ChainReach v w)
    (hw : ¬ N.IsChainVertex w) : chainEnd hN v = w :=
  (chainReach_chainEnd hN v).end_unique h (not_isChainVertex_chainEnd hN v) hw

theorem chainEnd_eq_self (hN : N.IsPhylogenetic) {v : V} (hv : ¬ N.IsChainVertex v) :
    chainEnd hN v = v :=
  chainEnd_eq_of_chainReach hN .refl hv

theorem chainEnd_eq_of_adj (hN : N.IsPhylogenetic) {v a : V} (hv : N.IsChainVertex v)
    (h : N.graph.Adj v a) : chainEnd hN v = chainEnd hN a :=
  chainEnd_eq_of_chainReach hN
    (Relation.ReflTransGen.head ⟨hv, h⟩ (chainReach_chainEnd hN a))
    (not_isChainVertex_chainEnd hN a)

theorem chainEnd_eq_of_chainReach_left (hN : N.IsPhylogenetic) {v w : V} (h : N.ChainReach v w) :
    chainEnd hN v = chainEnd hN w :=
  chainEnd_eq_of_chainReach hN (h.trans (chainReach_chainEnd hN w))
    (not_isChainVertex_chainEnd hN w)

/-- **Suppression** of the vertices of indegree one and outdegree one. The vertices are the others;
the arcs are those leaving the others, with the first such vertex along the chain as target. Arcs
keep their identity, and parallel arcs may appear. -/
def suppress (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) :
    RootedNetwork {v // ¬ N.IsChainVertex v} {e // ¬ N.IsChainVertex (N.graph.source e)} X where
  graph :=
    { source := fun e => ⟨N.graph.source e.1, e.2⟩
      target := fun e => ⟨chainEnd hN (N.graph.target e.1), not_isChainVertex_chainEnd hN _⟩ }
  root := ⟨N.root, not_isChainVertex_root hN⟩
  leaf x := ⟨N.leaf x, not_isChainVertex_leaf hN x⟩

/-- A path of the network gives a path of the suppressed network, to the end of the chain. -/
theorem suppress_reaches_chainEnd (hN : N.IsPhylogenetic) (u : {v // ¬ N.IsChainVertex v}) {w : V}
    (h : N.graph.Reaches u.1 w) :
    (N.suppress hN).graph.Reaches u ⟨chainEnd hN w, not_isChainVertex_chainEnd hN w⟩ := by
  induction h with
  | refl =>
    have : (⟨chainEnd hN u.1, not_isChainVertex_chainEnd hN u.1⟩ :
        {v // ¬ N.IsChainVertex v}) = u :=
      Subtype.ext (chainEnd_eq_self hN u.2)
    rw [this]
    exact .refl
  | @tail a b _ hab ih =>
    by_cases ha : N.IsChainVertex a
    · have heq := chainEnd_eq_of_adj hN ha hab
      simpa only [heq] using ih
    · refine ih.tail ?_
      obtain ⟨f, hs, ht⟩ := hab
      subst hs ht
      exact ⟨⟨f, ha⟩, Subtype.ext (chainEnd_eq_self hN ha).symm, rfl⟩

theorem suppress_reaches_of_reaches (hN : N.IsPhylogenetic) (u v : {v // ¬ N.IsChainVertex v})
    (h : N.graph.Reaches u.1 v.1) : (N.suppress hN).graph.Reaches u v := by
  have := suppress_reaches_chainEnd hN u h
  have heq : (⟨chainEnd hN v.1, not_isChainVertex_chainEnd hN v.1⟩ :
      {v // ¬ N.IsChainVertex v}) = v :=
    Subtype.ext (chainEnd_eq_self hN v.2)
  rwa [heq] at this

/-- Two arcs from outside chains, whose chains end at a vertex of indegree one, are the same arc. -/
theorem arc_eq_of_chainReach {e e' : E} {w : V} (he : ¬ N.IsChainVertex (N.graph.source e))
    (he' : ¬ N.IsChainVertex (N.graph.source e')) (h : N.ChainReach (N.graph.target e) w)
    (h' : N.ChainReach (N.graph.target e') w) (hw : N.graph.indegree w = 1) : e = e' := by
  induction h with
  | refl =>
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp hw
    rcases Relation.ReflTransGen.cases_tail h' with h | ⟨b, -, hb, f, hfs, hft⟩
    · rw [(hg e).mp rfl, (hg e').mp h.symm]
    · have hfe : f = e := by rw [(hg f).mp hft, (hg e).mp rfl]
      subst hfe
      exact absurd (hfs ▸ hb) he
  | @tail a b hprev hstep ih =>
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp hw
    obtain ⟨hb, f, hfs, hft⟩ := hstep
    rcases Relation.ReflTransGen.cases_tail h' with h | ⟨c, hc, hcc, f', hfs', hft'⟩
    · have hfe : f = e' := by rw [(hg f).mp hft, (hg e').mp h.symm]
      subst hfe
      exact absurd (hfs ▸ hb) he'
    · have hff : f = f' := by rw [(hg f).mp hft, (hg f').mp hft']
      subst hff
      have hac : a = c := hfs.symm.trans hfs'
      subst hac
      exact ih hc hb.1

/-- **Suppression preserves the network laws.** -/
theorem suppress_isPhylogenetic (hN : N.IsPhylogenetic) : (N.suppress hN).IsPhylogenetic := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hroot : ∀ v, (N.suppress hN).graph.Reaches (N.suppress hN).root v := fun v =>
    suppress_reaches_of_reaches hN _ v (hN.root_reaches v.1)
  have hin : ∀ v, v ≠ (N.suppress hN).root → ∃ e, (N.suppress hN).graph.target e = v := by
    intro v hv
    rcases Relation.ReflTransGen.cases_tail (hroot v) with h | ⟨a, -, e, -, he⟩
    · exact absurd h hv
    · exact ⟨e, he⟩
  refine ⟨inferInstance, inferInstance, hN.finite_taxa, ?_, hroot, ?_, ?_, ?_, ?_, ?_⟩
  · intro v h
    refine hN.acyclic v.1 (Relation.TransGen.lift' Subtype.val ?_ _ _ h)
    rintro a b ⟨e, hs, ht⟩
    subst hs ht
    exact Relation.TransGen.head' ⟨e.1, rfl, rfl⟩ (chainReach_chainEnd hN _).reaches
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    intro e he
    have heq : chainEnd hN (N.graph.target e.1) = N.root := congrArg Subtype.val he
    have hr := (chainReach_chainEnd hN (N.graph.target e.1)).reaches
    rw [heq] at hr
    exact hN.acyclic N.root (Relation.TransGen.trans_right (hN.root_reaches _)
      (Relation.TransGen.head' ⟨e.1, rfl, rfl⟩ hr))
  · intro v hv
    exact (DirectedMultigraph.one_le_indegree_iff _ _).mpr (hin v hv)
  · intro x y h
    exact hN.leaf_injective (congrArg Subtype.val h)
  · intro x
    have hne : (N.suppress hN).leaf x ≠ (N.suppress hN).root := fun h =>
      N.leaf_ne_root hN x (congrArg Subtype.val h)
    obtain ⟨e, he⟩ := hin _ hne
    have hc : ∀ f : {e // ¬ N.IsChainVertex (N.graph.source e)},
        (N.suppress hN).graph.target f = (N.suppress hN).leaf x →
          N.ChainReach (N.graph.target f.1) (N.leaf x) := by
      intro f hf
      have heq : chainEnd hN (N.graph.target f.1) = N.leaf x := congrArg Subtype.val hf
      exact heq ▸ chainReach_chainEnd hN _
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨e, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · exact Subtype.ext (arc_eq_of_chainReach f.2 e.2 (hc f hf) (hc e he) (hN.leaf_indegree x))
    · rintro rfl
      exact he
  · intro v
    rw [DirectedMultigraph.outdegree_eq_zero_iff]
    constructor
    · intro hv
      have hz : N.graph.outdegree v.1 = 0 := by
        refine (N.graph.outdegree_eq_zero_iff _).mpr fun e he => ?_
        exact hv ⟨e, he ▸ v.2⟩ (Subtype.ext he)
      obtain ⟨x, hx⟩ := (hN.leaves _).mp hz
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩ e he
      have hz := (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩)
      exact hz e.1 (congrArg Subtype.val he)

/-- The arc `e` lies on the chain starting with the arc `f`. -/
def IsOnChain (N : RootedNetwork V E X) (f e : E) : Prop :=
  e = f ∨ (N.IsChainVertex (N.graph.source e) ∧ N.ChainReach (N.graph.target f) (N.graph.source e))

/-- Every chain vertex lies on a chain starting at a non-chain vertex. -/
theorem exists_arc_chainReach (hN : N.IsPhylogenetic) {v : V} (hv : N.IsChainVertex v) :
    ∃ f, ¬ N.IsChainVertex (N.graph.source f) ∧ N.ChainReach (N.graph.target f) v := by
  have hr := hN.root_reaches v
  induction hr with
  | refl => exact absurd hv (not_isChainVertex_root hN)
  | @tail a b _ hab ih =>
    obtain ⟨g, hs, ht⟩ := hab
    by_cases ha : N.IsChainVertex a
    · obtain ⟨f, hf, hc⟩ := ih ha
      exact ⟨f, hf, hc.tail ⟨ha, g, hs, ht⟩⟩
    · exact ⟨g, hs ▸ ha, ht ▸ .refl⟩

/-- Every arc lies on a chain starting at a non-chain vertex. -/
theorem exists_isOnChain (hN : N.IsPhylogenetic) (e : E) :
    ∃ f, ¬ N.IsChainVertex (N.graph.source f) ∧ N.IsOnChain f e := by
  by_cases he : N.IsChainVertex (N.graph.source e)
  · obtain ⟨f, hf, hc⟩ := exists_arc_chainReach hN he
    exact ⟨f, hf, Or.inr ⟨he, hc⟩⟩
  · exact ⟨e, he, Or.inl rfl⟩

/-- An arc lies on only one chain. -/
theorem IsOnChain.unique {f f' e : E} (h : N.IsOnChain f e) (h' : N.IsOnChain f' e)
    (hf : ¬ N.IsChainVertex (N.graph.source f)) (hf' : ¬ N.IsChainVertex (N.graph.source f')) :
    f = f' := by
  rcases h with rfl | ⟨he, hc⟩ <;> rcases h' with h' | ⟨he', hc'⟩
  · exact h'
  · exact absurd he' hf
  · subst h'
    exact absurd he hf'
  · exact arc_eq_of_chainReach hf hf' hc hc' he.1

/-- A single-arc cut is constant along paths avoiding the arc. -/
theorem mem_iff_mem_of_avoidingReach_of_cut {S : Set V} {e : E}
    (hS : ∀ f, N.graph.Crosses f S ↔ f = e) {u v : V} (h : N.AvoidingReach e u v) :
    u ∈ S ↔ v ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | @tail a b _ hab ih =>
    obtain ⟨f, hfe, rfl, rfl⟩ := hab
    have hn : ¬ N.graph.Crosses f S := fun h => hfe ((hS f).mp h)
    simp only [DirectedMultigraph.Crosses] at hn
    exact ih.trans (by tauto)

/-- The chain starting with `f` crosses the single-arc cut of `e` exactly when `e` is on it. -/
theorem crosses_chain_iff (hN : N.IsPhylogenetic) {S : Set V} {e f : E}
    (hS : ∀ g, N.graph.Crosses g S ↔ g = e) :
    ((N.graph.source f ∈ S ∧ chainEnd hN (N.graph.target f) ∉ S) ∨
      (chainEnd hN (N.graph.target f) ∈ S ∧ N.graph.source f ∉ S)) ↔ N.IsOnChain f e := by
  have hA := hN.acyclic
  have hend : ∀ {u v : V}, N.graph.Reaches (N.graph.target e) u → N.graph.Reaches u v →
      (u ∈ S ↔ v ∈ S) := fun hu huv =>
    mem_iff_mem_of_avoidingReach_of_cut hS (avoidingReach_of_target_reaches hA hu huv)
  constructor
  · intro hc
    by_contra hnot
    have hfe : f ≠ e := fun h => hnot (Or.inl h.symm)
    have hnf : ¬ N.graph.Crosses f S := fun h => hfe ((hS f).mp h)
    -- the arcs of the chain differ from `e`
    have hav : ∀ {w : V}, N.ChainReach (N.graph.target f) w →
        N.AvoidingReach e (N.graph.target f) w := by
      intro w hw
      induction hw with
      | refl => exact .refl
      | @tail a b hprev hstep ih =>
        obtain ⟨ha, g, hs, ht⟩ := hstep
        refine ih.tail ⟨g, ?_, hs, ht⟩
        rintro rfl
        exact hnot (Or.inr ⟨hs ▸ ha, hs ▸ hprev⟩)
    have h₁ := mem_iff_mem_of_avoidingReach_of_cut hS (hav (chainReach_chainEnd hN _))
    simp only [DirectedMultigraph.Crosses] at hnf
    tauto
  · intro hon
    -- the part of the chain above `e` and the part below `e` avoid it
    have hsrc : N.graph.source f ∈ S ↔ N.graph.source e ∈ S := by
      rcases hon with rfl | ⟨-, hc⟩
      · exact Iff.rfl
      · exact mem_iff_mem_of_avoidingReach_of_cut hS (avoidingReach_of_reaches_source hA
          ((hc.reaches).head ⟨f, rfl, rfl⟩) .refl)
    have hend' : chainEnd hN (N.graph.target f) = chainEnd hN (N.graph.target e) := by
      rcases hon with rfl | ⟨he, hc⟩
      · rfl
      · rw [chainEnd_eq_of_chainReach_left hN hc, chainEnd_eq_of_adj hN he ⟨e, rfl, rfl⟩]
    have htgt : N.graph.target e ∈ S ↔ chainEnd hN (N.graph.target f) ∈ S := by
      rw [hend']
      exact hend .refl (chainReach_chainEnd hN _).reaches
    have hcross := (hS e).mpr rfl
    simp only [DirectedMultigraph.Crosses] at hcross
    tauto

/-- **Suppression preserves the cut-edge splits.** -/
theorem suppress_hasCutSplit_iff (hN : N.IsPhylogenetic) (A : Set X) :
    (N.suppress hN).HasCutSplit A ↔ N.HasCutSplit A := by
  constructor
  · rintro ⟨e', S', hS', rfl⟩
    let φ : V → {v // ¬ N.IsChainVertex v} := fun v =>
      ⟨chainEnd hN v, not_isChainVertex_chainEnd hN v⟩
    refine ⟨e'.1, φ ⁻¹' S', fun f => ?_, ?_⟩
    · by_cases hf : N.IsChainVertex (N.graph.source f)
      · have heq : φ (N.graph.source f) = φ (N.graph.target f) :=
          Subtype.ext (chainEnd_eq_of_adj hN hf ⟨f, rfl, rfl⟩)
        have hne : f ≠ e'.1 := fun h => e'.2 (h ▸ hf)
        simp only [DirectedMultigraph.Crosses, Set.mem_preimage, heq, and_not_self, or_self,
          false_iff]
        exact hne
      · have hs : φ (N.graph.source f) = ⟨N.graph.source f, hf⟩ :=
          Subtype.ext (chainEnd_eq_self hN hf)
        have hc := hS' ⟨f, hf⟩
        simp only [DirectedMultigraph.Crosses, Set.mem_preimage, hs]
        exact hc.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    · ext x
      have : φ (N.leaf x) = (N.suppress hN).leaf x :=
        Subtype.ext (chainEnd_eq_self hN (not_isChainVertex_leaf hN x))
      simp only [Set.mem_preimage, this]
  · rintro ⟨e, S, hS, rfl⟩
    obtain ⟨f, hf, hon⟩ := exists_isOnChain hN e
    refine ⟨⟨f, hf⟩, Subtype.val ⁻¹' S, fun g => ?_, rfl⟩
    refine (crosses_chain_iff hN hS (f := g.1)).trans ⟨fun h => ?_, ?_⟩
    · exact Subtype.ext (h.unique hon g.2 hf)
    · rintro rfl
      exact hon

/-- A kept vertex keeps its outgoing arcs. -/
theorem suppress_outdegree (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    (N.suppress hN).graph.outdegree v = N.graph.outdegree v.1 := by
  refine Set.ncard_congr' ⟨fun e => ⟨e.1.1, congrArg Subtype.val e.2⟩,
    fun e => ⟨⟨e.1, ?_⟩, Subtype.ext e.2⟩, fun _ => rfl, fun _ => rfl⟩
  have he : N.graph.source e.1 = v.1 := e.2
  rw [he]
  exact v.2

/-- Two points of a chain from one vertex are comparable along it. -/
theorem ChainReach.total {a b c : V} (h : N.ChainReach a b) (h' : N.ChainReach a c) :
    N.ChainReach b c ∨ N.ChainReach c b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl h'
  | @head a a' hstep hprev ih =>
    rcases Relation.ReflTransGen.cases_head h' with rfl | ⟨a'', hstep', h''⟩
    · exact Or.inr (hprev.head hstep)
    · have heq : a' = a'' := hstep.1.adj_unique hstep.2 hstep'.2
      subst heq
      exact ih h''

/-- An arc entering a non-chain vertex is the last arc of its chain. -/
theorem IsOnChain.eq_of_target_aux {g₁ g₂ : E}
    (hg₁ : N.IsChainVertex (N.graph.source g₁)) (hg₂ : N.IsChainVertex (N.graph.source g₂))
    (hv : ¬ N.IsChainVertex (N.graph.target g₁))
    (hr : N.ChainReach (N.graph.source g₁) (N.graph.source g₂)) : g₁ = g₂ := by
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨x, hstep, hx⟩
  · obtain ⟨e, he⟩ := (N.graph.outdegree_eq_one_iff _).mp hg₁.2
    rw [(he g₁).mp rfl, (he g₂).mp h.symm]
  · have hxt : x = N.graph.target g₁ := hg₁.adj_unique hstep.2 ⟨g₁, rfl, rfl⟩
    subst hxt
    rcases Relation.ReflTransGen.cases_head hx with h | ⟨y, hy, -⟩
    · exact absurd (h ▸ hg₂) hv
    · exact absurd hy.1 hv

/-- A chain has only one last arc. -/
theorem IsOnChain.eq_of_target {f g₁ g₂ : E} (h₁ : N.IsOnChain f g₁) (h₂ : N.IsOnChain f g₂)
    (ht : N.graph.target g₁ = N.graph.target g₂) (hv : ¬ N.IsChainVertex (N.graph.target g₁)) :
    g₁ = g₂ := by
  have hone : ∀ {g g' : E}, g = f → N.IsChainVertex (N.graph.source g') →
      N.ChainReach (N.graph.target f) (N.graph.source g') → ¬ N.IsChainVertex (N.graph.target g) →
      False := by
    rintro g g' rfl hc hr hn
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨y, hy, -⟩
    · exact hn (h ▸ hc)
    · exact hn hy.1
  rcases h₁ with h₁ | ⟨hc₁, hr₁⟩ <;> rcases h₂ with h₂ | ⟨hc₂, hr₂⟩
  · rw [h₁, h₂]
  · exact (hone h₁ hc₂ hr₂ hv).elim
  · exact (hone h₂ hc₁ hr₁ (ht ▸ hv)).elim
  · rcases hr₁.total hr₂ with h | h
    · exact IsOnChain.eq_of_target_aux hc₁ hc₂ hv h
    · exact (IsOnChain.eq_of_target_aux hc₂ hc₁ (ht ▸ hv) h).symm

/-- **Suppression leaves no vertex of indegree one and outdegree one.** -/
theorem suppress_not_isChainVertex (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    ¬ (N.suppress hN).IsChainVertex v := by
  have : Finite E := hN.finite_arcs
  rintro ⟨hin, hout⟩
  rw [suppress_outdegree] at hout
  have hvr : v.1 ≠ N.root := by
    intro h
    have hv : v = (N.suppress hN).root := Subtype.ext h
    rw [hv, (suppress_isPhylogenetic hN).root_indegree] at hin
    exact Nat.zero_ne_one hin
  obtain ⟨e', he'⟩ := (DirectedMultigraph.indegree_eq_one_iff _ _).mp hin
  obtain ⟨g₁, hg₁⟩ := (N.graph.one_le_indegree_iff _).mp (hN.nonroot_indegree _ hvr)
  apply v.2
  refine ⟨(N.graph.indegree_eq_one_iff _).mpr ⟨g₁, fun g₂ => ⟨fun hg₂ => ?_, ?_⟩⟩, hout⟩
  · have hend : ∀ {f g : E}, N.IsOnChain f g → N.graph.target g = v.1 →
        chainEnd hN (N.graph.target f) = v.1 := by
      rintro f g (rfl | ⟨hc, hr⟩) ht
      · rw [ht]
        exact chainEnd_eq_self hN v.2
      · rw [chainEnd_eq_of_chainReach_left hN hr, chainEnd_eq_of_adj hN hc ⟨g, rfl, rfl⟩, ht]
        exact chainEnd_eq_self hN v.2
    obtain ⟨f₁, hf₁, hon₁⟩ := exists_isOnChain hN g₁
    obtain ⟨f₂, hf₂, hon₂⟩ := exists_isOnChain hN g₂
    have h₁ : (⟨f₁, hf₁⟩ : {e // ¬ N.IsChainVertex (N.graph.source e)}) = e' :=
      (he' _).mp (Subtype.ext (hend hon₁ hg₁))
    have h₂ : (⟨f₂, hf₂⟩ : {e // ¬ N.IsChainVertex (N.graph.source e)}) = e' :=
      (he' _).mp (Subtype.ext (hend hon₂ hg₂))
    have hff : f₁ = f₂ := congrArg Subtype.val (h₁.trans h₂.symm)
    subst hff
    exact (hon₁.eq_of_target hon₂ (hg₁.trans hg₂.symm) (hg₁ ▸ v.2)).symm
  · rintro rfl
    exact hg₁

/-- **After suppression, only the root can have degree two.** -/
theorem suppress_degree_two_eq_root (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v})
    (hv : (N.suppress hN).graph.indegree v + (N.suppress hN).graph.outdegree v = 2) :
    v = (N.suppress hN).root := by
  have hT := suppress_isPhylogenetic hN
  by_contra hne
  have h₁ := hT.nonroot_indegree v hne
  by_cases ho : (N.suppress hN).graph.outdegree v = 0
  · obtain ⟨x, rfl⟩ := (hT.leaves v).mp ho
    rw [ho, hT.leaf_indegree x] at hv
    omega
  · exact suppress_not_isChainVertex hN v ⟨by omega, by omega⟩

/-! ### The induced network -/

/-- **The network induced on `Y`**, for at least two taxa: keep the arcs and vertices
ancestral to `Y` below the LSA of `Y`, and suppress the vertices of indegree and outdegree one. -/
def inducedNetwork (hN : N.IsPhylogenetic) (Y : Set X) (hY : Y.Nontrivial) :=
  (lsaNetwork hN Y hY.nonempty).suppress (lsaNetwork_isPhylogenetic hN hY)

/-- The induced network is a phylogenetic network. -/
theorem inducedNetwork_isPhylogenetic (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial) :
    (inducedNetwork hN Y hY).IsPhylogenetic :=
  suppress_isPhylogenetic _

/-- **`HasCutSplitOn` is the cut-edge split of the induced network.** For a split of `Y` with both
sides nonempty, `HasCutSplitOn Y A` on the induced subgraph is the existence of a cut edge of the
network induced on `Y` with `A ∩ Y` on one side. -/
theorem hasCutSplitOn_iff_inducedNetwork_hasCutSplit (hN : N.IsPhylogenetic) {Y A : Set X}
    (hY : Y.Nontrivial) (h₁ : (Y ∩ A).Nonempty) (h₂ : (Y \ A).Nonempty) :
    N.HasCutSplitOn Y A ↔ (inducedNetwork hN Y hY).HasCutSplit (Subtype.val ⁻¹' A) :=
  (hasCutSplitOn_iff_lsaNetwork_hasCutSplit hN hY h₁ h₂).trans
    (suppress_hasCutSplit_iff (lsaNetwork_isPhylogenetic hN hY) _).symm

end Phylogenetics.RootedNetwork
