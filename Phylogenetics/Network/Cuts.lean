module

public import Phylogenetics.Network.Quartets
public import Phylogenetics.Graph.BridgeCutLaminar
public import Phylogenetics.Network.AncestralRestriction

/-!
# Cut edges of rooted networks through domination

A description of cut-edge splits through paths, for proofs on graphs. An arc `e`
*dominates* a taxon when every directed path from the root to the taxon uses `e`. On a rooted
network a cut edge separates exactly the taxa it dominates from the taxa not below it, so a cut-edge
split is a statement about each taxon separately:

* `HasCutSplitOn Y A` holds exactly when an arc dominates one side of the split on `Y` while the
  other side is not below it (`hasCutSplitOn_iff_separates`);
* consequently a cut edge of the subgraph induced on `Y` remains one on any `Z ⊆ Y`
  (`HasCutSplitOn.mono`), which is the forward direction of Huber et al. (2025, Theorem 5.1).

## Main definitions and results

* `AvoidingReach`, `Dominates`, `IsBelow`, `Separates`.
* `hasCutSplitOn_iff_separates`, `hasCutSplit_iff_hasCutSplitOn_univ`, `HasCutSplitOn.mono`,
  `Separates.mono`.
* `HasCutSplit.hasCutSplitOn_quartet`: the forward direction of Huber et al. (2025, Theorem 5.1).
* The path lemmas `avoidingReach_of_reaches_source`, `avoidingReach_of_target_reaches`,
  `target_reaches_of_not_avoidingReach`, `reaches_source_of_not_avoidingReach`, `Dominates.isBelow`,
  `Dominates.reaches_or_reaches`, `exists_reaches_leaf`.

## References

* K. T. Huber, L. van Iersel, M. Jones, V. Moulton, L. Veenema-Nipius, *When are quarnets sufficient to
  reconstruct semi-directed phylogenetic networks?*, Bull. Math. Biol. 87 (2025), 136.
-/

@[expose] public section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- `v` is reachable from `u` by a directed path not using the arc `e`. -/
def AvoidingReach (e : E) : V → V → Prop :=
  Relation.ReflTransGen fun a b => ∃ f, f ≠ e ∧ N.graph.source f = a ∧ N.graph.target f = b

/-- Every directed path from the root to the taxon `x` uses the arc `e`. -/
def Dominates (e : E) (x : X) : Prop := ¬ N.AvoidingReach e N.root (N.leaf x)

/-- The taxon `x` is below the arc `e`. -/
def IsBelow (e : E) (x : X) : Prop := N.graph.Reaches (N.graph.target e) (N.leaf x)

/-- The arc `e` dominates all taxa of `P`, and no taxon of `Q` is below it. -/
def Separates (e : E) (P Q : Set X) : Prop :=
  (∀ x ∈ P, N.Dominates e x) ∧ ∀ x ∈ Q, ¬ N.IsBelow e x

variable {N}

/-! ### Paths and acyclicity -/

/-- A path avoiding an arc is a path. -/
theorem AvoidingReach.reaches {e : E} {u v : V} (h : N.AvoidingReach e u v) :
    N.graph.Reaches u v := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro _ _ ⟨f, _, hs, ht⟩
  exact ⟨f, hs, ht⟩

/-- In an acyclic graph the target of an arc does not reach its source. -/
theorem not_reaches_target_source (hA : N.graph.IsAcyclic) (e : E) :
    ¬ N.graph.Reaches (N.graph.target e) (N.graph.source e) := fun h =>
  hA _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)

/-- By acyclicity, a path ending above an arc avoids it. -/
theorem avoidingReach_of_reaches_source (hA : N.graph.IsAcyclic) {e : E} {u v : V}
    (huv : N.graph.Reaches u v) (hv : N.graph.Reaches v (N.graph.source e)) :
    N.AvoidingReach e u v := by
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab _ ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    refine Relation.ReflTransGen.head ⟨f, ?_, rfl, rfl⟩ ih
    rintro rfl
    exact not_reaches_target_source hA f (ih.reaches.trans hv)

/-- By acyclicity, a path starting below an arc avoids it. -/
theorem avoidingReach_of_target_reaches (hA : N.graph.IsAcyclic) {e : E} {u v : V}
    (hu : N.graph.Reaches (N.graph.target e) u) (huv : N.graph.Reaches u v) :
    N.AvoidingReach e u v := by
  induction huv with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    refine Relation.ReflTransGen.tail ih ⟨f, ?_, rfl, rfl⟩
    rintro rfl
    exact not_reaches_target_source hA f (hu.trans ih.reaches)

/-- A path that does not avoid an arc passes through it, so the arc's target reaches its end. -/
theorem target_reaches_of_not_avoidingReach {e : E} {u v : V} (huv : N.graph.Reaches u v)
    (hne : ¬ N.AvoidingReach e u v) : N.graph.Reaches (N.graph.target e) v := by
  induction huv with
  | refl => exact absurd .refl hne
  | @tail a b hua hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    by_cases hfe : f = e
    · subst hfe
      exact .refl
    · by_cases ha : N.AvoidingReach e u (N.graph.source f)
      · exact absurd (ha.tail ⟨f, hfe, rfl, rfl⟩) hne
      · exact (ih ha).tail ⟨f, rfl, rfl⟩

/-- A path that does not avoid an arc passes through it, so its start reaches the arc's source. -/
theorem reaches_source_of_not_avoidingReach {e : E} {u v : V} (huv : N.graph.Reaches u v)
    (hne : ¬ N.AvoidingReach e u v) : N.graph.Reaches u (N.graph.source e) := by
  induction huv with
  | refl => exact absurd .refl hne
  | @tail a b hua hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    by_cases hfe : f = e
    · subst hfe
      exact hua
    · by_cases ha : N.AvoidingReach e u (N.graph.source f)
      · exact absurd (ha.tail ⟨f, hfe, rfl, rfl⟩) hne
      · exact ih ha

/-- The part of a path before its first use of the arc `g` keeps avoiding what the path avoids. -/
theorem AvoidingReach.source_of_not_avoidingReach {g h : E} {u v : V}
    (hv : N.AvoidingReach h u v) (hne : ¬ N.AvoidingReach g u v) :
    N.AvoidingReach h u (N.graph.source g) := by
  induction hv with
  | refl => exact absurd .refl hne
  | @tail a b hua hab ih =>
    obtain ⟨f, hfh, rfl, rfl⟩ := hab
    by_cases hfg : f = g
    · subst hfg
      exact hua
    · by_cases ha : N.AvoidingReach g u (N.graph.source f)
      · exact absurd (ha.tail ⟨f, hfg, rfl, rfl⟩) hne
      · exact ih ha

/-- A taxon dominated by an arc is below it. -/
theorem Dominates.isBelow (hN : N.IsPhylogenetic) {e : E} {x : X} (h : N.Dominates e x) :
    N.IsBelow e x :=
  target_reaches_of_not_avoidingReach (hN.root_reaches _) h

/-- Every vertex reaches a taxon: a finite acyclic graph has sinks below every vertex, and the sinks
of a phylogenetic network are its taxa. -/
theorem exists_reaches_leaf (hN : N.IsPhylogenetic) (v : V) :
    ∃ x, N.graph.Reaches v (N.leaf x) := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  induction v using hwf.induction with
  | _ v ih =>
    by_cases hout : N.graph.outdegree v = 0
    · obtain ⟨x, rfl⟩ := (hN.leaves v).mp hout
      exact ⟨x, .refl⟩
    · rw [N.graph.outdegree_eq_zero_iff] at hout
      push Not at hout
      obtain ⟨e, rfl⟩ := hout
      obtain ⟨x, hx⟩ := ih (N.graph.target e) (.single ⟨e, rfl, rfl⟩)
      exact ⟨x, hx.head ⟨e, rfl, rfl⟩⟩

/-- Two distinct arcs dominating one taxon are ordered: they lie on a common path. -/
theorem Dominates.reaches_or_reaches (hN : N.IsPhylogenetic) {g g' : E} {x : X}
    (hg : N.Dominates g x) (hg' : N.Dominates g' x) (hne : g ≠ g') :
    N.graph.Reaches (N.graph.target g) (N.graph.source g') ∨
      N.graph.Reaches (N.graph.target g') (N.graph.source g) := by
  by_cases h : N.AvoidingReach g' N.root (N.graph.source g)
  · left
    refine reaches_source_of_not_avoidingReach (hg.isBelow hN) fun h₂ => hg' ?_
    exact (h.tail ⟨g, hne, rfl, rfl⟩).trans h₂
  · exact Or.inr (target_reaches_of_not_avoidingReach (hN.root_reaches _) h)

/-! ### The two directions of the characterization -/

/-- No arc of the induced subgraph other than `e` crosses `S`, so a path avoiding `e` towards a
taxon of `Y` stays on one side. -/
theorem mem_iff_mem_of_avoidingReach {Y : Set X} {S : Set V} {e : E}
    (hS : ∀ f ∈ N.ancestralArcs Y, f ≠ e → ¬ N.graph.Crosses f S) {u v : V}
    (h : N.AvoidingReach e u v) (hv : v ∈ N.ancestralVertices Y) : u ∈ S ↔ v ∈ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Iff.rfl
  | @head a b hab hbv ih =>
    obtain ⟨f, hfe, rfl, rfl⟩ := hab
    have hf : f ∈ N.ancestralArcs Y :=
      N.mem_ancestralVertices_of_reaches (AvoidingReach.reaches hbv) hv
    have hn := hS f hf hfe
    simp only [DirectedMultigraph.Crosses] at hn
    exact Iff.trans (by tauto) ih

/-- The forward direction: if `e` is the only arc of the induced subgraph crossing `T`, and `T` is
the side of the target of `e`, then `T` contains a taxon of `Y`, its taxa are dominated by `e`, and
the taxa of `Y` on the side of the source are not below `e`. -/
theorem separates_of_crossing {Y : Set X} {T : Set V} {e : E} (hN : N.IsPhylogenetic)
    (he : e ∈ N.ancestralArcs Y) (hT : ∀ f ∈ N.ancestralArcs Y, f ≠ e → ¬ N.graph.Crosses f T)
    (ht : N.graph.target e ∈ T) (hs : N.graph.source e ∉ T) :
    (∃ x ∈ Y, N.leaf x ∈ T) ∧ (∀ x ∈ Y, N.leaf x ∈ T → N.Dominates e x) ∧
      ∀ x ∈ Y, N.leaf x ∉ T → ¬ N.IsBelow e x := by
  have hsv : N.graph.source e ∈ N.ancestralVertices Y := N.source_mem_ancestralVertices he
  have hroot : N.root ∉ T := fun h => hs ((mem_iff_mem_of_avoidingReach hT
    (avoidingReach_of_reaches_source hN.acyclic (hN.root_reaches _) .refl) hsv).mp h)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hpath⟩ := he
    exact ⟨x, hx, (mem_iff_mem_of_avoidingReach hT
      (avoidingReach_of_target_reaches hN.acyclic .refl hpath)
      (N.leaf_mem_ancestralVertices hx)).mp ht⟩
  · intro x hx hxT hav
    exact hroot ((mem_iff_mem_of_avoidingReach hT hav (N.leaf_mem_ancestralVertices hx)).mpr hxT)
  · intro x hx hxT hbelow
    exact hxT ((mem_iff_mem_of_avoidingReach hT
      (avoidingReach_of_target_reaches hN.acyclic .refl hbelow)
      (N.leaf_mem_ancestralVertices hx)).mp ht)

/-- The set of vertices all of whose root paths use `e`. -/
def domSet (N : RootedNetwork V E X) (e : E) : Set V := {v | ¬ N.AvoidingReach e N.root v}

/-- The backward direction: if `e` dominates a taxon of `Y` and every taxon of `Y` is either
dominated by `e` or not below it, then `e` is an arc of the induced subgraph, and the only one
crossing the set of vertices all of whose root paths use `e`. -/
theorem crosses_domSet_iff {Y : Set X} {e : E} {x₀ : X} (hN : N.IsPhylogenetic)
    (hx₀ : x₀ ∈ Y) (hd : N.Dominates e x₀) (hY : ∀ y ∈ Y, N.Dominates e y ∨ ¬ N.IsBelow e y) :
    e ∈ N.ancestralArcs Y ∧ ∀ f ∈ N.ancestralArcs Y, N.graph.Crosses f (N.domSet e) ↔ f = e := by
  have hA := hN.acyclic
  have hb : N.IsBelow e x₀ := hd.isBelow hN
  have ht : N.graph.target e ∈ N.domSet e := fun h =>
    hd (h.trans (avoidingReach_of_target_reaches hA .refl hb))
  have hs : N.graph.source e ∉ N.domSet e := fun h =>
    h (avoidingReach_of_reaches_source hA (hN.root_reaches _) .refl)
  refine ⟨⟨x₀, hx₀, hb⟩, ?_⟩
  intro f hf
  constructor
  · rintro (⟨hsf, htf⟩ | ⟨htf, hsf⟩)
    · have hbelow : N.graph.Reaches (N.graph.target e) (N.graph.source f) :=
        target_reaches_of_not_avoidingReach (hN.root_reaches _) hsf
      have htf' : N.AvoidingReach e N.root (N.graph.target f) := not_not.mp htf
      obtain ⟨y, hy, hpath⟩ := hf
      have hbt : N.graph.Reaches (N.graph.target e) (N.graph.target f) :=
        hbelow.tail ⟨f, rfl, rfl⟩
      have hyb : N.IsBelow e y := hbt.trans hpath
      rcases hY y hy with hdy | hny
      · exact absurd (htf'.trans (avoidingReach_of_target_reaches hA hbt hpath)) hdy
      · exact absurd hyb hny
    · by_contra hfe
      exact htf (Relation.ReflTransGen.tail (not_not.mp hsf) ⟨f, hfe, rfl, rfl⟩)
  · rintro rfl
    exact Or.inr ⟨ht, hs⟩

/-- **The domination characterization of cut-edge splits.** `A ∩ Y | Y \ A` is a cut-edge split of
the network induced on `Y` exactly when an arc dominates one nonempty side and has no taxon of the
other side below it. -/
theorem hasCutSplitOn_iff_separates (hN : N.IsPhylogenetic) (Y A : Set X) :
    N.HasCutSplitOn Y A ↔ ∃ e, ((Y ∩ A).Nonempty ∧ N.Separates e (Y ∩ A) (Y \ A)) ∨
      ((Y \ A).Nonempty ∧ N.Separates e (Y \ A) (Y ∩ A)) := by
  constructor
  · rintro ⟨e, he, S, hS, hA⟩
    refine ⟨e, ?_⟩
    rcases (hS e he).mpr rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · have hT : ∀ f ∈ N.ancestralArcs Y, f ≠ e → ¬ N.graph.Crosses f Sᶜ := fun f hf hfe hc =>
        hfe ((hS f hf).mp ((N.graph.crosses_compl f S).mp hc))
      obtain ⟨⟨x, hx, hxT⟩, hdom, hnb⟩ := separates_of_crossing hN he hT ht (not_not.mpr hs)
      refine Or.inr ⟨⟨x, hx, fun h => hxT ((hA x hx).mpr h)⟩, ?_, ?_⟩
      · exact fun y hy => hdom y hy.1 fun h => hy.2 ((hA y hy.1).mp h)
      · exact fun y hy => hnb y hy.1 (not_not.mpr ((hA y hy.1).mpr hy.2))
    · have hT : ∀ f ∈ N.ancestralArcs Y, f ≠ e → ¬ N.graph.Crosses f S := fun f hf hfe hc =>
        hfe ((hS f hf).mp hc)
      obtain ⟨⟨x, hx, hxT⟩, hdom, hnb⟩ := separates_of_crossing hN he hT ht hs
      refine Or.inl ⟨⟨x, hx, (hA x hx).mp hxT⟩, ?_, ?_⟩
      · exact fun y hy => hdom y hy.1 ((hA y hy.1).mpr hy.2)
      · exact fun y hy => hnb y hy.1 fun h => hy.2 ((hA y hy.1).mp h)
  · rintro ⟨e, ⟨⟨x₀, hY₀, hA₀⟩, hdom, hnb⟩ | ⟨⟨x₀, hY₀, hA₀⟩, hdom, hnb⟩⟩
    · have hY : ∀ y ∈ Y, N.Dominates e y ∨ ¬ N.IsBelow e y := fun y hy => by
        by_cases hyA : y ∈ A
        · exact Or.inl (hdom y ⟨hy, hyA⟩)
        · exact Or.inr (hnb y ⟨hy, hyA⟩)
      obtain ⟨he, hc⟩ := crosses_domSet_iff hN hY₀ (hdom x₀ ⟨hY₀, hA₀⟩) hY
      refine ⟨e, he, N.domSet e, hc, fun y hy => ⟨fun h => ?_, fun h => hdom y ⟨hy, h⟩⟩⟩
      by_contra hyA
      exact hnb y ⟨hy, hyA⟩ (Dominates.isBelow hN h)
    · have hY : ∀ y ∈ Y, N.Dominates e y ∨ ¬ N.IsBelow e y := fun y hy => by
        by_cases hyA : y ∈ A
        · exact Or.inr (hnb y ⟨hy, hyA⟩)
        · exact Or.inl (hdom y ⟨hy, hyA⟩)
      obtain ⟨he, hc⟩ := crosses_domSet_iff hN hY₀ (hdom x₀ ⟨hY₀, hA₀⟩) hY
      refine ⟨e, he, (N.domSet e)ᶜ, fun f hf => (N.graph.crosses_compl f _).trans (hc f hf),
        fun y hy => ⟨fun h => ?_, fun h hd => hnb y ⟨hy, h⟩ (Dominates.isBelow hN hd)⟩⟩
      by_contra hyA
      exact h (hdom y ⟨hy, hyA⟩)

/-- A cut-edge split of the network is one of the network induced on all the taxa, since every arc
is ancestral to a taxon. -/
theorem hasCutSplit_iff_hasCutSplitOn_univ (hN : N.IsPhylogenetic) (A : Set X) :
    N.HasCutSplit A ↔ N.HasCutSplitOn Set.univ A := by
  have hall : ∀ f, f ∈ N.ancestralArcs Set.univ := fun f => by
    obtain ⟨x, hx⟩ := exists_reaches_leaf hN (N.graph.target f)
    exact ⟨x, Set.mem_univ x, hx⟩
  constructor
  · rintro ⟨e, S, hS, rfl⟩
    exact ⟨e, hall e, S, fun f _ => hS f, fun x _ => Iff.rfl⟩
  · rintro ⟨e, -, S, hS, hA⟩
    exact ⟨e, S, fun f => hS f (hall f), Set.ext fun x => hA x (Set.mem_univ x)⟩

/-- Separation restricts to subsets. -/
theorem Separates.mono {e : E} {P Q P' Q' : Set X} (h : N.Separates e P Q)
    (hP : P' ⊆ P) (hQ : Q' ⊆ Q) : N.Separates e P' Q' :=
  ⟨fun x hx => h.1 x (hP hx), fun x hx => h.2 x (hQ hx)⟩

/-- A cut-edge split of the network induced on `Y` restricts to a cut-edge split of the network
induced on any `Z ⊆ Y` whose two sides are both nonempty. -/
theorem HasCutSplitOn.mono (hN : N.IsPhylogenetic) {Y Z A : Set X} (h : N.HasCutSplitOn Y A)
    (hZ : Z ⊆ Y) (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) : N.HasCutSplitOn Z A := by
  rw [hasCutSplitOn_iff_separates hN] at h ⊢
  obtain ⟨e, ⟨_, hs⟩ | ⟨_, hs⟩⟩ := h
  · exact ⟨e, Or.inl ⟨h₁, hs.mono (Set.inter_subset_inter_left A hZ)
      (Set.sdiff_subset_sdiff_left hZ)⟩⟩
  · exact ⟨e, Or.inr ⟨h₂, hs.mono (Set.sdiff_subset_sdiff_left hZ)
      (Set.inter_subset_inter_left A hZ)⟩⟩

/-- A cut side of the network restricts to any taxon set with both sides nonempty. -/
theorem HasCutSplit.hasCutSplitOn (hN : N.IsPhylogenetic) {Z A : Set X} (h : N.HasCutSplit A)
    (h₁ : (Z ∩ A).Nonempty) (h₂ : (Z \ A).Nonempty) : N.HasCutSplitOn Z A :=
  ((hasCutSplit_iff_hasCutSplitOn_univ hN A).mp h).mono hN (Set.subset_univ Z) h₁ h₂

/-- The split is symmetric. -/
theorem hasCutSplitOn_compl (Y A : Set X) : N.HasCutSplitOn Y Aᶜ ↔ N.HasCutSplitOn Y A := by
  have flip : ∀ B : Set X, N.HasCutSplitOn Y B → N.HasCutSplitOn Y Bᶜ := by
    rintro B ⟨e, he, S, hS, hB⟩
    refine ⟨e, he, Sᶜ, fun f hf => (N.graph.crosses_compl f S).trans (hS f hf), fun x hx => ?_⟩
    simp only [Set.mem_compl_iff, hB x hx]
  exact ⟨fun h => by simpa only [compl_compl] using flip Aᶜ h, flip A⟩

/-- The split depends only on the side's trace on `Y`. -/
theorem hasCutSplitOn_congr {Y A B : Set X} (h : Y ∩ A = Y ∩ B) :
    N.HasCutSplitOn Y A ↔ N.HasCutSplitOn Y B := by
  have hmem : ∀ x ∈ Y, x ∈ A ↔ x ∈ B := fun x hx => by
    have := Set.ext_iff.mp h x
    simpa only [Set.mem_inter_iff, hx, true_and] using this
  constructor
  · rintro ⟨e, he, S, hS, hA⟩
    exact ⟨e, he, S, hS, fun x hx => (hA x hx).trans (hmem x hx)⟩
  · rintro ⟨e, he, S, hS, hB⟩
    exact ⟨e, he, S, hS, fun x hx => (hB x hx).trans (hmem x hx).symm⟩

/-- A path whose vertices avoid `l`, when `l` does not reach its end. -/
theorem avoiding_of_not_reaches {l a b : V} (h : N.graph.Reaches a b)
    (hl : ¬ N.graph.Reaches l b) :
    Relation.ReflTransGen (fun c d => N.graph.Adj c d ∧ c ≠ l ∧ d ≠ l) a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head c d hcd hdb ih =>
    refine .head ⟨hcd, ?_, ?_⟩ ih
    · rintro rfl
      exact hl (hdb.head hcd)
    · rintro rfl
      exact hl hdb

section Huber

variable {V E X : Type*} [Fintype X] [DecidableEq X] {N : RootedNetwork V E X}

omit [Fintype X] in
/-- **Huber et al. (2025, Theorem 5.1), forward direction.** If `A|B` is the split of a cut edge, then for all distinct
`a₁, a₂ ∈ A` and `b₁, b₂ ∈ B`, `a₁a₂|b₁b₂` is the split of a cut edge of the network induced on
these taxa. They treat binary semi-directed networks; the binary condition is not needed. -/
theorem HasCutSplit.hasCutSplitOn_quartet (hN : N.IsPhylogenetic) {A : Finset X} (hA : N.HasCutSplit (A : Set X))
    {a₁ a₂ b₁ b₂ : X} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∉ A) (hb₂ : b₂ ∉ A) :
    N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (({a₁, a₂} : Finset X) : Set X) := by
  have hcut : N.HasCutSplitOn (({a₁, a₂, b₁, b₂} : Finset X) : Set X) (A : Set X) :=
    hA.hasCutSplitOn hN ⟨a₁, by simp, ha₁⟩ ⟨b₁, by simp, hb₁⟩
  refine (hasCutSplitOn_congr ?_).mp hcut
  ext x
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hx | hx | hx | hx, hxA⟩
    · exact ⟨Or.inl hx, Or.inl hx⟩
    · exact ⟨Or.inr (Or.inl hx), Or.inr hx⟩
    · exact absurd (hx ▸ hxA) hb₁
    · exact absurd (hx ▸ hxA) hb₂
  · rintro ⟨-, rfl | rfl⟩
    · exact ⟨Or.inl rfl, ha₁⟩
    · exact ⟨Or.inr (Or.inl rfl), ha₂⟩

end Huber

end Phylogenetics.RootedNetwork
