module

public import Phylogenetics.Graph.BridgeCutLaminar
public import Phylogenetics.Graph.Blobs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Blobs and trees in directed multigraphs

* `isBlob_iff`: the classes of `blobSetoid` are exactly the blobs (Allman, Baños, Mitchell, Rhodes 2024, Definition 1), the
  maximal connected subgraphs without cut edges.
* `IsTree`, `IsTree.toSimpleGraph_isTree`: connected multigraphs without cycles, and the link with
  Mathlib's trees.
* `bridgeQuotient_isTree`: contracting the blobs of a connected graph gives a tree.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a
  species network under the coalescent model*, Algorithms Mol. Biol. 19 (2024), 23.
-/

@[expose] public noncomputable section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-! ### Blobs -/

variable {G} in
theorem walks_mono {F F' : Set E} (hF : F ⊆ F') {u v : V} (h : G.Walks F u v) : G.Walks F' u v := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro a b ⟨e, he, hl⟩
  exact ⟨e, hF he, hl⟩

/-- The vertex set `U` and arc set `F` form a connected subgraph with no cut edges: deleting any of
its arcs leaves it connected. -/
structure IsBridgelessSubgraph (U : Set V) (F : Set E) : Prop where
  nonempty : U.Nonempty
  endpoints : ∀ f ∈ F, G.source f ∈ U ∧ G.target f ∈ U
  connected : ∀ u ∈ U, ∀ v ∈ U, G.Walks F u v
  no_cut_edge : ∀ f ∈ F, ∀ u ∈ U, ∀ v ∈ U, G.Walks (F \ {f}) u v

/-- **A blob**: a maximal connected subgraph with no cut edges. -/
def IsBlob (U : Set V) (F : Set E) : Prop :=
  G.IsBridgelessSubgraph U F ∧
    ∀ U' F', G.IsBridgelessSubgraph U' F' → U ⊆ U' → F ⊆ F' → U' = U ∧ F' = F

/-- A walk between two vertices on one side of a singleton cut can avoid the cut's arc. -/
theorem walks_diff_of_cut {F : Set E} {T : Set V} {b : E} (hT : ∀ f, G.Crosses f T ↔ f = b)
    {u v : V} (h : G.Walks F u v) (hu : u ∈ T) (hv : v ∈ T) : G.Walks (F \ {b}) u v := by
  obtain ⟨z, hz, hzb⟩ : ∃ z ∈ T, G.source b = z ∨ G.target b = z := by
    rcases (hT b).mpr rfl with ⟨hs, _⟩ | ⟨ht, _⟩
    · exact ⟨_, hs, Or.inl rfl⟩
    · exact ⟨_, ht, Or.inr rfl⟩
  have key : ∀ y, G.Walks F u y →
      (y ∈ T → G.Walks (F \ {b}) u y) ∧ (y ∉ T → G.Walks (F \ {b}) u z) := by
    intro y hy
    induction hy with
    | refl => exact ⟨fun _ => .refl, fun h => absurd hu h⟩
    | @tail a c _ hstep ih =>
      obtain ⟨g, hg, hlink⟩ := hstep
      by_cases hgb : g = b
      · subst hgb
        have hcross := (hT g).mpr rfl
        have hside : (a ∈ T ∧ c ∉ T) ∨ (c ∈ T ∧ a ∉ T) := by
          rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Crosses] at hcross <;> tauto
        rcases hside with ⟨ha, hc⟩ | ⟨hc, ha⟩
        · have haz : a = z := by
            rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzb with rfl | rfl
            · rfl
            · exact absurd hz hc
            · exact absurd hz hc
            · rfl
          subst haz
          exact ⟨fun h => absurd h hc, fun _ => ih.1 ha⟩
        · have hcz : c = z := by
            rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hzb with rfl | rfl
            · exact absurd hz ha
            · rfl
            · rfl
            · exact absurd hz ha
          subst hcz
          exact ⟨fun _ => ih.2 ha, fun h => absurd hc h⟩
      · have hnc : ¬ G.Crosses g T := fun h => hgb ((hT g).mp h)
        have hstep' : G.AdjOn (F \ {b}) a c := ⟨g, ⟨hg, hgb⟩, hlink⟩
        have hiff : a ∈ T ↔ c ∈ T := by
          simp only [Crosses] at hnc
          rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
        exact ⟨fun hc => (ih.1 (hiff.mpr hc)).tail hstep', fun hc => ih.2 fun ha => hc (hiff.mp ha)⟩
  exact (key v h).1 hv

/-- A walk between two vertices of one blob class can avoid all bridges. -/
theorem walks_diff_bridges [Finite E] {F : Set E} {u v : V} (h : G.Walks F u v)
    (huv : G.blobSetoid.r u v) : G.Walks (F \ {e | G.underlying.IsBridge e}) u v := by
  classical
  have key : ∀ B : Finset E, (∀ b ∈ B, G.underlying.IsBridge b) →
      G.Walks (F \ (B : Set E)) u v := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro _
      simpa using h
    | insert b B _ ih =>
      intro hB
      have h' := ih fun c hc => hB c (Finset.mem_insert_of_mem hc)
      have hb := hB b (Finset.mem_insert_self b B)
      obtain ⟨S, hS⟩ := (G.isBridge_iff b).mp hb
      have hsame : u ∈ S ↔ v ∈ S := G.mem_iff_mem_of_walks (F := {e | ¬ G.underlying.IsBridge e})
        (fun f hf hc => hf ((hS f).mp hc ▸ hb)) huv
      have hsub : (F \ (B : Set E)) \ {b} ⊆ F \ ((insert b B : Finset E) : Set E) := by
        rintro f ⟨⟨hf, hfB⟩, hfb⟩
        refine ⟨hf, fun hmem => ?_⟩
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hmem) with h | h
        · exact hfb h
        · exact hfB h
      by_cases hu : u ∈ S
      · exact walks_mono hsub (G.walks_diff_of_cut hS h' hu (hsame.mp hu))
      · have hS' : ∀ f, G.Crosses f Sᶜ ↔ f = b := fun f => (G.crosses_compl f S).trans (hS f)
        exact walks_mono hsub (G.walks_diff_of_cut hS' h' hu fun hv => hu (hsame.mpr hv))
  have hfin := Set.toFinite {e | G.underlying.IsBridge e}
  have := key hfin.toFinset fun b hb => hfin.mem_toFinset.mp hb
  rwa [hfin.coe_toFinset] at this

/-- The arcs inside the blob class of `v`. -/
def blobArcs (v : V) : Set E :=
  {f | ¬ G.underlying.IsBridge f ∧ G.blobSetoid.r v (G.source f)}

/-- A walk by nonbridge arcs in `H` from the blob class of `v` uses arcs of that blob in `H`. -/
theorem walks_blobArcs {v u w : V} {H : Set E} (hu : G.blobSetoid.r v u)
    (h : G.Walks ({e | ¬ G.underlying.IsBridge e} ∩ H) u w) : G.Walks (G.blobArcs v ∩ H) u w := by
  induction h with
  | refl => exact .refl
  | @tail a c hprev hstep ih =>
    obtain ⟨g, ⟨hgn, hgH⟩, hlink⟩ := hstep
    have ha : G.blobSetoid.r v a := Relation.ReflTransGen.trans hu
      (walks_mono Set.inter_subset_left hprev)
    have hgs : G.blobSetoid.r v (G.source g) := by
      rcases hlink with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact ha
      · exact Relation.ReflTransGen.tail ha ⟨g, hgn, Or.inr ⟨rfl, rfl⟩⟩
    exact ih.tail ⟨g, ⟨⟨hgn, hgs⟩, hgH⟩, hlink⟩

theorem walks_blobArcs_of_walks {v u w : V} (hu : G.blobSetoid.r v u)
    (h : G.Walks {e | ¬ G.underlying.IsBridge e} u w) : G.Walks (G.blobArcs v) u w := by
  have h' := G.walks_blobArcs (H := Set.univ) hu (by rwa [Set.inter_univ])
  rwa [Set.inter_univ] at h'

/-- The blob class of `v` with its nonbridge arcs is a connected subgraph without cut edges. -/
theorem isBridgelessSubgraph_blobClass [Finite E] (v : V) :
    G.IsBridgelessSubgraph {w | G.blobSetoid.r v w} (G.blobArcs v) := by
  have hrefl : G.blobSetoid.r v v := Relation.ReflTransGen.refl
  have hconn : ∀ {u w : V}, G.blobSetoid.r v u → G.blobSetoid.r v w →
      G.Walks {e | ¬ G.underlying.IsBridge e} u w := fun hu hw =>
    (G.walks_symm hu).trans hw
  refine ⟨⟨v, hrefl⟩, ?_, ?_, ?_⟩
  · rintro f ⟨hf, hs⟩
    exact ⟨hs, Relation.ReflTransGen.tail hs ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro u hu w hw
    exact G.walks_blobArcs_of_walks hu (hconn hu hw)
  · rintro f ⟨hf, hs⟩ u hu w hw
    -- a detour around `f`
    have hdet : G.Walks (G.blobArcs v \ {f}) (G.source f) (G.target f) := by
      have hnb : G.Walks {f}ᶜ (G.source f) (G.target f) := by
        by_contra hcon
        exact hf ((G.isBridge_iff_not_walks_delete f).mpr hcon)
      have h₁ := G.walks_diff_bridges hnb
        (Relation.ReflTransGen.single (⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩ : G.AdjOn _ _ _))
      have h₂ : G.Walks ({e | ¬ G.underlying.IsBridge e} ∩ {f}ᶜ) (G.source f) (G.target f) :=
        walks_mono (by rintro e ⟨h, h'⟩; exact ⟨h', h⟩) h₁
      exact walks_mono (by rintro e ⟨h, h'⟩; exact ⟨h, h'⟩) (G.walks_blobArcs hs h₂)
    have hmain : ∀ {a : V}, G.Walks (G.blobArcs v) u a → G.Walks (G.blobArcs v \ {f}) u a := by
      intro a ha
      induction ha with
      | refl => exact .refl
      | @tail a c _ hstep ih =>
        obtain ⟨g, hg, hlink⟩ := hstep
        by_cases hgf : g = f
        · subst hgf
          rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans hdet
          · exact ih.trans (G.walks_symm hdet)
        · exact ih.tail ⟨g, ⟨hg, hgf⟩, hlink⟩
    exact hmain (G.walks_blobArcs_of_walks hu (hconn hu hw))

/-- A connected subgraph without cut edges has only nonbridge arcs of the graph, and lies in one
blob class. -/
theorem IsBridgelessSubgraph.subset_blobClass {G : DirectedMultigraph V E} {U : Set V} {F : Set E}
    (h : G.IsBridgelessSubgraph U F) {v : V} (hv : v ∈ U) :
    U ⊆ {w | G.blobSetoid.r v w} ∧ F ⊆ G.blobArcs v := by
  have hF : F ⊆ {e | ¬ G.underlying.IsBridge e} := by
    intro f hf hb
    obtain ⟨S, hS⟩ := (G.isBridge_iff f).mp hb
    obtain ⟨hs, ht⟩ := h.endpoints f hf
    have hd := h.no_cut_edge f hf _ hs _ ht
    have hsame := G.mem_iff_mem_of_walks (F := F \ {f}) (S := S)
      (fun g hg hc => hg.2 ((hS g).mp hc)) hd
    have hcross := (hS f).mpr rfl
    simp only [Crosses] at hcross
    tauto
  have hU : U ⊆ {w | G.blobSetoid.r v w} := fun w hw =>
    walks_mono hF (h.connected v hv w hw)
  exact ⟨hU, fun f hf => ⟨hF hf, hU (h.endpoints f hf).1⟩⟩

/-- **The classes of `blobSetoid` are exactly the blobs.** A blob is the
blob class of any of its vertices, with the nonbridge arcs leaving that class. -/
theorem isBlob_iff [Finite E] (U : Set V) (F : Set E) :
    G.IsBlob U F ↔ ∃ v, U = {w | G.blobSetoid.r v w} ∧ F = G.blobArcs v := by
  constructor
  · rintro ⟨h, hmax⟩
    obtain ⟨v, hv⟩ := h.nonempty
    obtain ⟨h₁, h₂⟩ := h.subset_blobClass hv
    obtain ⟨h₃, h₄⟩ := hmax _ _ (G.isBridgelessSubgraph_blobClass v) h₁ h₂
    exact ⟨v, h₃.symm, h₄.symm⟩
  · rintro ⟨v, rfl, rfl⟩
    refine ⟨G.isBridgelessSubgraph_blobClass v, fun U' F' h' hU hF => ?_⟩
    obtain ⟨h₁, h₂⟩ := h'.subset_blobClass (hU Relation.ReflTransGen.refl)
    exact ⟨h₁.antisymm hU, h₂.antisymm hF⟩

/-- Every vertex is in a blob: the blob classes partition the vertices into blobs. -/
theorem isBlob_blobClass [Finite E] (v : V) :
    G.IsBlob {w | G.blobSetoid.r v w} (G.blobArcs v) :=
  (G.isBlob_iff _ _).mpr ⟨v, rfl, rfl⟩

/-! ### Trees -/

/-- A tree: a connected multigraph with no cycle, that is, whose arcs have endpoints joined by no
walk avoiding them. Equivalently (`isBridge_iff_not_walks_delete`), a connected graph all of whose
arcs are bridges. -/
def IsTree : Prop :=
  G.IsConnected ∧ ∀ e, ¬ G.Walks {e}ᶜ (G.source e) (G.target e)

/-- The simple graph underlying a multigraph. -/
def toSimpleGraph : SimpleGraph V := SimpleGraph.fromRel G.Adj

variable {G} in
/-- A multigraph tree is a tree in the sense of Mathlib. -/
theorem IsTree.toSimpleGraph_isTree [Nonempty V] (h : G.IsTree) : G.toSimpleGraph.IsTree := by
  obtain ⟨hconn, hcyc⟩ := h
  have hstep : ∀ {u v : V}, G.AdjOn Set.univ u v → G.toSimpleGraph.Reachable u v := by
    rintro u v ⟨e, -, hl⟩
    by_cases huv : u = v
    · subst huv
      exact SimpleGraph.Reachable.refl u
    · refine SimpleGraph.Adj.reachable ?_
      rw [toSimpleGraph, SimpleGraph.fromRel_adj]
      refine ⟨huv, ?_⟩
      rcases hl with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨e, hs, ht⟩
      · exact Or.inr ⟨e, hs, ht⟩
  refine ⟨⟨?_⟩, ?_⟩
  · intro u v
    induction hconn u v with
    | refl => exact SimpleGraph.Reachable.refl u
    | tail _ hst ih => exact ih.trans (hstep hst)
  · rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro v w hvw
    rw [SimpleGraph.isBridge_iff]
    intro hr
    rw [toSimpleGraph, SimpleGraph.fromRel_adj] at hvw
    -- an arc `e` between `v` and `w`
    obtain ⟨e, he⟩ : ∃ e, (G.source e = v ∧ G.target e = w) ∨
        (G.source e = w ∧ G.target e = v) := by
      rcases hvw.2 with ⟨e, hs, ht⟩ | ⟨e, hs, ht⟩
      · exact ⟨e, Or.inl ⟨hs, ht⟩⟩
      · exact ⟨e, Or.inr ⟨hs, ht⟩⟩
    have hwalk : G.Walks {e}ᶜ v w := by
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      refine Relation.ReflTransGen.mono ?_ _ _ hr
      intro a b hab
      rw [SimpleGraph.deleteEdges_adj] at hab
      obtain ⟨hab₁, hab₂⟩ := hab
      rw [toSimpleGraph, SimpleGraph.fromRel_adj] at hab₁
      obtain ⟨g, hg⟩ : ∃ g, (G.source g = a ∧ G.target g = b) ∨
          (G.source g = b ∧ G.target g = a) := by
        rcases hab₁.2 with ⟨g, hs, ht⟩ | ⟨g, hs, ht⟩
        · exact ⟨g, Or.inl ⟨hs, ht⟩⟩
        · exact ⟨g, Or.inr ⟨hs, ht⟩⟩
      refine ⟨g, ?_, hg⟩
      rintro rfl
      apply hab₂
      rw [Set.mem_singleton_iff]
      rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first | rfl | exact Sym2.eq_swap
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcyc e hwalk
    · exact hcyc e (G.walks_symm hwalk)

/-- **Contracting the blobs of a connected graph gives a tree.** -/
theorem bridgeQuotient_isTree (hG : G.IsConnected) : G.bridgeQuotient.IsTree :=
  ⟨G.bridgeQuotient_connected hG, fun e =>
    (G.bridgeQuotient.isBridge_iff_not_walks_delete e).mp (G.bridgeQuotient_isBridge e)⟩

variable {G} in
/-- A bridge has a cut with its target on one side and its source on the other. -/
theorem exists_oriented_cut {e : E} (he : G.underlying.IsBridge e) :
    ∃ S : Set V, (∀ f, G.Crosses f S ↔ f = e) ∧ G.target e ∈ S ∧ G.source e ∉ S := by
  obtain ⟨S, hS⟩ := (G.isBridge_iff e).mp he
  rcases (hS e).mpr rfl with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · exact ⟨Sᶜ, fun f => (G.crosses_compl f S).trans (hS f), ht, not_not.mpr hs⟩
  · exact ⟨S, hS, ht, hs⟩

variable {G} in
/-- Directed paths do not leave the target side of a bridge. -/
theorem mem_of_reaches_of_cut {S : Set V} {e : E} (hS : ∀ f, G.Crosses f S ↔ f = e)
    (hs : G.source e ∉ S) {u w : V} (hr : G.Reaches u w) (hu : u ∈ S) : w ∈ S := by
  induction hr with
  | refl => exact hu
  | @tail a c _ hstep ih =>
    obtain ⟨f, rfl, rfl⟩ := hstep
    by_contra hc
    have hfe := (hS f).mp (Or.inl ⟨ih, hc⟩)
    exact hs (hfe ▸ ih)

variable {G} in
/-- A graph whose arcs are all bridges has no directed cycle. -/
theorem isAcyclic_of_forall_isBridge (h : ∀ e, G.underlying.IsBridge e) : G.IsAcyclic := by
  intro v hv
  obtain ⟨a, ⟨e, rfl, rfl⟩, hr⟩ := Relation.TransGen.head'_iff.mp hv
  obtain ⟨S, hS, ht, hs⟩ := exists_oriented_cut (h e)
  exact hs (mem_of_reaches_of_cut hS hs hr ht)

/-- Directed paths descend to the contraction of the blobs. -/
theorem bridgeQuotient_reaches {u w : V} (h : G.Reaches u w) :
    G.bridgeQuotient.Reaches (Quotient.mk G.blobSetoid u) (Quotient.mk G.blobSetoid w) := by
  induction h with
  | refl => exact .refl
  | @tail a c _ hstep ih =>
    obtain ⟨f, rfl, rfl⟩ := hstep
    by_cases hf : G.underlying.IsBridge f
    · exact ih.tail ⟨⟨f, hf⟩, rfl, rfl⟩
    · rwa [← G.quotient_eq_of_not_isBridge hf]

/-- A singleton cut does not separate two vertices of one blob. -/
theorem mem_iff_of_blobSetoid {S : Set V} {e : E} (hS : ∀ f, G.Crosses f S ↔ f = e) {a b : V}
    (h : Quotient.mk G.blobSetoid a = Quotient.mk G.blobSetoid b) : a ∈ S ↔ b ∈ S := by
  have he : G.underlying.IsBridge e := (G.isBridge_iff e).mpr ⟨S, hS⟩
  exact G.mem_iff_mem_of_walks (F := {f | ¬ G.underlying.IsBridge f})
    (fun f hf hc => hf ((hS f).mp hc ▸ he)) (Quotient.exact h)

end Phylogenetics.DirectedMultigraph
