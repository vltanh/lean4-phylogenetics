module

public import Phylogenetics.Graph.Basic

/-!
# Walks and bridges in directed multigraphs

Orientation is ignored for walks, but the allowed set of arcs retains the identity of the arcs, so
deleting one of two parallel arcs does not delete both.

## Main results

* `AdjOn`, `Walks`, `IsConnected`: undirected walks using allowed arcs.
* `mem_iff_mem_of_walks`: a cut that no allowed arc crosses does not separate the ends of a walk.
* `isBridge_iff_not_walks_delete`: Mathlib's bridges, defined through singleton cuts, are the arcs whose
  deletion separates their ends.
* `isAcyclic_of_rank`: strictly increasing vertex ranks exclude directed cycles.
-/

@[expose] public section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Undirected adjacency using an arc from the specified set. -/
def AdjOn (F : Set E) (u v : V) : Prop :=
  ∃ e ∈ F, (G.source e = u ∧ G.target e = v) ∨
    (G.source e = v ∧ G.target e = u)

/-- Undirected reachability, with empty walks permitted. -/
def Walks (F : Set E) : V → V → Prop := Relation.ReflTransGen (G.AdjOn F)

def IsConnected : Prop := ∀ u v, G.Walks Set.univ u v

theorem adjOn_symm {F : Set E} {u v : V} (h : G.AdjOn F u v) :
    G.AdjOn F v u := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.symm⟩

theorem walks_symm {F : Set E} {u v : V} (h : G.Walks F u v) :
    G.Walks F v u := by
  induction h with
  | refl => exact .refl
  | tail _ huv ih => exact ih.head (G.adjOn_symm huv)

theorem walks_trans {F : Set E} {u v w : V}
    (h : G.Walks F u v) (h' : G.Walks F v w) : G.Walks F u w :=
  h.trans h'

theorem walks_of_reaches {u v : V} (h : G.Reaches u v) :
    G.Walks Set.univ u v := by
  apply Relation.ReflTransGen.mono (r := G.Adj) (p := G.AdjOn Set.univ) _ _ _ h
  rintro a b ⟨e, hs, ht⟩
  exact ⟨e, Set.mem_univ e, Or.inl ⟨hs, ht⟩⟩

/-- A cut that no allowed arc crosses cannot separate endpoints of an allowed walk. -/
theorem mem_iff_mem_of_walks {F : Set E} {S : Set V}
    (hF : ∀ e ∈ F, ¬ G.Crosses e S) {u v : V} (h : G.Walks F u v) :
    u ∈ S ↔ v ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | @tail v w _ hvw ih =>
    obtain ⟨e, he, hlink⟩ := hvw
    have hn := hF e he
    have heq : G.source e ∈ S ↔ G.target e ∈ S := by
      unfold Crosses at hn
      tauto
    rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans heq
    · exact ih.trans heq.symm

/-- Mathlib's cut-defined bridge agrees with the usual edge-deletion criterion. -/
theorem isBridge_iff_not_walks_delete (e : E) :
    G.underlying.IsBridge e ↔ ¬ G.Walks {e}ᶜ (G.source e) (G.target e) := by
  rw [G.isBridge_iff]
  constructor
  · rintro ⟨S, hS⟩ hwalk
    have hsame := G.mem_iff_mem_of_walks (F := ({e}ᶜ : Set E)) (S := S) (fun f hf hcross =>
      hf ((hS f).mp hcross)) hwalk
    have hcross := (hS e).mpr rfl
    rcases hcross with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · exact ht (hsame.mp hs)
    · exact hs (hsame.mpr ht)
  · intro hnot
    let S : Set V := {v | G.Walks {e}ᶜ (G.source e) v}
    have hs : G.source e ∈ S := Relation.ReflTransGen.refl
    have ht : G.target e ∉ S := hnot
    refine ⟨S, ?_⟩
    intro f
    constructor
    · intro hcross
      by_contra hfe
      have hf : f ∈ ({e}ᶜ : Set E) := hfe
      have hlink : G.AdjOn {e}ᶜ (G.source f) (G.target f) :=
        ⟨f, hf, Or.inl ⟨rfl, rfl⟩⟩
      rcases hcross with ⟨hsf, htf⟩ | ⟨htf, hsf⟩
      · exact htf (Relation.ReflTransGen.tail hsf hlink)
      · exact hsf (Relation.ReflTransGen.tail htf (G.adjOn_symm hlink))
    · rintro rfl
      exact Or.inl ⟨hs, ht⟩

/-- Strictly increasing vertex ranks prohibit directed cycles. -/
theorem isAcyclic_of_rank (rank : V → ℕ)
    (hrank : ∀ e, rank (G.source e) < rank (G.target e)) : G.IsAcyclic := by
  have strict : ∀ {u v}, Relation.TransGen G.Adj u v → rank u < rank v := by
    intro u v h
    induction h using Relation.TransGen.trans_induction_on with
    | single h =>
      obtain ⟨e, rfl, rfl⟩ := h
      exact hrank e
    | trans _ _ ih ih' => exact lt_trans ih ih'
  intro v h
  exact lt_irrefl (rank v) (strict h)


/-- With finitely many arcs, zero outdegree means that no arc leaves the vertex. -/
theorem outdegree_eq_zero_iff [Finite E] (v : V) :
    G.outdegree v = 0 ↔ ∀ e, G.source e ≠ v := by
  rw [outdegree, Set.ncard_eq_zero]
  exact Set.eq_empty_iff_forall_notMem

/-- A vertex with no outgoing arc reaches only itself. -/
theorem eq_of_reaches_of_outdegree_eq_zero [Finite E] {u v : V}
    (h : G.Reaches u v) (hu : G.outdegree u = 0) : v = u := by
  apply (Relation.reflTransGen_iff_eq (r := G.Adj) (a := u) ?_).mp h
  rintro w ⟨e, he, _⟩
  exact (G.outdegree_eq_zero_iff u).mp hu e he


end Phylogenetics.DirectedMultigraph
