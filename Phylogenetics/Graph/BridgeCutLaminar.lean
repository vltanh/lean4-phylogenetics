module

public import Phylogenetics.Graph.CutUniqueness

/-!
# Connected sides of singleton cuts, and laminarity

A side of a singleton cut is exactly a connected component after deleting its unique crossing arc. In a
connected graph, the sides of singleton cuts that avoid a fixed vertex form a laminar family. No
finiteness hypothesis is needed.

## Main results

* `singletonCut_side_eq_walk_component`, `singletonCut_side_walks`: the sides are components.
* `singletonCut_laminar`: the sides avoiding a vertex are laminar.
-/

@[expose] public section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Complementing a vertex cut preserves which arcs cross it. -/
theorem crosses_compl (e : E) (S : Set V) : G.Crosses e Sᶜ ↔ G.Crosses e S := by
  simp only [Crosses, Set.mem_compl_iff, not_not]
  tauto

/-- No allowed arc crosses a component defined by allowed walks. -/
theorem not_crosses_walk_component (F : Set E) (u : V) {e : E} (he : e ∈ F) :
    ¬ G.Crosses e {v | G.Walks F u v} := by
  rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
  · exact ht (hs.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
  · exact hs (ht.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩)

/-- A side of a singleton cut is the component of any of its vertices after
removing that particular crossing arc. -/
theorem singletonCut_side_eq_walk_component (hG : G.IsConnected) (e : E) {S : Set V}
    (hS : ∀ f, G.Crosses f S ↔ f = e) {u : V} (hu : u ∈ S) :
    S = {v | G.Walks {e}ᶜ u v} := by
  classical
  let C : Set V := {v | G.Walks {e}ᶜ u v}
  have huC : u ∈ C := Relation.ReflTransGen.refl
  have hCsub : C ⊆ S := by
    intro v hv
    exact (G.mem_iff_mem_of_walks (F := ({e}ᶜ : Set E))
      (fun f hf hcross => hf ((hS f).mp hcross)) hv).mp hu
  obtain ⟨w, hw⟩ : ∃ w, w ∉ S := by
    rcases (hS e).mpr rfl with ⟨_, ht⟩ | ⟨_, hs⟩
    · exact ⟨G.target e, ht⟩
    · exact ⟨G.source e, hs⟩
  have heC : G.Crosses e C := by
    by_contra hnot
    have hnone : ∀ f ∈ (Set.univ : Set E), ¬ G.Crosses f C := by
      intro f _
      by_cases hfe : f = e
      · simpa only [hfe] using hnot
      · exact G.not_crosses_walk_component {e}ᶜ u hfe
    have hwC := (G.mem_iff_mem_of_walks hnone (hG u w)).mp huC
    exact hw (hCsub hwC)
  have hCcut : ∀ f, G.Crosses f C ↔ f = e := by
    intro f
    constructor
    · intro hcross
      by_contra hfe
      exact G.not_crosses_walk_component {e}ᶜ u hfe hcross
    · rintro rfl
      exact heC
  rcases G.singleton_cuts_eq_or_eq_compl hG e hS hCcut with heq | heq
  · exact heq
  · have huNotC : u ∉ C := by simpa only [heq, Set.mem_compl_iff] using hu
    exact False.elim (huNotC huC)

/-- Each side of a singleton cut is connected by walks avoiding the crossing arc. -/
theorem singletonCut_side_walks (hG : G.IsConnected) (e : E) {S : Set V}
    (hS : ∀ f, G.Crosses f S ↔ f = e) {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    G.Walks {e}ᶜ u v := by
  rw [G.singletonCut_side_eq_walk_component hG e hS hu] at hv
  exact hv

/-- A walk confined by a noncrossing cut cannot use an arc with both endpoints
outside that cut side. -/
theorem walks_avoid_of_endpoints_not_mem {F : Set E} {S : Set V} {e : E}
    (hF : ∀ f ∈ F, ¬ G.Crosses f S)
    (hs : G.source e ∉ S) (ht : G.target e ∉ S)
    {u v : V} (hu : u ∈ S) (h : G.Walks F u v) : G.Walks {e}ᶜ u v := by
  induction h with
  | refl => exact .refl
  | @tail v w hprefix hstep ih =>
    have hv : v ∈ S := (G.mem_iff_mem_of_walks hF hprefix).mp hu
    obtain ⟨f, _, hlink⟩ := hstep
    have hfe : f ≠ e := by
      intro heq
      subst f
      rcases hlink with ⟨hsrc, _⟩ | ⟨_, htgt⟩
      · exact hs (hsrc ▸ hv)
      · exact ht (htgt ▸ hv)
    exact ih.tail ⟨f, hfe, hlink⟩

/-- A side of one singleton cut can be traversed while avoiding an arc wholly
outside that side. -/
theorem singletonCut_side_walks_avoiding (hG : G.IsConnected) (e f : E) {S : Set V}
    (hS : ∀ g, G.Crosses g S ↔ g = e)
    (hs : G.source f ∉ S) (ht : G.target f ∉ S)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) : G.Walks {f}ᶜ u v :=
  G.walks_avoid_of_endpoints_not_mem (F := ({e}ᶜ : Set E)) (fun g hg hcross => hg ((hS g).mp hcross)) hs ht hu
    (G.singletonCut_side_walks hG e hS hu hv)

/-- In a connected graph, singleton-cut sides avoiding one fixed vertex are laminar. -/
theorem singletonCut_laminar (hG : G.IsConnected) (r : V) (e f : E) {S T : Set V}
    (hS : ∀ g, G.Crosses g S ↔ g = e)
    (hT : ∀ g, G.Crosses g T ↔ g = f)
    (hrS : r ∉ S) (hrT : r ∉ T) : S ⊆ T ∨ T ⊆ S ∨ Disjoint S T := by
  classical
  by_cases hef : e = f
  · subst f
    rcases G.singleton_cuts_eq_or_eq_compl hG e hS hT with heq | heq
    · exact Or.inl heq.subset
    · have hr : r ∈ S := by simpa only [heq, Set.mem_compl_iff] using hrT
      exact False.elim (hrS hr)
  have hfnot : ¬ G.Crosses f S := fun hcross => hef ((hS f).mp hcross).symm
  by_cases hsrc : G.source f ∈ S
  · have htgt : G.target f ∈ S := by
      by_contra h
      exact hfnot (Or.inl ⟨hsrc, h⟩)
    right
    left
    intro v hvT
    by_contra hvS
    have hScomp : ∀ g, G.Crosses g Sᶜ ↔ g = e :=
      fun g => (G.crosses_compl g S).trans (hS g)
    have hwalk := G.singletonCut_side_walks_avoiding hG e f hScomp
      (by simpa only [Set.mem_compl_iff, not_not] using hsrc)
      (by simpa only [Set.mem_compl_iff, not_not] using htgt) hrS hvS
    have hsame := G.mem_iff_mem_of_walks (F := ({f}ᶜ : Set E))
      (fun g hg hcross => hg ((hT g).mp hcross)) hwalk
    exact hrT (hsame.mpr hvT)
  · have htgt : G.target f ∉ S := fun h => hfnot (Or.inr ⟨h, hsrc⟩)
    by_cases hmeet : ∃ u, u ∈ S ∧ u ∈ T
    · obtain ⟨u, huS, huT⟩ := hmeet
      left
      intro v hvS
      have hwalk := G.singletonCut_side_walks_avoiding hG e f hS hsrc htgt huS hvS
      exact (G.mem_iff_mem_of_walks (F := ({f}ᶜ : Set E))
        (fun g hg hcross => hg ((hT g).mp hcross)) hwalk).mp huT
    · right
      right
      exact Set.disjoint_left.mpr (fun u huS huT => hmeet ⟨u, huS, huT⟩)

end Phylogenetics.DirectedMultigraph
