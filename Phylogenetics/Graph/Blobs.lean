module

public import Phylogenetics.Graph.Connectivity

/-!
# Contraction of the components remaining after deleting the bridges

The quotient is constructed from walks of the graph. Its vertices are the components obtained by deleting
every bridge, and its arcs are the bridges of the graph. `Phylogenetics.Graph.Tree` proves that these
components are the blobs and that a connected graph gives a tree.

## Main results

* `blobSetoid`, `BlobVertex`, `BridgeArc`, `bridgeQuotient`: the quotient.
* `bridgeQuotient_connected`, `bridgeQuotient_isBridge`: it stays connected, and bridges stay bridges.
* `labelled_cut_iff_quotient`: it has the same labelled singleton cuts.
-/

@[expose] public section

namespace Phylogenetics.DirectedMultigraph

variable {V E : Type*} (G : DirectedMultigraph V E)

/-- Vertices joined without using a bridge are identified in the contraction. -/
def blobSetoid : Setoid V where
  r := G.Walks {e | ¬ G.underlying.IsBridge e}
  iseqv := ⟨fun _ => .refl, fun h => G.walks_symm h, fun h h' => h.trans h'⟩

/-- Components remaining when all bridge arcs are deleted. -/
abbrev BlobVertex := Quotient G.blobSetoid

/-- Arcs retained by the component contraction. -/
abbrev BridgeArc := {e : E // G.underlying.IsBridge e}

def bridgeQuotient : DirectedMultigraph G.BlobVertex G.BridgeArc where
  source e := Quotient.mk G.blobSetoid (G.source e.val)
  target e := Quotient.mk G.blobSetoid (G.target e.val)

/-- A nonbridge arc is contracted to a single quotient vertex. -/
theorem quotient_eq_of_not_isBridge {e : E} (he : ¬ G.underlying.IsBridge e) :
    Quotient.mk G.blobSetoid (G.source e) =
      Quotient.mk G.blobSetoid (G.target e) := by
  apply Quotient.sound
  exact Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- Every undirected adjacency maps to a walk, possibly empty, in the contraction. -/
theorem quotient_walks_of_adj {u v : V} (h : G.AdjOn Set.univ u v) :
    G.bridgeQuotient.Walks Set.univ (Quotient.mk G.blobSetoid u)
      (Quotient.mk G.blobSetoid v) := by
  obtain ⟨e, _, h⟩ := h
  by_cases he : G.underlying.IsBridge e
  · apply Relation.ReflTransGen.single
    exact ⟨⟨e, he⟩, Set.mem_univ _, by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩⟩
  · have heq := G.quotient_eq_of_not_isBridge he
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [heq]
      exact .refl
    · rw [heq]
      exact .refl

/-- A connected graph stays connected after contracting all nonbridge arcs. -/
theorem bridgeQuotient_connected (hG : G.IsConnected) :
    G.bridgeQuotient.IsConnected := by
  intro u v
  induction u using Quotient.inductionOn with
  | h u =>
    induction v using Quotient.inductionOn with
    | h v =>
      exact Relation.ReflTransGen.lift' (Quotient.mk G.blobSetoid)
        (fun _ _ h => G.quotient_walks_of_adj h) _ _ (hG u v)

/-- Each retained original bridge is still a bridge in the quotient. -/
theorem bridgeQuotient_isBridge (e : G.BridgeArc) :
    G.bridgeQuotient.underlying.IsBridge e := by
  classical
  obtain ⟨S, hS⟩ := (G.isBridge_iff e.val).mp e.property
  have hstable : ∀ a b, G.blobSetoid.r a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    apply G.mem_iff_mem_of_walks (F := {f | ¬ G.underlying.IsBridge f}) _ h
    intro f hf hcross
    have hfe := (hS f).mp hcross
    exact hf (hfe ▸ e.property)
  let inCut : G.BlobVertex → Prop := Quotient.lift (fun v => v ∈ S)
    (fun a b h => propext (hstable a b h))
  apply (G.bridgeQuotient.isBridge_iff e).mpr
  refine ⟨{v | inCut v}, ?_⟩
  intro f
  change G.Crosses f.val S ↔ f = e
  rw [hS f.val, Subtype.ext_iff]

/-- Every singleton cut is constant on each contracted component. -/
theorem exists_quotient_set_of_singleton_cut (e : E) (S : Set V)
    (hS : ∀ f, G.Crosses f S ↔ f = e) :
    ∃ T : Set G.BlobVertex, (Quotient.mk G.blobSetoid) ⁻¹' T = S := by
  have he : G.underlying.IsBridge e := (G.isBridge_iff e).mpr ⟨S, hS⟩
  have hstable : ∀ a b, G.blobSetoid.r a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    apply G.mem_iff_mem_of_walks (F := {f | ¬ G.underlying.IsBridge f}) _ h
    intro f hf hcross
    exact hf ((hS f).mp hcross ▸ he)
  let inCut : G.BlobVertex → Prop := Quotient.lift (fun v => v ∈ S)
    (fun a b h => propext (hstable a b h))
  exact ⟨{v | inCut v}, rfl⟩

/-- Pullback preserves singleton cuts exactly, including their arc identities. -/
theorem singleton_cut_preimage_iff (e : G.BridgeArc) (T : Set G.BlobVertex) :
    (∀ f, G.Crosses f ((Quotient.mk G.blobSetoid) ⁻¹' T) ↔ f = e.val) ↔
      ∀ f, G.bridgeQuotient.Crosses f T ↔ f = e := by
  constructor
  · intro h f
    change G.Crosses f.val ((Quotient.mk G.blobSetoid) ⁻¹' T) ↔ f = e
    rw [h f.val, Subtype.ext_iff]
  · intro h f
    by_cases hf : G.underlying.IsBridge f
    · have hh := h ⟨f, hf⟩
      change G.Crosses f ((Quotient.mk G.blobSetoid) ⁻¹' T) ↔
        (⟨f, hf⟩ : G.BridgeArc) = e at hh
      simpa only [Subtype.ext_iff] using hh
    · have heq := G.quotient_eq_of_not_isBridge hf
      have hne : f ≠ e.val := fun hfe => hf (hfe ▸ e.property)
      simp only [Crosses, Set.mem_preimage, heq, and_not_self, or_self,
        false_iff]
      exact hne

/-- Contraction preserves the labelled splits carried by singleton cuts.
No assumption about labels, connectivity or finiteness is required. -/
theorem labelled_cut_iff_quotient {X : Type*} (label : X → V) (A : Set X) :
    (∃ (e : E) (S : Set V), (∀ f, G.Crosses f S ↔ f = e) ∧ label ⁻¹' S = A) ↔
      ∃ (e : G.BridgeArc) (T : Set G.BlobVertex),
        (∀ f, G.bridgeQuotient.Crosses f T ↔ f = e) ∧
          (fun x => Quotient.mk G.blobSetoid (label x)) ⁻¹' T = A := by
  constructor
  · rintro ⟨e, S, hS, hA⟩
    have he := (G.isBridge_iff e).mpr ⟨S, hS⟩
    obtain ⟨T, hT⟩ := G.exists_quotient_set_of_singleton_cut e S hS
    refine ⟨⟨e, he⟩, T, ?_, ?_⟩
    · apply (G.singleton_cut_preimage_iff ⟨e, he⟩ T).mp
      simpa only [hT] using hS
    · change label ⁻¹' ((Quotient.mk G.blobSetoid) ⁻¹' T) = A
      rw [hT, hA]
  · rintro ⟨e, T, hT, hA⟩
    exact ⟨e.val, (Quotient.mk G.blobSetoid) ⁻¹' T,
      (G.singleton_cut_preimage_iff e T).mpr hT, hA⟩

end Phylogenetics.DirectedMultigraph

