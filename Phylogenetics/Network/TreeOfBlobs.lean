module

public import Phylogenetics.Graph.Tree
public import Phylogenetics.Network.CutHierarchy
public import Phylogenetics.Network.Induced

/-!
# The tree of blobs of a rooted network

`treeOfBlobs N` (`Phylogenetics.Network.Quartets`) is a family of taxon sets: the nonempty proper taxon
sides of the cut edges of `N`. This module proves that it is the split family of the tree of blobs of
Allman, Baños, Mitchell, Rhodes (2024, Definitions 1–3), built from the graph.

* `isBlob_iff`: the classes of `blobSetoid` are exactly the vertex sets of the blobs, the maximal
  connected subgraphs without cut edges (Definition 1).
* `bridgeQuotient_isTree`, `IsTree.toSimpleGraph_isTree`: contracting the blobs gives a tree
  (Definition 2). `hasCutSplit_iff_bridgeQuotient` (`Phylogenetics.Network.Basic`): with the same labelled cuts.
* `bridgeQuotientData_isPhylogenetic`: oriented away from the root, this tree obeys the laws of a
  rooted network.
* `blobTree`, `blobTree_isTree`, `blobTree_hasCutSplit_iff`: suppressing its vertices of indegree
  and outdegree one (Definition 3) gives a tree with the same labelled cuts.
* `side_eq_of_stem`, `arc_pair_of_root`, `suppress_degree_two_eq_root`: the only vertex of degree
  two or unlabelled of degree one left is the root, and its arcs add no further nontrivial split.
  The operation deleting this root is not constructed.
* `mem_treeOfBlobs_iff_blobTree`, `isUnrootedTree_treeOfBlobs`,
  `hierarchyNetwork_hasCutSplit_iff_mem_treeOfBlobs`, `mem_treeOfBlobs_iff_inducedNetwork`:
  conclusions for `treeOfBlobs N`.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *TINNiK: inference of the tree of blobs of a
  species network under the coalescent model*, Algorithms Mol. Biol. 19 (2024), 23.
-/

@[expose] public noncomputable section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### The tree of blobs, oriented away from the root -/

/-- The blob of a taxon is the taxon's vertex alone. -/
theorem eq_leaf_of_quotient_eq (hN : N.IsPhylogenetic) {x : X} {v : V}
    (h : Quotient.mk N.graph.blobSetoid v = Quotient.mk N.graph.blobSetoid (N.leaf x)) :
    v = N.leaf x := by
  have : Finite E := hN.finite_arcs
  obtain ⟨e, he⟩ := N.graph.exists_singleton_vertex_cut (hN.leaf_indegree x)
    ((hN.leaves _).mpr ⟨x, rfl⟩)
  exact (N.graph.mem_iff_of_blobSetoid he h).mpr rfl

/-- **The contraction of the blobs of a network obeys the laws of a rooted network**: it is a tree,
oriented away from the blob of the root. -/
theorem bridgeQuotientData_isPhylogenetic (hN : N.IsPhylogenetic) :
    N.bridgeQuotientData.IsPhylogenetic := by
  have : Finite V := hN.finite_vertices
  have : Finite E := hN.finite_arcs
  have hroot : ∀ v, N.bridgeQuotientData.graph.Reaches N.bridgeQuotientData.root v := by
    intro v
    induction v using Quotient.inductionOn with
    | h v => exact N.graph.bridgeQuotient_reaches (hN.root_reaches v)
  refine ⟨Quotient.finite _, inferInstance, hN.finite_taxa, ?_, hroot, ?_, ?_, ?_, ?_, ?_⟩
  · exact DirectedMultigraph.isAcyclic_of_forall_isBridge N.graph.bridgeQuotient_isBridge
  · rw [DirectedMultigraph.indegree_eq_zero_iff]
    intro e he
    obtain ⟨S, hS, ht, hs⟩ := DirectedMultigraph.exists_oriented_cut e.2
    have hr : N.root ∈ S := (N.graph.mem_iff_of_blobSetoid hS he).mp ht
    exact hs (DirectedMultigraph.mem_of_reaches_of_cut hS hs (hN.root_reaches _) hr)
  · intro v hv
    rw [DirectedMultigraph.one_le_indegree_iff]
    rcases Relation.ReflTransGen.cases_tail (hroot v) with h | ⟨a, -, e, -, he⟩
    · exact absurd h hv
    · exact ⟨e, he⟩
  · intro x y h
    exact hN.leaf_injective (eq_leaf_of_quotient_eq hN h).symm |>.symm
  · intro x
    obtain ⟨g, hg⟩ := (N.graph.indegree_eq_one_iff _).mp (hN.leaf_indegree x)
    have hb : N.graph.underlying.IsBridge g := by
      obtain ⟨e, he⟩ := N.graph.exists_singleton_vertex_cut (hN.leaf_indegree x)
        ((hN.leaves _).mpr ⟨x, rfl⟩)
      have hc : N.graph.Crosses g {N.leaf x} :=
        Or.inr ⟨(hg g).mpr rfl, fun h => hN.acyclic _ (Relation.TransGen.single
          ⟨g, h.trans ((hg g).mpr rfl).symm, rfl⟩)⟩
      exact (N.graph.isBridge_iff g).mpr ⟨{N.leaf x}, fun f => by rw [he f, (he g).mp hc]⟩
    refine (DirectedMultigraph.indegree_eq_one_iff _ _).mpr ⟨⟨g, hb⟩, fun f => ⟨fun hf => ?_, ?_⟩⟩
    · exact Subtype.ext ((hg f.1).mp (eq_leaf_of_quotient_eq hN hf))
    · rintro rfl
      exact congrArg (Quotient.mk N.graph.blobSetoid) ((hg g).mpr rfl)
  · intro q
    rw [DirectedMultigraph.outdegree_eq_zero_iff]
    induction q using Quotient.inductionOn with
    | h v =>
      constructor
      · intro h
        obtain ⟨x, hx⟩ := exists_reaches_leaf hN v
        refine ⟨x, ?_⟩
        have hall : ∀ w, N.graph.Reaches v w →
            Quotient.mk N.graph.blobSetoid w = Quotient.mk N.graph.blobSetoid v := by
          intro w hw
          induction hw with
          | refl => rfl
          | @tail a c _ hstep ih =>
            obtain ⟨f, rfl, rfl⟩ := hstep
            have hf : ¬ N.graph.underlying.IsBridge f := fun hb => h ⟨f, hb⟩ ih
            rw [← N.graph.quotient_eq_of_not_isBridge hf, ih]
        exact hall _ hx
      · rintro ⟨x, hx⟩ e he
        have heq : N.graph.source e.1 = N.leaf x := eq_leaf_of_quotient_eq hN (he.trans hx.symm)
        have hz := (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves (N.leaf x)).mpr ⟨x, rfl⟩)
        exact hz e.1 heq

/-- Suppression keeps the bridges. -/
theorem suppress_isBridge (hN : N.IsPhylogenetic) (e : {e // ¬ N.IsChainVertex (N.graph.source e)})
    (he : N.graph.underlying.IsBridge e.1) : (N.suppress hN).graph.underlying.IsBridge e := by
  obtain ⟨S, hS⟩ := (N.graph.isBridge_iff e.1).mp he
  refine ((N.suppress hN).graph.isBridge_iff e).mpr ⟨Subtype.val ⁻¹' S, fun g => ?_⟩
  refine (crosses_chain_iff hN hS (f := g.1)).trans ⟨fun h => ?_, ?_⟩
  · exact Subtype.ext (h.unique (Or.inl rfl) g.2 e.2)
  · rintro rfl
    exact Or.inl rfl

/-- **The tree of blobs, oriented away from the root**: contract the blobs of the network and
suppress the vertices of indegree one and outdegree one (Definitions 2 and 3 of Allman, Baños, Mitchell, Rhodes 2024). The root may
remain with degree one or two, with the same nontrivial splits (`side_eq_of_stem`,
`arc_pair_of_root`); all other vertices have degree other than two (`suppress_degree_two_eq_root`).
-/
def blobTree (N : RootedNetwork V E X) (hN : N.IsPhylogenetic) :=
  N.bridgeQuotientData.suppress (bridgeQuotientData_isPhylogenetic hN)

theorem blobTree_isPhylogenetic (hN : N.IsPhylogenetic) : (N.blobTree hN).IsPhylogenetic :=
  suppress_isPhylogenetic _

/-- **The tree of blobs is a tree.** -/
theorem blobTree_isTree (hN : N.IsPhylogenetic) : (N.blobTree hN).graph.IsTree := by
  refine ⟨(N.blobTree hN).graph_connected (blobTree_isPhylogenetic hN), fun e => ?_⟩
  exact ((N.blobTree hN).graph.isBridge_iff_not_walks_delete e).mp
    (suppress_isBridge _ e (N.graph.bridgeQuotient_isBridge e.1))

/-- The tree of blobs is a tree in the sense of Mathlib. -/
theorem blobTree_toSimpleGraph_isTree (hN : N.IsPhylogenetic) :
    (N.blobTree hN).graph.toSimpleGraph.IsTree :=
  have : Nonempty _ := ⟨(N.blobTree hN).root⟩
  (blobTree_isTree hN).toSimpleGraph_isTree

/-- **The labelled cuts of the tree of blobs are those of the network.** -/
theorem blobTree_hasCutSplit_iff (hN : N.IsPhylogenetic) (A : Set X) :
    (N.blobTree hN).HasCutSplit A ↔ N.HasCutSplit A :=
  (suppress_hasCutSplit_iff (bridgeQuotientData_isPhylogenetic hN) A).trans
    (N.hasCutSplit_iff_bridgeQuotient A).symm

/-- A stem, the only arc leaving the root, has a trivial split, which `treeOfBlobs` excludes. -/
theorem side_eq_of_stem (hN : N.IsPhylogenetic) {e : E}
    (hroot : ∀ f, N.graph.source f = N.root ↔ f = e) {S : Set V}
    (hS : ∀ f, N.graph.Crosses f S ↔ f = e) : N.leaf ⁻¹' S = ∅ ∨ N.leaf ⁻¹' S = Set.univ := by
  have hA := hN.acyclic
  -- every vertex other than the root is below `e`
  have hbelow : ∀ v, v ≠ N.root → N.graph.Reaches (N.graph.target e) v := by
    intro v hv
    rcases Relation.ReflTransGen.cases_head (hN.root_reaches v) with h | ⟨a, ⟨f, hs, rfl⟩, hav⟩
    · exact absurd h.symm hv
    · rwa [(hroot f).mp hs] at hav
  have hleaf : ∀ x y, N.leaf x ∈ S ↔ N.leaf y ∈ S := fun x y => by
    have h : ∀ z, N.graph.target e ∈ S ↔ N.leaf z ∈ S := fun z =>
      mem_iff_mem_of_avoidingReach_of_cut hS
        (avoidingReach_of_target_reaches hA .refl (hbelow _ (N.leaf_ne_root hN z)))
    exact (h x).symm.trans (h y)
  by_cases hx : ∃ x, N.leaf x ∈ S
  · obtain ⟨x, hx⟩ := hx
    exact Or.inr (Set.eq_univ_of_forall fun y => (hleaf x y).mp hx)
  · exact Or.inl (Set.eq_empty_of_forall_notMem fun y hy => hx ⟨y, hy⟩)

/-- The two arcs at a root of outdegree two give the same split: suppressing such a root, which
merges the two, does not change the splits. -/
theorem arc_pair_of_root (hN : N.IsPhylogenetic) {e₁ e₂ : E} (hne : e₁ ≠ e₂)
    (hroot : ∀ f, N.graph.source f = N.root ↔ f = e₁ ∨ f = e₂) {S : Set V}
    (hS : ∀ f, N.graph.Crosses f S ↔ f = e₁) :
    ∃ S' : Set V, (∀ f, N.graph.Crosses f S' ↔ f = e₂) ∧ N.leaf ⁻¹' S' = N.leaf ⁻¹' S := by
  have : Finite E := hN.finite_arcs
  have hin : ∀ f, N.graph.target f ≠ N.root :=
    (N.graph.indegree_eq_zero_iff _).mp hN.root_indegree
  -- `S'` is `S` with the root moved across
  let S' : Set V := {v | v ∈ S ↔ v ≠ N.root}
  have hmem : ∀ v, v ≠ N.root → (v ∈ S' ↔ v ∈ S) := fun v hv => by
    simp only [S', Set.mem_ofPred_eq, hv, ne_eq, not_false_eq_true, iff_true]
  have hr : N.root ∈ S' ↔ N.root ∉ S := by
    simp only [S', Set.mem_ofPred_eq, ne_eq, not_true_eq_false, iff_false]
  refine ⟨S', fun f => ?_, Set.ext fun x => hmem _ (N.leaf_ne_root hN x)⟩
  by_cases hfr : N.graph.source f = N.root
  · have hf := (hroot f).mp hfr
    have hc := hS f
    have hiff : f = e₂ ↔ ¬ f = e₁ :=
      ⟨by rintro rfl; exact hne.symm, fun h => hf.resolve_left h⟩
    simp only [DirectedMultigraph.Crosses, hfr] at hc ⊢
    rw [hr, hmem _ (hin f), hiff, ← hc]
    tauto
  · have he₁ : f ≠ e₁ := fun h => hfr ((hroot f).mpr (Or.inl h))
    have he₂ : f ≠ e₂ := fun h => hfr ((hroot f).mpr (Or.inr h))
    have hc := hS f
    simp only [DirectedMultigraph.Crosses] at hc ⊢
    rw [hmem _ hfr, hmem _ (hin f), hc]
    exact ⟨fun h => absurd h he₁, fun h => absurd h he₂⟩

section Family

variable [Fintype X] [DecidableEq X]

theorem mem_treeOfBlobs_iff (A : Finset X) :
    A ∈ treeOfBlobs N ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X) := by
  simp only [treeOfBlobs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **`treeOfBlobs N` is the family of the nonempty proper sides of the splits of the tree of
blobs.** -/
theorem mem_treeOfBlobs_iff_blobTree (hN : N.IsPhylogenetic) (A : Finset X) :
    A ∈ treeOfBlobs N ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ (N.blobTree hN).HasCutSplit (A : Set X) := by
  rw [mem_treeOfBlobs_iff, blobTree_hasCutSplit_iff]

/-- The tree of blobs of `N`, computed from what lies below the LSA of the taxa with degree-two
vertices suppressed, has the same splits: `treeOfBlobs` does not see the part above the LSA. -/
theorem mem_treeOfBlobs_iff_inducedNetwork (hN : N.IsPhylogenetic)
    (hX : (Set.univ : Set X).Nontrivial) (A : Finset X) :
    A ∈ treeOfBlobs N ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧
      (inducedNetwork hN Set.univ hX).HasCutSplit (Subtype.val ⁻¹' (A : Set X)) := by
  rw [mem_treeOfBlobs_iff]
  refine and_congr_right fun h₁ => and_congr_right fun h₂ => ?_
  rw [hasCutSplit_iff_hasCutSplitOn_univ hN]
  refine hasCutSplitOn_iff_inducedNetwork_hasCutSplit hN hX ?_ ?_
  · obtain ⟨x, hx⟩ := h₁
    exact ⟨x, Set.mem_univ x, hx⟩
  · obtain ⟨x, hx⟩ := h₂
    exact ⟨x, Set.mem_univ x, by simpa using hx⟩

/-- `treeOfBlobs N` is the split family of the concrete tree `cutHierarchy`, rooted at an outgroup.
-/
theorem unroot_cutHierarchy_eq_treeOfBlobs (hN : N.IsPhylogenetic) (r : X) :
    unroot (N.cutHierarchy r) = treeOfBlobs N := by
  ext A
  rw [N.mem_unroot_cutHierarchy hN r A, mem_treeOfBlobs_iff]

/-- **`treeOfBlobs N` is an unrooted tree.** -/
theorem isUnrootedTree_treeOfBlobs (hN : N.IsPhylogenetic) : IsUnrootedTree (treeOfBlobs N) := by
  obtain ⟨r, -⟩ := exists_reaches_leaf hN N.root
  exact ⟨N.cutHierarchy r, N.cutHierarchy_isHierarchy hN r, unroot_cutHierarchy_eq_treeOfBlobs hN r⟩

/-- The concrete tree of `cutHierarchy` has exactly the cut sides in `treeOfBlobs N`. -/
theorem hierarchyNetwork_hasCutSplit_iff_mem_treeOfBlobs (hN : N.IsPhylogenetic) (r : X)
    (A : Finset X) :
    (hierarchyNetwork (N.cutHierarchy r)
      (N.cutHierarchy_isHierarchy hN r)).HasCutSplit (A : Set X) ↔ A ∈ treeOfBlobs N := by
  rw [N.cutHierarchy_graph_cuts hN r A, mem_treeOfBlobs_iff]

end Family

end Phylogenetics.RootedNetwork
