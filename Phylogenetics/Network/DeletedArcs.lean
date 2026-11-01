module

public import Phylogenetics.Network.Cuts
public import Phylogenetics.Network.Quartets
public import Phylogenetics.Graph.Degree
public import Phylogenetics.Network.Cuts

/-!
# Networks with hybrid arcs deleted

An inheritance probability `0` effectively deletes a hybrid arc, a device of Allman, Baños, Mitchell, Rhodes (2023). So
this module keeps the network and its vertices, and
reads reachability, domination and cut splits off a set `D` of deleted arcs. For `D = ∅` these are the
notions of `Phylogenetics.Network.Cuts` (`reachesOff_empty_iff`, `dominatesOff_empty_iff`,
`isBelowOff_empty_iff`).

The path lemmas say how a path off `D` behaves when one more arc is deleted
(`ReachesOff.insert_of_not_reaches`, `ReachesOff.insert_of_target_reaches`, `ReachesOff.split`,
`reachesOff_insert_or`), and how domination and being below combine over the two ways of deleting one
of two arcs with a common target (`dominatesOff_of_insert_of_insert`,
`not_isBelowOff_of_insert_of_insert`). `IsTreelikeOff` is `IsTreelike` off `D`.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
-/

@[expose] public section

open Finset

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X) (D : Set E)

/-- `u` reaches `v` along arcs outside `D`. -/
def ReachesOff : V → V → Prop :=
  Relation.ReflTransGen fun a b => ∃ f, f ∉ D ∧ N.graph.source f = a ∧ N.graph.target f = b

/-- With the arcs `D` deleted, every directed path from the root to the taxon `x` uses the arc `e`. -/
def DominatesOff (e : E) (x : X) : Prop := ¬ N.ReachesOff (insert e D) N.root (N.leaf x)

/-- With the arcs `D` deleted, the taxon `x` is below the arc `e`. -/
def IsBelowOff (e : E) (x : X) : Prop := e ∉ D ∧ N.ReachesOff D (N.graph.target e) (N.leaf x)

/-- With the arcs `D` deleted, the arc `e` dominates all taxa of `P`, and no taxon of `Q` is below it. -/
def SeparatesOff (e : E) (P Q : Set X) : Prop :=
  (∀ x ∈ P, N.DominatesOff D e x) ∧ ∀ x ∈ Q, ¬ N.IsBelowOff D e x

/-- `D` deletes only hybrid arcs, and leaves every non-root vertex a parent. Then every vertex is
still reached from the root. -/
structure IsDeletion : Prop where
  hybrid : ∀ e ∈ D, N.IsHybridArc e
  parent : ∀ v, v ≠ N.root → ∃ f, f ∉ D ∧ N.graph.target f = v

section Paths

variable {N D}

/-- Deleting more arcs leaves fewer paths. -/
theorem ReachesOff.mono {D' : Set E} (h : D' ⊆ D) {u v : V} (huv : N.ReachesOff D u v) :
    N.ReachesOff D' u v :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, fun hf' => hf (h hf'), hs, ht⟩) _ _ huv

/-- A path off `D` is a path. -/
theorem ReachesOff.reaches {u v : V} (h : N.ReachesOff D u v) : N.graph.Reaches u v :=
  Relation.ReflTransGen.mono (fun _ _ ⟨f, _, hs, ht⟩ => ⟨f, hs, ht⟩) _ _ h

/-- Paths off `D` compose. -/
theorem ReachesOff.trans {u v w : V} (h : N.ReachesOff D u v) (h' : N.ReachesOff D v w) :
    N.ReachesOff D u w :=
  Relation.ReflTransGen.trans h h'

/-- Extend a path off `D` by an arc at its end. -/
theorem ReachesOff.tail_arc {u : V} {f : E} (h : N.ReachesOff D u (N.graph.source f)) (hf : f ∉ D) :
    N.ReachesOff D u (N.graph.target f) :=
  Relation.ReflTransGen.tail h ⟨f, hf, rfl, rfl⟩

/-- Extend a path off `D` by an arc at its start. -/
theorem ReachesOff.head_arc {v : V} {f : E} (hf : f ∉ D) (h : N.ReachesOff D (N.graph.target f) v) :
    N.ReachesOff D (N.graph.source f) v :=
  Relation.ReflTransGen.head ⟨f, hf, rfl, rfl⟩ h

/-- A nonempty path off `D` has a first arc. -/
theorem ReachesOff.exists_first {u v : V} (h : N.ReachesOff D u v) (hne : u ≠ v) :
    ∃ f, f ∉ D ∧ N.graph.source f = u ∧ N.ReachesOff D (N.graph.target f) v := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨f, hf, hs, rfl⟩, hc⟩
  · exact absurd rfl hne
  · exact ⟨f, hf, hs, hc⟩

/-- A nonempty path off `D` has a last arc. -/
theorem ReachesOff.exists_last {u v : V} (h : N.ReachesOff D u v) (hne : u ≠ v) :
    ∃ f, f ∉ D ∧ N.graph.target f = v ∧ N.ReachesOff D u (N.graph.source f) := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, hc, ⟨f, hf, rfl, ht⟩⟩
  · exact absurd rfl hne
  · exact ⟨f, hf, ht, hc⟩

/-- A path ending where the target of `k` does not reach avoids `k`. -/
theorem ReachesOff.insert_of_not_reaches {k : E} {u v : V} (h : N.ReachesOff D u v)
    (hk : ¬ N.ReachesOff D (N.graph.target k) v) : N.ReachesOff (insert k D) u v := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hab
    have hfk : f ≠ k := by
      rintro rfl
      exact hk .refl
    refine ReachesOff.tail_arc (ih fun h => hk (h.tail_arc hf)) ?_
    simp [hfk, hf]

/-- By acyclicity, a path starting below `k` avoids `k`. -/
theorem ReachesOff.insert_of_target_reaches (hA : N.graph.IsAcyclic) {k : E} {u v : V}
    (hu : N.ReachesOff D (N.graph.target k) u) (h : N.ReachesOff D u v) :
    N.ReachesOff (insert k D) u v := by
  induction h with
  | refl => exact .refl
  | @tail a b hua hab ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hab
    have hfk : f ≠ k := by
      rintro rfl
      exact not_reaches_target_source hA f (ReachesOff.reaches (hu.trans hua))
    refine ReachesOff.tail_arc ih ?_
    simp [hfk, hf]

/-- A path either avoids the arc `e`, or runs from a part avoiding `e` through `e`. -/
theorem ReachesOff.split (e : E) {u v : V} (h : N.ReachesOff D u v) :
    N.ReachesOff (insert e D) u v ∨
      (N.ReachesOff (insert e D) u (N.graph.source e) ∧ e ∉ D ∧
        N.ReachesOff D (N.graph.target e) v) := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail a b _ hab ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hab
    rcases ih with hl | ⟨hp, he, hr⟩
    · by_cases hfe : f = e
      · subst hfe
        exact Or.inr ⟨hl, hf, .refl⟩
      · refine Or.inl (ReachesOff.tail_arc hl ?_)
        simp [hfe, hf]
    · exact Or.inr ⟨hp, he, hr.tail_arc hf⟩

/-- In an acyclic graph, a path uses at most one of two arcs with a common target. -/
theorem reachesOff_insert_or (hA : N.graph.IsAcyclic) {k₁ k₂ : E} (hne : k₁ ≠ k₂)
    (ht : N.graph.target k₁ = N.graph.target k₂) {u v : V} (h : N.ReachesOff D u v) :
    N.ReachesOff (insert k₁ D) u v ∨ N.ReachesOff (insert k₂ D) u v := by
  rcases h.split k₁ with hl | ⟨hp, hk, hr⟩
  · exact Or.inl hl
  · refine Or.inr ?_
    have h₁ : N.ReachesOff (insert k₂ D) u (N.graph.source k₁) :=
      (hp.mono (Set.subset_insert _ _)).insert_of_not_reaches fun h =>
        not_reaches_target_source hA k₁ (ht ▸ h).reaches
    have h₂ : N.ReachesOff (insert k₂ D) (N.graph.target k₁) v :=
      ReachesOff.insert_of_target_reaches hA (ht ▸ .refl) hr
    exact (h₁.tail_arc (by simp [hne, hk])).trans h₂

/-- The reversed strict reachability is well founded. -/
theorem wellFounded_transGen_adj_flip (hN : N.IsPhylogenetic) :
    WellFounded fun a b : V => Relation.TransGen N.graph.Adj b a := by
  have : Finite V := hN.finite_vertices
  let r : V → V → Prop := fun a b => Relation.TransGen N.graph.Adj b a
  have : IsTrans V r := ⟨fun _ _ _ h h' => h'.trans h⟩
  have : Std.Irrefl r := ⟨fun a h => hN.acyclic a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl r

/-- Strict reachability is well founded. -/
theorem wellFounded_transGen_adj (hN : N.IsPhylogenetic) :
    WellFounded (Relation.TransGen N.graph.Adj) := by
  have : Finite V := hN.finite_vertices
  have : IsTrans V (Relation.TransGen N.graph.Adj) := ⟨fun _ _ _ h h' => h.trans h'⟩
  have : Std.Irrefl (Relation.TransGen N.graph.Adj) := ⟨fun a h => hN.acyclic a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- A nonempty set of vertices has a lowest member: nothing else of the set is below it. -/
theorem exists_lowest (hN : N.IsPhylogenetic) {S : Set V} (hS : S.Nonempty) :
    ∃ h ∈ S, ∀ u ∈ S, N.graph.Reaches h u → u = h := by
  obtain ⟨h, hh, hmin⟩ := (wellFounded_transGen_adj_flip hN).has_min S hS
  refine ⟨h, hh, fun u hu hr => ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hr with rfl | ht
  · rfl
  · exact absurd ht (hmin u hu)

/-- No deletion: every vertex other than the root has a parent. -/
theorem isDeletion_empty (hN : N.IsPhylogenetic) : N.IsDeletion ∅ where
  hybrid _ he := absurd he (Set.notMem_empty _)
  parent v hv := by
    have : Finite E := hN.finite_arcs
    obtain ⟨f, hf⟩ := (N.graph.one_le_indegree_iff v).mp (hN.nonroot_indegree v hv)
    exact ⟨f, Set.notMem_empty _, hf⟩

/-- Deleting one more of two arcs with a common target keeps a deletion. -/
theorem IsDeletion.insert (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {k k' : E} (hne : k ≠ k')
    (ht : N.graph.target k = N.graph.target k') (hk' : k' ∉ D) : N.IsDeletion (insert k D) where
  hybrid e he := by
    rcases he with rfl | he
    · have : Finite E := hN.finite_arcs
      refine Set.one_lt_ncard_iff (Set.toFinite _) |>.mpr ⟨e, k', rfl, ht.symm, hne⟩
    · exact hD.hybrid e he
  parent v hv := by
    obtain ⟨f, hf, hfv⟩ := hD.parent v hv
    by_cases hfk : f = k
    · subst hfk
      exact ⟨k', by simp [hne.symm, hk'], ht ▸ hfv⟩
    · exact ⟨f, by simp [hfk, hf], hfv⟩

/-- Off a deletion, the root still reaches every vertex. -/
theorem IsDeletion.root_reachesOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) (v : V) :
    N.ReachesOff D N.root v := by
  induction v using (wellFounded_transGen_adj hN).induction with
  | _ v ih =>
    by_cases hv : v = N.root
    · subst hv
      exact .refl
    · obtain ⟨f, hf, rfl⟩ := hD.parent v hv
      exact (ih _ (.single ⟨f, rfl, rfl⟩)).tail_arc hf

/-- A taxon dominated by an arc off a deletion is below it. -/
theorem DominatesOff.isBelowOff (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {e : E} {x : X}
    (h : N.DominatesOff D e x) : N.IsBelowOff D e x := by
  rcases (hD.root_reachesOff hN (N.leaf x)).split e with hl | ⟨-, he, hr⟩
  · exact absurd hl h
  · exact ⟨he, hr⟩

/-- Two distinct arcs dominating one taxon off a deletion are ordered. -/
theorem DominatesOff.reaches_or_reaches (hN : N.IsPhylogenetic) (hD : N.IsDeletion D) {g g' : E}
    {x : X} (hg : N.DominatesOff D g x) (hg' : N.DominatesOff D g' x) (hne : g ≠ g') :
    N.ReachesOff D (N.graph.target g) (N.graph.source g') ∨
      N.ReachesOff D (N.graph.target g') (N.graph.source g) := by
  have hb := hg.isBelowOff hN hD
  by_cases h : N.ReachesOff (insert g' D) N.root (N.graph.source g)
  · left
    rcases hb.2.split g' with hl | ⟨hp, -, -⟩
    · exact absurd ((h.tail_arc (by simp [hne, hb.1])).trans hl) hg'
    · exact hp.mono (Set.subset_insert _ _)
  · right
    rcases (hD.root_reachesOff hN (N.graph.source g)).split g' with hl | ⟨-, -, hr⟩
    · exact absurd hl h
    · exact hr

/-- An arc dominating a taxon both when `k₁` and when `k₂` is deleted dominates it. -/
theorem dominatesOff_of_insert_of_insert (hA : N.graph.IsAcyclic) {k₁ k₂ : E} (hne : k₁ ≠ k₂)
    (ht : N.graph.target k₁ = N.graph.target k₂) {e : E} {x : X}
    (h₁ : N.DominatesOff (insert k₁ D) e x) (h₂ : N.DominatesOff (insert k₂ D) e x) :
    N.DominatesOff D e x := by
  intro hr
  rcases reachesOff_insert_or hA hne ht hr with h | h
  · exact h₁ (by rwa [Set.insert_comm])
  · exact h₂ (by rwa [Set.insert_comm])

/-- A taxon below an arc is below it when `k₁` or when `k₂` is deleted. -/
theorem not_isBelowOff_of_insert_of_insert (hA : N.graph.IsAcyclic) {k₁ k₂ : E} (hne : k₁ ≠ k₂)
    (ht : N.graph.target k₁ = N.graph.target k₂) {e : E} {x : X} (he₁ : e ≠ k₁) (he₂ : e ≠ k₂)
    (h₁ : ¬ N.IsBelowOff (insert k₁ D) e x) (h₂ : ¬ N.IsBelowOff (insert k₂ D) e x) :
    ¬ N.IsBelowOff D e x := by
  rintro ⟨he, hr⟩
  rcases reachesOff_insert_or hA hne ht hr with h | h
  · exact h₁ ⟨by simp [he₁, he], h⟩
  · exact h₂ ⟨by simp [he₂, he], h⟩

/-- Domination of a taxon that the target of `k` does not reach ignores the deletion of `k`. -/
theorem dominatesOff_insert_iff {k e : E} {x : X}
    (hx : ¬ N.ReachesOff D (N.graph.target k) (N.leaf x)) :
    N.DominatesOff (insert k D) e x ↔ N.DominatesOff D e x := by
  constructor
  · intro h hr
    refine h ?_
    rw [Set.insert_comm]
    exact hr.insert_of_not_reaches fun h' => hx (h'.mono (Set.subset_insert _ _))
  · intro h hr
    exact h (hr.mono (Set.insert_subset_insert (Set.subset_insert _ _)))

/-- Being below an arc, for a taxon that the target of `k` does not reach, ignores the deletion of
`k`. -/
theorem isBelowOff_insert_iff {k e : E} {x : X}
    (hx : ¬ N.ReachesOff D (N.graph.target k) (N.leaf x)) :
    N.IsBelowOff (insert k D) e x ↔ N.IsBelowOff D e x := by
  constructor
  · rintro ⟨he, hr⟩
    exact ⟨fun h => he (Set.mem_insert_of_mem _ h), hr.mono (Set.subset_insert _ _)⟩
  · rintro ⟨he, hr⟩
    have hek : e ≠ k := by
      rintro rfl
      exact hx hr
    exact ⟨by simp [hek, he], hr.insert_of_not_reaches hx⟩

/-- The root has no parent. -/
theorem target_ne_root_of_isPhylogenetic (hN : N.IsPhylogenetic) (f : E) :
    N.graph.target f ≠ N.root := by
  have : Finite E := hN.finite_arcs
  exact (N.graph.indegree_eq_zero_iff N.root).mp hN.root_indegree f

/-- A taxon is a sink. -/
theorem eq_of_leaf_reachesOff_leaf (hN : N.IsPhylogenetic) {x y : X}
    (h : N.ReachesOff D (N.leaf x) (N.leaf y)) : y = x := by
  have : Finite E := hN.finite_arcs
  by_contra hne
  obtain ⟨f, -, hs, -⟩ := h.exists_first fun h' => hne (hN.leaf_injective h').symm
  exact (N.graph.outdegree_eq_zero_iff _).mp ((hN.leaves _).mpr ⟨x, rfl⟩) f hs

/-- A reticulation of degree at most three has two parents and one child. -/
theorem indegree_eq_two_of_degree_le_three (hN : N.IsPhylogenetic) {v : V}
    (h2 : 2 ≤ N.graph.indegree v) (h : N.graph.indegree v + N.graph.outdegree v ≤ 3) :
    N.graph.indegree v = 2 ∧ N.graph.outdegree v = 1 := by
  have hout : N.graph.outdegree v ≠ 0 := by
    intro h0
    obtain ⟨x, rfl⟩ := (hN.leaves v).mp h0
    have := hN.leaf_indegree x
    omega
  omega

/-- In a binary network every vertex has degree at most three. -/
theorem degree_le_three_of_isBinary (hN : N.IsPhylogenetic) (hBin : N.IsBinary) (v : V) :
    N.graph.indegree v + N.graph.outdegree v ≤ 3 := by
  by_cases hv : v = N.root
  · subst hv
    rw [hN.root_indegree, hBin.1]
    norm_num
  · by_cases hout : N.graph.outdegree v = 0
    · obtain ⟨x, rfl⟩ := (hN.leaves v).mp hout
      rw [hN.leaf_indegree, hout]
      norm_num
    · exact (hBin.2 v hv hout).le

/-- A path avoiding the only arc crossing `S` stays on one side. -/
theorem mem_iff_mem_of_reachesOff_insert {f : E} {S : Set V}
    (hS : ∀ g, N.graph.Crosses g S ↔ g = f) {u v : V} (h : N.ReachesOff (insert f D) u v) :
    u ∈ S ↔ v ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | @tail a b _ hab ih =>
    obtain ⟨g, hg, rfl, rfl⟩ := hab
    have hgf : g ≠ f := fun h => hg (Set.mem_insert_iff.mpr (Or.inl h))
    have hn := (hS g).not.mpr hgf
    simp only [DirectedMultigraph.Crosses] at hn
    exact ih.trans (by tauto)

/-- An arc into a reticulation is not a bridge: the root reaches both its ends without it. -/
theorem not_isBridge_of_two_parents (hN : N.IsPhylogenetic) {f g : E} (hne : f ≠ g)
    (ht : N.graph.target f = N.graph.target g) : ¬ N.graph.underlying.IsBridge f := by
  rw [N.graph.isBridge_iff]
  rintro ⟨S, hS⟩
  have hA := hN.acyclic
  have hdel := isDeletion_empty (N := N) hN
  have hr₁ : N.ReachesOff (insert f ∅) N.root (N.graph.source f) :=
    (hdel.root_reachesOff hN _).insert_of_not_reaches fun h =>
      not_reaches_target_source hA f (ReachesOff.reaches h)
  have hr₂ : N.ReachesOff (insert f ∅) N.root (N.graph.source g) :=
    (hdel.root_reachesOff hN _).insert_of_not_reaches fun h =>
      not_reaches_target_source hA g (ht ▸ ReachesOff.reaches h)
  have hr₃ : N.ReachesOff (insert f ∅) N.root (N.graph.target f) :=
    ht ▸ hr₂.tail_arc (by simp [hne.symm])
  have h₁ := mem_iff_mem_of_reachesOff_insert hS hr₁
  have h₂ := mem_iff_mem_of_reachesOff_insert hS hr₃
  have hc := (hS f).mpr rfl
  simp only [DirectedMultigraph.Crosses] at hc
  tauto

end Paths

variable [Fintype X] [DecidableEq X]

/-- With the arcs `D` deleted, the arc `e` induces the split of the quartet tree `s`. -/
def SplitOffAt (e : E) (s : QuartetTree X) : Prop :=
  ∃ P ∈ s.val, N.SeparatesOff D e (P : Set X) ((s.taxa \ P : Finset X) : Set X)

/-- With the arcs `D` deleted, some arc induces a split of a quartet tree on `q`. For `D = ∅` this is
`IsTreelike`, by `hasCutSplitOn_iff_separates`. -/
def IsTreelikeOff (q : Finset X) : Prop :=
  ∃ s ∈ treesOn q, ∃ e, N.SplitOffAt D e s

variable {N D}

omit [Fintype X] [DecidableEq X] in
theorem reachesOff_empty_iff {u v : V} : N.ReachesOff ∅ u v ↔ N.graph.Reaches u v := by
  have h : (fun a b => ∃ f, f ∉ (∅ : Set E) ∧ N.graph.source f = a ∧ N.graph.target f = b) =
      N.graph.Adj := by
    funext a b
    simp [DirectedMultigraph.Adj]
  simp only [ReachesOff, DirectedMultigraph.Reaches, h]

omit [Fintype X] [DecidableEq X] in
theorem dominatesOff_empty_iff {e : E} {x : X} : N.DominatesOff ∅ e x ↔ N.Dominates e x := by
  have h : (fun a b => ∃ f, f ∉ (insert e ∅ : Set E) ∧ N.graph.source f = a ∧ N.graph.target f = b) =
      fun a b => ∃ f, f ≠ e ∧ N.graph.source f = a ∧ N.graph.target f = b := by
    funext a b
    simp
  simp only [DominatesOff, Dominates, ReachesOff, AvoidingReach, h]

omit [Fintype X] [DecidableEq X] in
theorem isBelowOff_empty_iff {e : E} {x : X} : N.IsBelowOff ∅ e x ↔ N.IsBelow e x := by
  simp [IsBelowOff, IsBelow, reachesOff_empty_iff]

end Phylogenetics.RootedNetwork
