module

public import Phylogenetics.Network.Quartets
public import Phylogenetics.Network.OfHierarchy
public import Phylogenetics.Network.PendantCuts
public import Phylogenetics.Graph.BridgeCutLaminar

/-!
# A tree hierarchy constructed from network cuts

Choose an outgroup taxon. Nonempty cut sides avoiding that taxon, together with
the full set and the outgroup singleton, form an actual finite hierarchy. Its
unrooted splits are exactly the network's nonempty proper cut sides. The
construction uses graph cuts, not an arbitrary assigned tree.

## Main results

* `cutSplits_laminar`: the cut sides avoiding a taxon are laminar.
* `cutHierarchy_isHierarchy`, `mem_cutHierarchy`: the hierarchy of the cuts.
* `mem_unroot_cutHierarchy`: its unrooted splits are the nonempty proper cut sides.
* `cutHierarchy_graph_cuts`: the graph realizing it has the same labelled cuts.
-/

@[expose] public section

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-- Labelled singleton-cut sides avoiding a common taxon inherit graph laminarity. -/
theorem cutSplits_laminar (hG : N.graph.IsConnected) (r : X) {A B : Set X}
    (hA : N.HasCutSplit A) (hB : N.HasCutSplit B)
    (hrA : r ∉ A) (hrB : r ∉ B) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  obtain ⟨e, S, he, hS⟩ := hA
  obtain ⟨f, T, hf, hT⟩ := hB
  have hrS : N.leaf r ∉ S := by simpa only [← hS, Set.mem_preimage] using hrA
  have hrT : N.leaf r ∉ T := by simpa only [← hT, Set.mem_preimage] using hrB
  rcases N.graph.singletonCut_laminar hG (N.leaf r) e f he hf hrS hrT with
    h | h | h
  · left
    rw [← hS, ← hT]
    exact Set.preimage_mono h
  · right
    left
    rw [← hS, ← hT]
    exact Set.preimage_mono h
  · right
    right
    rw [← hS, ← hT]
    exact h.preimage N.leaf

variable [Fintype X] [DecidableEq X]

/-- Orient each nonempty taxon cut away from one fixed outgroup. -/
noncomputable def cutHierarchy (r : X) : Finset (Finset X) := by
  classical
  exact insert Finset.univ (insert {r} (Finset.univ.filter fun A : Finset X =>
    A.Nonempty ∧ r ∉ A ∧ N.HasCutSplit (A : Set X)))

theorem mem_cutHierarchy (r : X) (A : Finset X) :
    A ∈ N.cutHierarchy r ↔ A = Finset.univ ∨ A = {r} ∨
      (A.Nonempty ∧ r ∉ A ∧ N.HasCutSplit (A : Set X)) := by
  classical
  simp only [cutHierarchy, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The cut construction satisfies every defining hierarchy law. -/
theorem cutHierarchy_isHierarchy (hN : N.IsPhylogenetic) (r : X) :
    IsHierarchy (N.cutHierarchy r) := by
  classical
  refine ⟨(N.mem_cutHierarchy r _).mpr (Or.inl rfl), ?_, ?_, ?_⟩
  · intro x
    apply (N.mem_cutHierarchy r _).mpr
    by_cases hxr : x = r
    · exact Or.inr (Or.inl (by rw [hxr]))
    · right
      right
      refine ⟨Finset.singleton_nonempty x, ?_, ?_⟩
      · simpa only [Finset.mem_singleton] using (fun hrx : r = x => hxr hrx.symm)
      · simpa only [Finset.coe_singleton] using N.hasSingletonCut hN x
  · intro A hA
    rcases (N.mem_cutHierarchy r A).mp hA with rfl | rfl | hA
    · exact ⟨r, Finset.mem_univ r⟩
    · exact Finset.singleton_nonempty r
    · exact hA.1
  · intro A hA B hB
    rcases (N.mem_cutHierarchy r A).mp hA with rfl | rfl | hA
    · exact Or.inr (Or.inl (Finset.subset_univ B))
    · rcases (N.mem_cutHierarchy r B).mp hB with rfl | rfl | hB
      · exact Or.inl (Finset.subset_univ _)
      · exact Or.inl (Finset.Subset.refl _)
      · right
        right
        exact Finset.disjoint_singleton_left.mpr hB.2.1
    · rcases (N.mem_cutHierarchy r B).mp hB with rfl | rfl | hB
      · exact Or.inl (Finset.subset_univ _)
      · right
        right
        exact Finset.disjoint_singleton_right.mpr hA.2.1
      · simpa only [Finset.coe_subset, Finset.disjoint_coe] using
          N.cutSplits_laminar (N.graph_connected hN) r hA.2.2 hB.2.2 hA.2.1 hB.2.1

/-- A non-root member of the constructed hierarchy is a genuine labelled cut. -/
theorem hasCutSplit_of_mem_cutHierarchy (hN : N.IsPhylogenetic) (r : X)
    {A : Finset X} (hA : A ∈ N.cutHierarchy r) (hne : A ≠ Finset.univ) :
    N.HasCutSplit (A : Set X) := by
  rcases (N.mem_cutHierarchy r A).mp hA with h | rfl | h
  · exact False.elim (hne h)
  · simpa only [Finset.coe_singleton] using N.hasSingletonCut hN r
  · exact h.2.2

/-- The constructed tree's split family is exactly the nonempty proper network
cut sides. Empty sides from possible root stems are excluded explicitly. -/
theorem mem_unroot_cutHierarchy (hN : N.IsPhylogenetic) (r : X) (A : Finset X) :
    A ∈ unroot (N.cutHierarchy r) ↔
      A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X) := by
  have hH := N.cutHierarchy_isHierarchy hN r
  constructor
  · intro hA
    rcases mem_unroot.mp hA with ⟨hm, hne⟩ | ⟨hm, hne⟩
    · refine ⟨hH.2.2.1 A hm, ?_, N.hasCutSplit_of_mem_cutHierarchy hN r hm hne⟩
      exact Finset.nonempty_iff_ne_empty.mpr
        (fun he => hne ((Finset.compl_eq_empty_iff A).mp he))
    · have hcut := N.hasCutSplit_of_mem_cutHierarchy hN r hm hne
      refine ⟨?_, hH.2.2.1 Aᶜ hm, ?_⟩
      · exact Finset.nonempty_iff_ne_empty.mpr
          (fun he => hne ((Finset.compl_eq_univ_iff A).mpr he))
      · apply (N.hasCutSplit_compl (A : Set X)).mp
        simpa only [Finset.coe_compl] using hcut
  · rintro ⟨ha, hac, hcut⟩
    by_cases hr : r ∈ A
    · apply mem_unroot.mpr
      right
      refine ⟨(N.mem_cutHierarchy r Aᶜ).mpr (Or.inr (Or.inr ⟨hac, ?_, ?_⟩)), ?_⟩
      · simpa only [Finset.mem_compl, not_not] using hr
      · have hcomp := (N.hasCutSplit_compl (A : Set X)).mpr hcut
        simpa only [Finset.coe_compl] using hcomp
      · exact fun he => ha.ne_empty ((Finset.compl_eq_univ_iff A).mp he)
    · apply mem_unroot.mpr
      left
      refine ⟨(N.mem_cutHierarchy r A).mpr (Or.inr (Or.inr ⟨ha, hr, hcut⟩)), ?_⟩
      exact fun he => hac.ne_empty ((Finset.compl_eq_empty_iff A).mpr he)

/-- The cut hierarchy has a concrete graph realizing exactly the original
network's nonempty proper taxon cuts. This is independent of any model or CFs. -/
theorem cutHierarchy_graph_cuts (hN : N.IsPhylogenetic) (r : X) (A : Finset X) :
    (hierarchyNetwork (N.cutHierarchy r) (N.cutHierarchy_isHierarchy hN r)).HasCutSplit
      (A : Set X) ↔ A.Nonempty ∧ Aᶜ.Nonempty ∧ N.HasCutSplit (A : Set X) := by
  rw [hierarchyNetwork_hasCutSplit_iff, N.mem_unroot_cutHierarchy hN r A]

end Phylogenetics.RootedNetwork
