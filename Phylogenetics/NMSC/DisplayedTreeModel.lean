module

public import Phylogenetics.Network.DeletedArcs
public import Phylogenetics.NMSC.Analytic
public import Phylogenetics.NMSC.TreeCF
public import Phylogenetics.NMSC.Witness

/-!
# The displayed tree model, and the network multispecies coalescent with common inheritance

A *parent choice* picks one parent at every non-root vertex of a network; the probability of a choice is
the product of the inheritance probabilities of the chosen arcs. The arcs left out form a deletion
(`isDeletion_deletedArcs`), so the arcs kept are a spanning tree of the network. Each choice gives a gene tree
on the taxa, with the polytomies that the network's multifurcations leave: this is the displayed tree model.

At `ρ = 1` all lineages at a reticulation take one parent, so the network multispecies coalescent is the mixture
over the parent choices of the coalescent within the displayed tree (`nmscCF_rho_one`). The parameters of a
choice have inheritance `0` on the arcs left out. The kept arcs that still have a taxon below them form a
phylogenetic network with no reticulation (`choiceNetwork`), with the same gene tree distribution
(`geneTreeDist_choiceNetwork`). There the argument of `Phylogenetics.NMSC.TreeCF` applies, conditioning
at an arc whose fork may be further up (`one_sub_exp_le_sub_nmscCF_of_tree`).

## Main results

* `ParentChoice`, `deletedArcs`, `choiceWeight`, `sum_choiceWeight`: the choices and their probabilities.
* `displayedCluster`, `displayedClusters`, `displayedSides`: the gene tree of a choice, and
  `isUnrootedTree_displayedSides`: it is an unrooted tree on the taxa.
* `displays_displayedSides_of_inducedCutSplit`, `treeOfBlobs_subset_displayedSides`: every displayed tree
  displays the cut-edge splits, of the network and of its induced networks.
* `choiceMetric`, `nmscCF_rho_one`: the mixture over the choices, for inheritance without signs.
* `choiceNetwork`, `isPhylogenetic_choiceNetwork`, `nmscCF_choiceNetwork`: the tree of a choice as a network.
* `one_sub_exp_le_sub_nmscCF_rho_one`: at `ρ = 1`, an arc `e` separating the cherries of `s` gives
  `1 - exp (-ℓ e) ≤ F(s) - F(r)` for the alternatives `r`, for any weak parameters.
* `nmscCF_lt_rho_one_of_separates`: with `e` of positive length, `s` is strictly the most probable.
* `exists_isBridge_separating`: a quartet tree that the tree of blobs displays is separated by a bridge.
* `exchangeability_weak`, `cut_alternatives_weak`: these facts at the boundary of the parameters, by continuity.
* `displays_relabelQuartet_swap`: a tree containing a side that groups `a, a'` away from the other three
  taxa of a quartet tree treats `a` and `a'` alike.
* `hasTrivialFourBlob_of_tree`, `nmscCF_choiceMetric_eq_third`, `nmscCF_choiceMetric_bounds_of_displays`: long edges
  resolve a gene tree as its displayed tree, and a polytomy of it gives `1/3` for all lengths.
* `not_displays_of_hasTrivialFourBlob`: no displayed tree resolves a trivial 4-blob.
* `liftSet`, `setMass_mul_injDist`, `setMass_mul_cherryMass`: the Markov property at any set of vertices closed under
  children, with no domination.
* `placeInj`, `cherryMass_placeInj_lift`, `cherryMass_placeInj_eq_third`, `cherryMass_placeInj_eq_of_below`: singleton
  lineages at given vertices.
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} (N : RootedNetwork V E X)

/-! ### Parent choices -/

/-- A choice of one parent at every non-root vertex. At a tree vertex the choice is forced. -/
abbrev ParentChoice : Type _ := (v : {v : V // v ≠ N.root}) → {e : E // N.graph.target e = v.val}

/-- The arcs that the choice `c` leaves out. -/
def deletedArcs (c : N.ParentChoice) : Set E :=
  {f | ∀ h : N.graph.target f ≠ N.root, (c ⟨_, h⟩).val ≠ f}

/-- The probability of a parent choice: the product of the inheritance probabilities of the chosen
arcs. Tree arcs have inheritance one, so only the choices at reticulations count. -/
def choiceWeight [Fintype V] (θ : MetricData E) (c : N.ParentChoice) : ℝ :=
  ∏ v, θ.inheritance (c v).val

variable {N}

theorem notMem_deletedArcs_choice (c : N.ParentChoice) (v : {v : V // v ≠ N.root}) :
    (c v).val ∉ N.deletedArcs c := by
  intro h
  have hv : N.graph.target (c v).val ≠ N.root := by
    rw [(c v).property]
    exact v.property
  have hv' : (⟨N.graph.target (c v).val, hv⟩ : {v : V // v ≠ N.root}) = v := Subtype.ext (c v).property
  have := h hv
  rw [hv'] at this
  exact this rfl

/-- Off a parent choice, an arc is the chosen parent of its target. -/
theorem eq_choice_of_notMem_deletedArcs (hN : N.IsPhylogenetic) {c : N.ParentChoice} {f : E}
    (hf : f ∉ N.deletedArcs c) :
    (c ⟨N.graph.target f, target_ne_root_of_isPhylogenetic hN f⟩).val = f := by
  by_contra hne
  exact hf fun _ => hne

/-- An arc other than the chosen parent of its target is left out. -/
theorem mem_deletedArcs_of_ne {c : N.ParentChoice} {f : E} {v : {v : V // v ≠ N.root}}
    (hv : N.graph.target f = v.val) (hne : f ≠ (c v).val) : f ∈ N.deletedArcs c := by
  intro h
  have hv' : (⟨N.graph.target f, h⟩ : {v : V // v ≠ N.root}) = v := Subtype.ext hv
  rw [hv']
  exact hne.symm

/-- A vertex has at most one parent off a parent choice. -/
theorem eq_of_notMem_deletedArcs (hN : N.IsPhylogenetic) {c : N.ParentChoice} {f g : E}
    (hf : f ∉ N.deletedArcs c) (hg : g ∉ N.deletedArcs c) (h : N.graph.target f = N.graph.target g) :
    f = g := by
  have hsub : (⟨N.graph.target f, target_ne_root_of_isPhylogenetic hN f⟩ : {v : V // v ≠ N.root}) =
      ⟨N.graph.target g, target_ne_root_of_isPhylogenetic hN g⟩ := Subtype.ext h
  rw [← eq_choice_of_notMem_deletedArcs hN hf, ← eq_choice_of_notMem_deletedArcs hN hg, hsub]

/-- The arcs left out by a parent choice form a deletion. -/
theorem isDeletion_deletedArcs (hN : N.IsPhylogenetic) (c : N.ParentChoice) :
    N.IsDeletion (N.deletedArcs c) where
  hybrid f hf := by
    have : Finite E := hN.finite_arcs
    have hv := target_ne_root_of_isPhylogenetic hN f
    have hne : (c ⟨_, hv⟩).val ≠ f := hf hv
    exact Set.one_lt_ncard_iff (Set.toFinite _) |>.mpr ⟨f, (c ⟨_, hv⟩).val, rfl, (c ⟨_, hv⟩).property,
      hne.symm⟩
  parent v hv := ⟨(c ⟨v, hv⟩).val, notMem_deletedArcs_choice c _, (c ⟨v, hv⟩).property⟩

/-- A path off a parent choice from the root to a vertex is unique: two vertices reaching one vertex
are ordered. -/
theorem ReachesOff.comparable (hN : N.IsPhylogenetic) {c : N.ParentChoice} {u v w : V}
    (hu : N.ReachesOff (N.deletedArcs c) u w) (hv : N.ReachesOff (N.deletedArcs c) v w) :
    N.ReachesOff (N.deletedArcs c) u v ∨ N.ReachesOff (N.deletedArcs c) v u := by
  induction hu generalizing v with
  | refl => exact Or.inr hv
  | @tail b w hub hstep ih =>
    rcases Relation.ReflTransGen.cases_tail hv with rfl | ⟨y, hvy, ⟨g, hg, hgs, hgt⟩⟩
    · exact Or.inl (hub.tail hstep)
    · obtain ⟨f, hf, hfs, hft⟩ := hstep
      have hfg : f = g := eq_of_notMem_deletedArcs hN hf hg (hft.trans hgt.symm)
      subst hfg
      exact ih (hfs ▸ hgs ▸ hvy)

/-- A path off the arcs `insert e D` avoids `e`. -/
theorem ReachesOff.avoidingReach_of_insert {D : Set E} {e : E} {u v : V}
    (h : N.ReachesOff (insert e D) u v) : N.AvoidingReach e u v :=
  Relation.ReflTransGen.mono
    (fun _ _ ⟨f, hf, hs, ht⟩ => ⟨f, fun h' => hf (Set.mem_insert_iff.2 (Or.inl h')), hs, ht⟩) _ _ h

/-- An arc dominating a taxon dominates it off any set of arcs. -/
theorem Dominates.dominatesOff {D : Set E} {e : E} {x : X} (h : N.Dominates e x) :
    N.DominatesOff D e x :=
  fun hr => h hr.avoidingReach_of_insert

/-- The weights of the parent choices sum to one. -/
theorem sum_choiceWeight [Fintype V] [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsNormalized θ) : ∑ c : N.ParentChoice, N.choiceWeight θ c = 1 := by
  unfold choiceWeight
  have h := Finset.prod_univ_sum (fun v : {v : V // v ≠ N.root} =>
    (univ : Finset {e : E // N.graph.target e = v.val})) (fun v e => θ.inheritance e.val)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact prod_eq_one fun v _ => NMSC.sum_inheritance_weak hN hθ v.property

/-- The weight of a parent choice is nonnegative. -/
theorem choiceWeight_nonneg [Fintype V] [Fintype E] {θ : MetricData E} (hθ : N.IsWeakMetric θ)
    (c : N.ParentChoice) : 0 ≤ N.choiceWeight θ c :=
  prod_nonneg fun _ _ => NMSC.inheritance_nonneg_weak hθ _

/-! ### The tree of a parent choice -/

section Tree

variable [Fintype X] [DecidableEq X]

variable (N) in
/-- The taxa below a vertex along the arcs kept by a parent choice. -/
def displayedCluster (c : N.ParentChoice) (v : V) : Finset X :=
  univ.filter fun x => N.ReachesOff (N.deletedArcs c) v (N.leaf x)

omit [DecidableEq X] in
theorem mem_displayedCluster {c : N.ParentChoice} {v : V} {x : X} :
    x ∈ N.displayedCluster c v ↔ N.ReachesOff (N.deletedArcs c) v (N.leaf x) := by
  simp [displayedCluster]

variable (N) in
/-- The clusters of the rooted tree of a parent choice, on all the taxa. -/
def displayedClusters [Fintype V] (c : N.ParentChoice) : Finset (Finset X) :=
  (univ.image (N.displayedCluster c)).erase ∅

variable (N) in
/-- **The tree displayed by a parent choice**, given by the sides of its splits. A vertex of the network
with three or more kept children below it leaves a polytomy. -/
def displayedSides [Fintype V] (c : N.ParentChoice) : Finset (Finset X) :=
  unroot (N.displayedClusters c)

variable [Fintype V]

theorem mem_displayedClusters {c : N.ParentChoice} {A : Finset X} :
    A ∈ N.displayedClusters c ↔ A ≠ ∅ ∧ ∃ v, N.displayedCluster c v = A := by
  simp [displayedClusters]

/-- The clusters of a parent choice form a hierarchy. -/
theorem isHierarchy_displayedClusters [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) :
    IsHierarchy (N.displayedClusters c) := by
  have hdel := isDeletion_deletedArcs hN c
  refine ⟨mem_displayedClusters.2 ⟨univ_nonempty.ne_empty, N.root, ?_⟩, fun x => ?_, fun A hA => ?_,
    fun A hA B hB => ?_⟩
  · exact eq_univ_of_forall fun x => mem_displayedCluster.2 (hdel.root_reachesOff hN _)
  · refine mem_displayedClusters.2 ⟨singleton_ne_empty x, N.leaf x, ?_⟩
    ext y
    rw [mem_displayedCluster, mem_singleton]
    exact ⟨fun h => eq_of_leaf_reachesOff_leaf (D := N.deletedArcs c) hN h,
      fun h => h ▸ Relation.ReflTransGen.refl⟩
  · exact nonempty_iff_ne_empty.2 (mem_displayedClusters.1 hA).1
  · obtain ⟨-, u, rfl⟩ := mem_displayedClusters.1 hA
    obtain ⟨-, v, rfl⟩ := mem_displayedClusters.1 hB
    by_cases hdis : Disjoint (N.displayedCluster c u) (N.displayedCluster c v)
    · exact Or.inr (Or.inr hdis)
    obtain ⟨x, hxu, hxv⟩ := not_disjoint_iff.1 hdis
    rcases ReachesOff.comparable hN (mem_displayedCluster.1 hxu) (mem_displayedCluster.1 hxv) with
      h | h
    · exact Or.inr (Or.inl fun y hy => mem_displayedCluster.2 (h.trans (mem_displayedCluster.1 hy)))
    · exact Or.inl fun y hy => mem_displayedCluster.2 (h.trans (mem_displayedCluster.1 hy))

/-- The tree of a parent choice is an unrooted tree on the taxa. -/
theorem isUnrootedTree_displayedSides [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) :
    IsUnrootedTree (N.displayedSides c) :=
  ⟨_, isHierarchy_displayedClusters hN c, rfl⟩

omit [Fintype V] [DecidableEq X] in
/-- A taxon dominated by an arc is below it in the tree of every parent choice. -/
theorem mem_displayedCluster_of_dominates (hN : N.IsPhylogenetic) (c : N.ParentChoice) {e : E} {x : X}
    (h : N.Dominates e x) : x ∈ N.displayedCluster c (N.graph.target e) :=
  mem_displayedCluster.2 (h.dominatesOff.isBelowOff hN (isDeletion_deletedArcs hN c)).2

omit [Fintype V] [DecidableEq X] in
/-- A taxon not below an arc is not below it in the tree of a parent choice. -/
theorem notMem_displayedCluster_of_not_isBelow {c : N.ParentChoice} {e : E} {x : X}
    (h : ¬ N.IsBelow e x) : x ∉ N.displayedCluster c (N.graph.target e) :=
  fun hx => h (mem_displayedCluster.1 hx).reaches

/-- **An arc separating the cherry `P` of `s` from the other two taxa stays in the tree of every parent
choice**, so that tree displays `s`. The arc is never left out, since it dominates a taxon; deleted arcs
may shorten the path from it to the taxa, but the cluster of its target still is `P` on the taxa of `s`. -/
theorem displays_displayedSides_of_separates (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    {s : QuartetTree X} {P : Finset X} (hP : P ∈ s.val) {e : E} (hd : ∀ x ∈ P, N.Dominates e x)
    (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) : Displays (N.displayedSides c) s := by
  set A := N.displayedCluster c (N.graph.target e) with hA
  have hAq : A ∩ s.taxa = P := by
    ext x
    rw [mem_inter]
    constructor
    · rintro ⟨hxA, hxq⟩
      by_contra hxP
      exact notMem_displayedCluster_of_not_isBelow (hn x hxq hxP) hxA
    · exact fun hx => ⟨mem_displayedCluster_of_dominates hN c (hd x hx), s.subset_taxa hP hx⟩
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  obtain ⟨y, hy⟩ : (s.taxa \ P).Nonempty :=
    card_pos.1 (by rw [s.card_of_mem (s.sdiff_mem hP)]; omega)
  obtain ⟨hyq, hyP⟩ := mem_sdiff.1 hy
  have hAne : A ≠ ∅ := nonempty_iff_ne_empty.1 ⟨a, mem_displayedCluster_of_dominates hN c (hd a ha)⟩
  have hAu : A ≠ univ := fun h =>
    notMem_displayedCluster_of_not_isBelow (hn y hyq hyP) (h ▸ mem_univ y)
  refine ⟨A, mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hAne, _, rfl⟩, hAu⟩), ?_⟩
  rw [hAq]
  exact hP

omit [Fintype X] [Fintype V] in
/-- An induced cut-edge split: an arc dominates one of its cherries, with the other taxa not below it. -/
theorem exists_separating_arc [Fintype X] (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : InducedCutSplit N s) :
    ∃ P ∈ s.val, ∃ e, (∀ x ∈ P, N.Dominates e x) ∧ ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x := by
  obtain ⟨B, hB, hcut⟩ := hs
  obtain ⟨e, ⟨-, hd, hn⟩ | ⟨-, hd, hn⟩⟩ := (hasCutSplitOn_iff_separates hN _ _).1 hcut
  · exact ⟨B, hB, e, fun x hx => hd x ⟨s.subset_taxa hB hx, hx⟩, fun x hx hxB => hn x ⟨hx, hxB⟩⟩
  · refine ⟨s.taxa \ B, s.sdiff_mem hB, e,
      fun x hx => hd x ⟨(mem_sdiff.1 hx).1, (mem_sdiff.1 hx).2⟩, fun x hx hxB => hn x ⟨hx, ?_⟩⟩
    by_contra hxn
    exact hxB (mem_sdiff.2 ⟨hx, hxn⟩)

/-- **The tree of every parent choice displays the cut-edge splits of the induced networks.** -/
theorem displays_displayedSides_of_inducedCutSplit (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    {s : QuartetTree X} (hs : InducedCutSplit N s) : Displays (N.displayedSides c) s := by
  obtain ⟨P, hP, e, hd, hn⟩ := exists_separating_arc hN hs
  exact displays_displayedSides_of_separates hN c hP hd hn

omit [Fintype V] in
/-- A quartet tree that the tree of blobs displays is a cut-edge split of the induced network. -/
theorem inducedCutSplit_of_displays_treeOfBlobs (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : Displays (treeOfBlobs N) s) : InducedCutSplit N s := by
  obtain ⟨A, hA, hAs⟩ := hs
  have hcut : N.HasCutSplit (A : Set X) := (mem_filter.1 hA).2.2.2
  have hq := s.sdiff_mem hAs
  obtain ⟨a, ha⟩ : (A ∩ s.taxa).Nonempty := card_pos.1 (by rw [s.card_of_mem hAs]; omega)
  obtain ⟨y, hy⟩ : (s.taxa \ (A ∩ s.taxa)).Nonempty := card_pos.1 (by rw [s.card_of_mem hq]; omega)
  obtain ⟨hyq, hyA⟩ := mem_sdiff.1 hy
  have hon : N.HasCutSplitOn (s.taxa : Set X) (A : Set X) := hcut.hasCutSplitOn hN
    ⟨a, mem_coe.2 (mem_inter.1 ha).2, mem_coe.2 (mem_inter.1 ha).1⟩
    ⟨y, mem_coe.2 hyq, fun h => hyA (mem_inter.2 ⟨mem_coe.1 h, hyq⟩)⟩
  refine ⟨A ∩ s.taxa, hAs, (hasCutSplitOn_congr ?_).1 hon⟩
  ext x
  simp only [Set.mem_inter_iff, mem_coe, mem_inter]
  tauto

/-- **Every displayed tree is a resolution of the tree of blobs.** -/
theorem treeOfBlobs_subset_displayedSides [Nonempty X] (hN : N.IsPhylogenetic) (c : N.ParentChoice) :
    treeOfBlobs N ⊆ N.displayedSides c := by
  refine subset_of_forall_displays (isUnrootedTree_displayedSides hN c) (treeOfBlobs_isUnrootedTree hN)
    fun r hr => displays_displayedSides_of_inducedCutSplit hN c
      (inducedCutSplit_of_displays_treeOfBlobs hN hr)

end Tree

/-! ### Inheritance one on the chosen parents -/

section ChoiceMetric

open NMSC

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X]

variable (N) in
/-- The parameters in which every vertex takes its chosen parent: inheritance one on the chosen arcs and
zero on the others, the lengths being those of `θ`. -/
def choiceMetric (θ : MetricData E) (c : N.ParentChoice) : MetricData E where
  length := θ.length
  inheritance f := if f ∈ N.deletedArcs c then 0 else 1

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
@[simp] theorem choiceMetric_length (θ : MetricData E) (c : N.ParentChoice) :
    (N.choiceMetric θ c).length = θ.length := rfl

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem choiceMetric_inheritance_choice (θ : MetricData E) (c : N.ParentChoice)
    (v : {v : V // v ≠ N.root}) : (N.choiceMetric θ c).inheritance (c v).val = 1 :=
  ite_eq_right (notMem_deletedArcs_choice c v)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem choiceMetric_inheritance_of_mem (θ : MetricData E) {c : N.ParentChoice} {f : E}
    (hf : f ∈ N.deletedArcs c) : (N.choiceMetric θ c).inheritance f = 0 :=
  ite_eq_left hf

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of a parent choice are normalized. -/
theorem isNormalized_choiceMetric (hN : N.IsPhylogenetic) (θ : MetricData E) (c : N.ParentChoice) :
    N.IsNormalized (N.choiceMetric θ c) := by
  have hdel := isDeletion_deletedArcs hN c
  refine ⟨fun e he => ite_eq_right fun hd => ?_, fun v hv => ?_⟩
  · have := hdel.hybrid e hd
    unfold RootedNetwork.IsTreeArc at he
    unfold RootedNetwork.IsHybridArc at this
    omega
  · have hvr : v ≠ N.root := fun h => by
      have := hN.root_indegree
      rw [h] at hv
      omega
    rw [Finset.sum_eq_single (c ⟨v, hvr⟩).val]
    · rw [ite_eq_left (c ⟨v, hvr⟩).property]
      exact choiceMetric_inheritance_choice θ c _
    · intro f _ hf
      split_ifs with hft
      · exact choiceMetric_inheritance_of_mem θ (mem_deletedArcs_of_ne (v := ⟨v, hvr⟩) hft hf)
      · rfl
    · exact fun h => absurd (mem_univ _) h

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The parameters of a parent choice are weak parameters, if the lengths are nonnegative. -/
theorem isWeakMetric_choiceMetric (hN : N.IsPhylogenetic) {θ : MetricData E} (hℓ : ∀ e, 0 ≤ θ.length e)
    (c : N.ParentChoice) : N.IsWeakMetric (N.choiceMetric θ c) := by
  refine ⟨hℓ, fun e _ => ?_, isNormalized_choiceMetric hN θ c⟩
  change 0 ≤ if e ∈ N.deletedArcs c then (0 : ℝ) else 1
  split_ifs <;> norm_num

omit [Fintype V] [Fintype E] in
/-- What a constant assignment of the roots of `F` to the parent `k` puts on the arcs entering `v`. -/
theorem forestBelow_const [Fintype E] {F : Finset (Finset X)} {v : V} (k e : {e // N.graph.target e = v}) :
    forestBelow F ((univ.filter fun _ : {A // A ∈ roots F} => k = e).image Subtype.val) =
      if e.val = k.val then F else ∅ := by
  by_cases h : e = k
  · subst h
    rw [ite_eq_left rfl, filter_true_of_mem fun _ _ => rfl]
    ext A
    rw [mem_forestBelow]
    constructor
    · exact fun h => h.1
    · intro hA
      obtain ⟨R, hR, hAR⟩ := exists_mem_roots_subset hA
      exact ⟨hA, R, mem_image.2 ⟨⟨R, hR⟩, mem_univ _, rfl⟩, hAR⟩
  · rw [ite_eq_right fun h' => h (Subtype.ext h'), filter_false_of_mem fun _ _ h' => h h'.symm, image_empty]
    ext A
    simp [mem_forestBelow]

omit [Fintype V] in
/-- The condition of `allocationFactor` on a constant assignment. -/
theorem forall_bot_const_iff {F : Finset (Finset X)} {v : V} {bot : E → Finset (Finset X)}
    (k : {e // N.graph.target e = v}) :
    (∀ e : {e // N.graph.target e = v}, bot e.val =
      forestBelow F ((univ.filter fun _ : {A // A ∈ roots F} => k = e).image Subtype.val)) ↔
      bot k.val = F ∧ ∀ g, N.graph.target g = v → g ≠ k.val → bot g = ∅ := by
  simp only [forestBelow_const]
  constructor
  · intro h
    refine ⟨by simpa using h k, fun g hg hne => ?_⟩
    simpa [hne] using h ⟨g, hg⟩
  · rintro ⟨h1, h2⟩ e
    by_cases he : e.val = k.val
    · rw [ite_eq_left he, he, h1]
    · rw [ite_eq_right he]
      exact h2 e.val e.property he

omit [Fintype V] in
/-- **At a vertex all of whose inheritance is on one parent `k`**, the allocation is forced: all roots
take `k`. -/
theorem allocationFactor_of_inheritance {θ : MetricData E} {ρ : ℝ} (hρ : 0 ≤ ρ) {v : V} {k : E}
    (hk : N.graph.target k = v) (h1 : θ.inheritance k = 1)
    (h0 : ∀ g, N.graph.target g = v → g ≠ k → θ.inheritance g = 0) (F : Finset (Finset X))
    (bot : E → Finset (Finset X)) :
    allocationFactor N θ ρ F v bot =
      if bot k = F ∧ ∀ g, N.graph.target g = v → g ≠ k → bot g = ∅ then 1 else 0 := by
  unfold allocationFactor
  set k₀ : {e // N.graph.target e = v} := ⟨k, hk⟩ with hk₀
  rw [Finset.sum_eq_single (fun _ => k₀)]
  · have hc := forall_bot_const_iff (F := F) (bot := bot) k₀
    simp only [hk₀] at hc ⊢
    have hW : allocationWeight ρ (fun e : {e // N.graph.target e = v} => θ.inheritance e.val)
        (fun _ : {A // A ∈ roots F} => (⟨k, hk⟩ : {e // N.graph.target e = v})) = 1 := by
      rcases isEmpty_or_nonempty {A // A ∈ roots F} with hR | hR
      · simp [allocationWeight]
      · exact allocationWeight_const_eq_one hρ (γ := fun g : {g // N.graph.target g = v} =>
          θ.inheritance g.val) h1
    rw [hW]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (hc.1 h₁) h₂
    · exact absurd (hc.2 h₂) h₁
    · rfl
  · intro a _ ha
    obtain ⟨r, hr⟩ : ∃ r, a r ≠ k₀ := Function.ne_iff.1 ha
    have hz := allocationWeight_eq_zero_of_apply (ρ := ρ) (γ := fun g : {g // N.graph.target g = v} =>
      θ.inheritance g.val) a r (h0 _ (a r).property fun h => hr (Subtype.ext h))
    rw [hz, ite_self]
  · exact fun h => absurd (mem_univ _) h

omit [Fintype X] [DecidableEq X] [Fintype V] in
/-- The allocation of a parent choice is forced. -/
theorem allocationFactor_choiceMetric [Fintype X] [DecidableEq X] {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : MetricData E)
    (c : N.ParentChoice) (v : {v : V // v ≠ N.root}) (F : Finset (Finset X))
    (bot : E → Finset (Finset X)) :
    allocationFactor N (N.choiceMetric θ c) ρ F v.val bot =
      if bot (c v).val = F ∧ ∀ g, N.graph.target g = v.val → g ≠ (c v).val → bot g = ∅ then 1 else 0 :=
  allocationFactor_of_inheritance hρ (c v).property (choiceMetric_inheritance_choice θ c v)
    (fun _ hg hne => choiceMetric_inheritance_of_mem θ (mem_deletedArcs_of_ne hg hne)) F bot

omit [Fintype V] in
/-- **At `ρ = 1` the allocation at a vertex is the mixture over its parents.** All the roots take one
parent `k`, with probability `γ_k`. With no roots, nothing is allocated: the one empty assignment has
weight one, and the inheritance sums to one. No sign of `γ` is used. -/
theorem allocationFactor_rho_one (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsNormalized θ) {v : V}
    (hv : v ≠ N.root) (F : Finset (Finset X)) (bot : E → Finset (Finset X)) :
    allocationFactor N θ 1 F v bot = ∑ k : {e // N.graph.target e = v}, θ.inheritance k.val *
      if bot k.val = F ∧ ∀ g, N.graph.target g = v → g ≠ k.val → bot g = ∅ then 1 else 0 := by
  unfold allocationFactor
  rcases isEmpty_or_nonempty {A // A ∈ roots F} with hR | ⟨⟨r₀⟩⟩
  · have hF : F = ∅ := eq_empty_of_forall_notMem fun A hA => by
      obtain ⟨R, hR', -⟩ := exists_mem_roots_subset hA
      exact hR.elim ⟨R, hR'⟩
    subst hF
    have hsum := sum_inheritance_weak hN hθ hv
    have hb : ∀ S : Finset (Finset X), forestBelow (∅ : Finset (Finset X)) S = ∅ := fun S => by
      ext A
      simp [mem_forestBelow]
    have hc : ∀ k : {e // N.graph.target e = v},
        (bot k.val = ∅ ∧ ∀ g, N.graph.target g = v → g ≠ k.val → bot g = ∅) ↔
        ∀ e : {e // N.graph.target e = v}, bot e.val = ∅ := fun k =>
      ⟨fun h e => by
        by_cases he : e.val = k.val
        · rw [he]
          exact h.1
        · exact h.2 e.val e.property he, fun h => ⟨h k, fun g hg _ => h ⟨g, hg⟩⟩⟩
    rw [Fintype.sum_subsingleton _ (fun r => hR.elim r)]
    have hw : ∀ a : {A // A ∈ roots (∅ : Finset (Finset X))} → {e // N.graph.target e = v},
        allocationWeight 1 (fun e : {e // N.graph.target e = v} => θ.inheritance e.val) a = 1 := by
      intro a
      simp [allocationWeight]
    simp only [hw, hb, hc]
    rw [← Finset.sum_mul, hsum, one_mul]
  · have hinj : Function.Injective fun (k : {e // N.graph.target e = v}) (_ : {A // A ∈ roots F}) => k :=
      fun _ _ h => congrFun h r₀
    symm
    refine Fintype.sum_of_injective _ hinj _ _ (fun a ha => ?_) fun k => ?_
    · have : ¬ ∀ r, a r = a r₀ := fun h => ha ⟨a r₀, funext fun r => (h r).symm⟩
      split_ifs with hcond
      · rw [allocationWeight_rho_one r₀, ite_eq_right this]
      · rfl
    · have hc := forall_bot_const_iff (F := F) (bot := bot) k
      have : Nonempty {A // A ∈ roots F} := ⟨r₀⟩
      rw [allocationWeight_rho_one_const]
      split_ifs with h₁ h₂ h₂
      · rw [mul_one]
      · exact absurd (hc.2 h₁) h₂
      · exact absurd (hc.1 h₂) h₁
      · rw [mul_zero]

/-- **At `ρ = 1` the weight of a history is the mixture over the parent choices.** -/
theorem historyWeight_rho_one (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsNormalized θ)
    (bot top : E → Finset (Finset X)) :
    historyWeight N θ 1 bot top =
      ∑ c : N.ParentChoice, N.choiceWeight θ c * historyWeight N (N.choiceMetric θ c) 1 bot top := by
  unfold historyWeight
  have hprod : ∀ θ' : MetricData E, ∏ v ∈ univ.erase N.root,
      allocationFactor N θ' 1 (arrivingForest N top v) v bot =
      ∏ v : {v : V // v ≠ N.root}, allocationFactor N θ' 1 (arrivingForest N top v.val) v.val bot :=
    fun θ' => Finset.prod_subtype _ (fun v => by simp) _
  simp only [hprod, choiceMetric_length]
  have h1 : ∏ v : {v : V // v ≠ N.root}, allocationFactor N θ 1 (arrivingForest N top v.val) v.val bot =
      ∑ c : N.ParentChoice, ∏ v, (θ.inheritance (c v).val *
        allocationFactor N (N.choiceMetric θ c) 1 (arrivingForest N top v.val) v.val bot) := by
    have h := Finset.prod_univ_sum (fun v : {v : V // v ≠ N.root} =>
      (univ : Finset {e : E // N.graph.target e = v.val}))
      (fun v k => θ.inheritance k.val *
        if bot k.val = arrivingForest N top v.val ∧
          ∀ g, N.graph.target g = v.val → g ≠ k.val → bot g = ∅ then (1 : ℝ) else 0)
    rw [Fintype.piFinset_univ] at h
    rw [prod_congr rfl fun v _ => allocationFactor_rho_one hN hθ v.property _ bot, h]
    refine sum_congr rfl fun c _ => prod_congr rfl fun v _ => ?_
    rw [allocationFactor_choiceMetric zero_le_one]
  rw [h1, Finset.sum_mul]
  refine sum_congr rfl fun c _ => ?_
  unfold choiceWeight
  rw [prod_mul_distrib, mul_assoc]

/-- **At `ρ = 1` the gene tree distribution is the mixture over the parent choices.** -/
theorem geneTreeDist_rho_one (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsNormalized θ)
    (G : Finset (Finset X)) :
    geneTreeDist N θ 1 G =
      ∑ c : N.ParentChoice, N.choiceWeight θ c * geneTreeDist N (N.choiceMetric θ c) 1 G := by
  unfold geneTreeDist
  simp only [historyWeight_rho_one hN hθ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact (sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- **At `ρ = 1` the concordance factors are the mixture over the parent choices**: all lineages at a
reticulation take one parent, so a gene tree evolves within one displayed tree. -/
theorem nmscCF_rho_one (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsNormalized θ)
    (s : QuartetTree X) :
    nmscCF N θ 1 s = ∑ c : N.ParentChoice, N.choiceWeight θ c * nmscCF N (N.choiceMetric θ c) 1 s := by
  unfold nmscCF
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun G _ => ?_
  split_ifs
  · exact geneTreeDist_rho_one hN hθ G
  · simp

end ChoiceMetric

/-! ### The network of a parent choice

The arcs kept by a parent choice, with the vertices that still have a taxon below them, form a rooted tree
on the taxa, a phylogenetic network in its own right. A vertex none of whose kept descendants is a taxon has
to go, since the sinks of a phylogenetic network are its taxa. In the parameters of the parent choice no
lineage leaves these arcs, so that the gene tree distribution is the same. -/

section Pruned

open NMSC

variable (N) in
/-- A vertex that still has a taxon below it along the arcs that a parent choice keeps. -/
def IsKeptVertex (c : N.ParentChoice) (v : V) : Prop :=
  ∃ x, N.ReachesOff (N.deletedArcs c) v (N.leaf x)

variable (N) in
/-- An arc kept by a parent choice with a taxon below it. -/
def IsKeptArc (c : N.ParentChoice) (f : E) : Prop :=
  f ∉ N.deletedArcs c ∧ N.IsKeptVertex c (N.graph.target f)

theorem IsKeptArc.source {c : N.ParentChoice} {f : E} (hf : N.IsKeptArc c f) :
    N.IsKeptVertex c (N.graph.source f) := by
  obtain ⟨h1, x, hx⟩ := hf
  exact ⟨x, ReachesOff.head_arc h1 hx⟩

theorem isKeptVertex_leaf (c : N.ParentChoice) (x : X) : N.IsKeptVertex c (N.leaf x) :=
  ⟨x, .refl⟩

/-- The root has all taxa below it. -/
theorem isKeptVertex_root (hN : N.IsPhylogenetic) (c : N.ParentChoice) (x : X) :
    N.IsKeptVertex c N.root :=
  ⟨x, (isDeletion_deletedArcs hN c).root_reachesOff hN _⟩

variable (N) in
/-- **The network of a parent choice**: a rooted tree on the taxa. -/
def choiceNetwork (hN : N.IsPhylogenetic) (c : N.ParentChoice) (x₀ : X) :
    RootedNetwork {v // N.IsKeptVertex c v} {f // N.IsKeptArc c f} X where
  graph :=
    { source := fun f => ⟨N.graph.source f.val, f.property.source⟩
      target := fun f => ⟨N.graph.target f.val, f.property.2⟩ }
  root := ⟨N.root, isKeptVertex_root hN c x₀⟩
  leaf := fun x => ⟨N.leaf x, isKeptVertex_leaf c x⟩

variable (N) in
theorem mem_erase_root_iff [Fintype V] {v : V} : v ∈ (univ : Finset V).erase N.root ↔ v ≠ N.root := by
  simp

variable (hN : N.IsPhylogenetic) (c : N.ParentChoice) (x₀ : X)

include hN in
/-- A path off a parent choice ending at a kept vertex is a path of its network. -/
theorem reaches_choiceNetwork {u v : V} (hu : N.IsKeptVertex c u) (hv : N.IsKeptVertex c v)
    (h : N.ReachesOff (N.deletedArcs c) u v) :
    (N.choiceNetwork hN c x₀).graph.Reaches ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction h with
  | refl => exact .refl
  | @tail a b hua hab ih =>
    obtain ⟨f, hf, rfl, rfl⟩ := hab
    exact (ih (IsKeptArc.source ⟨hf, hv⟩)).tail ⟨⟨f, hf, hv⟩, rfl, rfl⟩

/-- A path of the network of a parent choice is a path off it. -/
theorem reachesOff_of_reaches_choiceNetwork {u v : {v // N.IsKeptVertex c v}}
    (h : (N.choiceNetwork hN c x₀).graph.Reaches u v) :
    N.ReachesOff (N.deletedArcs c) u.val v.val := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    obtain ⟨f, rfl, rfl⟩ := hab
    exact ih.tail ⟨f.val, f.property.1, rfl, rfl⟩

/-- The network of a parent choice has no two arcs with one target. -/
theorem eq_of_target_choiceNetwork {f g : {f // N.IsKeptArc c f}}
    (h : (N.choiceNetwork hN c x₀).graph.target f = (N.choiceNetwork hN c x₀).graph.target g) :
    f = g :=
  Subtype.ext (eq_of_notMem_deletedArcs hN f.property.1 g.property.1 (congrArg Subtype.val h))

/-- The chosen parent of a kept non-root vertex is an arc of the network of the choice. -/
theorem exists_target_choiceNetwork {v : {v // N.IsKeptVertex c v}} (hv : v.val ≠ N.root) :
    ∃ f : {f // N.IsKeptArc c f}, (N.choiceNetwork hN c x₀).graph.target f = v := by
  refine ⟨⟨(c ⟨v.val, hv⟩).val, notMem_deletedArcs_choice c _, ?_⟩, Subtype.ext (c ⟨v.val, hv⟩).property⟩
  rw [(c ⟨v.val, hv⟩).property]
  exact v.property

/-- **The network of a parent choice is a phylogenetic network.** -/
theorem isPhylogenetic_choiceNetwork : (N.choiceNetwork hN c x₀).IsPhylogenetic := by
  have : Finite E := hN.finite_arcs
  have : Finite V := hN.finite_vertices
  have : Finite X := hN.finite_taxa
  have hdel := isDeletion_deletedArcs hN c
  have htree : ∀ f g : {f // N.IsKeptArc c f},
      (N.choiceNetwork hN c x₀).graph.target f = (N.choiceNetwork hN c x₀).graph.target g → f = g :=
    fun _ _ h => eq_of_target_choiceNetwork hN c x₀ h
  have hleafne : ∀ x, N.leaf x ≠ N.root := fun x h => by
    have h1 := hN.leaf_indegree x
    have h0 := hN.root_indegree
    rw [h] at h1
    omega
  refine
    { finite_vertices := inferInstance
      finite_arcs := inferInstance
      finite_taxa := inferInstance
      acyclic := fun v hv => ?_
      root_reaches := fun v => ?_
      root_indegree := ?_
      nonroot_indegree := fun v hv => ?_
      leaf_injective := fun x y h => hN.leaf_injective (congrArg Subtype.val h)
      leaf_indegree := fun x => ?_
      leaves := fun v => ?_ }
  · have hl : ∀ u w : {v // N.IsKeptVertex c v}, Relation.TransGen (N.choiceNetwork hN c x₀).graph.Adj u w →
        Relation.TransGen N.graph.Adj u.val w.val := by
      intro u w h
      induction h with
      | single h =>
        obtain ⟨f, rfl, rfl⟩ := h
        exact .single ⟨f.val, rfl, rfl⟩
      | tail _ h ih =>
        obtain ⟨f, rfl, rfl⟩ := h
        exact ih.tail ⟨f.val, rfl, rfl⟩
    exact hN.acyclic v.val (hl v v hv)
  · exact reaches_choiceNetwork hN c x₀ _ v.property (hdel.root_reachesOff hN _)
  · refine ((N.choiceNetwork hN c x₀).graph.indegree_eq_zero_iff _).2 fun f hf => ?_
    exact target_ne_root_of_isPhylogenetic hN f.val (congrArg Subtype.val hf)
  · exact ((N.choiceNetwork hN c x₀).graph.one_le_indegree_iff _).2
      (exists_target_choiceNetwork hN c x₀ fun h => hv (Subtype.ext h))
  · obtain ⟨f, hf⟩ := exists_target_choiceNetwork hN c x₀ (v := ⟨N.leaf x, isKeptVertex_leaf c x⟩)
      (hleafne x)
    exact (N.choiceNetwork hN c x₀).graph.indegree_eq_one_iff _ |>.2
      ⟨f, fun g => ⟨fun hg => htree _ _ (hg.trans hf.symm), fun hg => hg ▸ hf⟩⟩
  · rw [(N.choiceNetwork hN c x₀).graph.outdegree_eq_zero_iff]
    constructor
    · intro h0
      obtain ⟨x, hx⟩ := v.property
      refine ⟨x, ?_⟩
      by_contra hne
      have hne' : v.val ≠ N.leaf x := fun h => hne (Subtype.ext h.symm)
      obtain ⟨f, hf, hs, hr⟩ := ReachesOff.exists_first hx hne'
      exact h0 ⟨f, hf, x, hr⟩ (Subtype.ext hs)
    · rintro ⟨x, rfl⟩ f hf
      exact (N.graph.outdegree_eq_zero_iff _).1 ((hN.leaves _).2 ⟨x, rfl⟩) f.val (congrArg Subtype.val hf)

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {ρ : ℝ}

variable (N) in
/-- The parameters of the network of a parent choice: the lengths of the same arcs, and inheritance one. -/
def choiceNetworkMetric (θ : MetricData E) (c : N.ParentChoice) : MetricData {f // N.IsKeptArc c f} where
  length f := θ.length f.val
  inheritance _ := 1

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- The network of a parent choice has valid parameters when the lengths of its arcs are positive. -/
theorem isMetric_choiceNetworkMetric [Fintype E] {θ : MetricData E}
    (hℓ : ∀ f, N.IsKeptArc c f → 0 < θ.length f) :
    (N.choiceNetwork hN c x₀).IsMetric (N.choiceNetworkMetric θ c) := by
  have htree : ∀ f g : {f // N.IsKeptArc c f},
      (N.choiceNetwork hN c x₀).graph.target f = (N.choiceNetwork hN c x₀).graph.target g → f = g :=
    fun _ _ h => eq_of_target_choiceNetwork hN c x₀ h
  have hle : ∀ v, ¬ 2 ≤ (N.choiceNetwork hN c x₀).graph.indegree v := fun v h2 => by
    have : (N.choiceNetwork hN c x₀).graph.indegree v ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).2 fun a ha b hb => htree _ _ (ha.trans hb.symm)
    omega
  exact ⟨fun f _ => hℓ f.val f.property, fun f hf => absurd hf (hle _), fun _ _ => rfl,
    fun _ _ => one_pos, fun v hv => absurd hv (hle v)⟩

/-- The forests on the arcs of the network of a parent choice, extended by the empty forest. -/
def extForest (c : N.ParentChoice) (b : {f // N.IsKeptArc c f} → Finset (Finset X)) :
    E → Finset (Finset X) := fun f => if h : N.IsKeptArc c f then b ⟨f, h⟩ else ∅

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem extForest_val {b : {f // N.IsKeptArc c f} → Finset (Finset X)} (f : {f // N.IsKeptArc c f}) :
    extForest c b f.val = b f :=
  dite_eq_left f.property

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem extForest_of_not {b : {f // N.IsKeptArc c f} → Finset (Finset X)} {f : E}
    (hf : ¬ N.IsKeptArc c f) : extForest c b f = ∅ :=
  dite_eq_right hf

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
theorem extForest_injective : Function.Injective (extForest (X := X) c) := fun b b' h =>
  funext fun f => by rw [← extForest_val (b := b) c f, h, extForest_val]

omit [Fintype V] in
/-- The forest arriving at a kept vertex is the same in the network of the choice. -/
theorem arrivingForest_extForest (t : {f // N.IsKeptArc c f} → Finset (Finset X))
    (v : {v // N.IsKeptVertex c v}) :
    arrivingForest N (extForest c t) v.val = arrivingForest (N.choiceNetwork hN c x₀) t v := by
  unfold arrivingForest
  congr 1
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · ext A
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, hA⟩
      by_cases hk : N.IsKeptArc c f
      · exact ⟨⟨f, hk⟩, Subtype.ext hf, by rwa [← extForest_val (b := t) c (⟨f, hk⟩ : {f // N.IsKeptArc c f})]⟩
      · rw [extForest_of_not c hk] at hA
        exact absurd hA (notMem_empty _)
    · rintro ⟨f, hf, hA⟩
      exact ⟨f.val, congrArg Subtype.val hf, by rwa [extForest_val]⟩

omit [Fintype V] in
/-- No forest arrives at a vertex that is not kept. -/
theorem arrivingForest_extForest_of_not (t : {f // N.IsKeptArc c f} → Finset (Finset X)) {v : V}
    (hv : ¬ N.IsKeptVertex c v) : arrivingForest N (extForest c t) v = ∅ := by
  unfold arrivingForest
  rw [union_eq_empty]
  constructor
  · refine image_eq_empty.2 (filter_eq_empty_iff.2 fun x _ hx => hv (hx ▸ isKeptVertex_leaf c x))
  · refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
    rw [extForest_of_not c fun hk => hv ((mem_filter.1 hf).2 ▸ hk.source)] at hAf
    exact notMem_empty _ hAf

omit [Fintype V] in
/-- The factor of a kept vertex is the same in the network of the choice. -/
theorem allocationFactor_extForest (hρ : 0 ≤ ρ) (θ : MetricData E)
    (F : Finset (Finset X)) (b : {f // N.IsKeptArc c f} → Finset (Finset X))
    {v : {v // N.IsKeptVertex c v}} (hv : v ≠ (N.choiceNetwork hN c x₀).root) :
    allocationFactor N (N.choiceMetric θ c) ρ F v.val (extForest c b) =
      allocationFactor (N.choiceNetwork hN c x₀) (N.choiceNetworkMetric θ c) ρ F v b := by
  have hvr : v.val ≠ N.root := fun h => hv (Subtype.ext h)
  obtain ⟨k, hk⟩ := exists_target_choiceNetwork hN c x₀ hvr
  have htree : ∀ f g : {f // N.IsKeptArc c f},
      (N.choiceNetwork hN c x₀).graph.target f = (N.choiceNetwork hN c x₀).graph.target g → f = g :=
    fun _ _ h => eq_of_target_choiceNetwork hN c x₀ h
  have hkc : (c ⟨v.val, hvr⟩).val = k.val := by
    have hkv : N.graph.target k.val = v.val := congrArg Subtype.val hk
    have h1 := eq_choice_of_notMem_deletedArcs hN k.property.1
    have hsub : (⟨N.graph.target k.val, target_ne_root_of_isPhylogenetic hN k.val⟩ :
        {v : V // v ≠ N.root}) = ⟨v.val, hvr⟩ := Subtype.ext hkv
    rwa [hsub] at h1
  rw [allocationFactor_choiceMetric hρ θ c ⟨v.val, hvr⟩,
    allocationFactor_of_inheritance hρ hk rfl (fun g hg hne => absurd (htree _ _ (hg.trans hk.symm)) hne)]
  have hiff : (extForest c b (c ⟨v.val, hvr⟩).val = F ∧ ∀ g, N.graph.target g = v.val →
      g ≠ (c ⟨v.val, hvr⟩).val → extForest c b g = ∅) ↔
      (b k = F ∧ ∀ g, (N.choiceNetwork hN c x₀).graph.target g = v → g ≠ k → b g = ∅) := by
    rw [hkc, extForest_val]
    constructor
    · exact fun h => ⟨h.1, fun g hg hne => absurd (htree _ _ (hg.trans hk.symm)) hne⟩
    · refine fun h => ⟨h.1, fun g hg hgk => extForest_of_not c fun hkept => hgk ?_⟩
      have hgv : (N.choiceNetwork hN c x₀).graph.target ⟨g, hkept⟩ =
          (N.choiceNetwork hN c x₀).graph.target k :=
        Subtype.ext (hg.trans (congrArg Subtype.val hk).symm)
      exact congrArg Subtype.val (htree _ _ hgv)
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (hiff.1 h₁) h₂
  · exact absurd (hiff.2 h₂) h₁
  · rfl

omit [Fintype V] in
/-- The factor of a vertex that is not kept is one. -/
theorem allocationFactor_extForest_of_not (hρ : 0 ≤ ρ) (θ : MetricData E)
    (t b : {f // N.IsKeptArc c f} → Finset (Finset X)) {v : V} (hv : ¬ N.IsKeptVertex c v)
    (hvr : v ≠ N.root) :
    allocationFactor N (N.choiceMetric θ c) ρ (arrivingForest N (extForest c t) v) v (extForest c b) = 1 := by
  have htar : ∀ g, N.graph.target g = v → extForest c b g = ∅ := fun g hg =>
    extForest_of_not c fun hk => hv (hg ▸ hk.2)
  rw [allocationFactor_choiceMetric hρ θ c ⟨v, hvr⟩, arrivingForest_extForest_of_not c t hv, ite_eq_left]
  exact ⟨htar _ (c ⟨v, hvr⟩).property, fun g hg _ => htar g hg⟩

/-- **On forests that vanish off its arcs, the weight of a history is that of the network of the
choice.** -/
theorem historyWeight_extForest (hρ : 0 ≤ ρ) (θ : MetricData E)
    (b t : {f // N.IsKeptArc c f} → Finset (Finset X)) :
    historyWeight N (N.choiceMetric θ c) ρ (extForest c b) (extForest c t) =
      historyWeight (N.choiceNetwork hN c x₀) (N.choiceNetworkMetric θ c) ρ b t := by
  unfold historyWeight
  congr 1
  · symm
    refine Finset.prod_of_injOn Subtype.val Subtype.val_injective.injOn ?_ ?_ ?_
    · intro v hv
      exact mem_coe.2 ((mem_erase_root_iff N).2 fun h =>
        (mem_erase_root_iff (N.choiceNetwork hN c x₀)).1 (mem_coe.1 hv) (Subtype.ext h))
    · intro v hv hni
      have hkept : ¬ N.IsKeptVertex c v := fun hk => hni ⟨⟨v, hk⟩, mem_coe.2
        ((mem_erase_root_iff (N.choiceNetwork hN c x₀)).2 fun h =>
          (mem_erase_root_iff N).1 hv (congrArg Subtype.val h)), rfl⟩
      exact allocationFactor_extForest_of_not c hρ θ t b hkept ((mem_erase_root_iff N).1 hv)
    · intro v hv
      rw [arrivingForest_extForest hN c x₀ t v]
      exact (allocationFactor_extForest hN c x₀ hρ θ _ b
        ((mem_erase_root_iff (N.choiceNetwork hN c x₀)).1 hv)).symm
  · symm
    refine Fintype.prod_of_injective Subtype.val Subtype.val_injective _ _ ?_ fun f => ?_
    · intro f hf
      have hk : ¬ N.IsKeptArc c f := fun hk => hf ⟨⟨f, hk⟩, rfl⟩
      rw [extForest_of_not c hk, extForest_of_not c hk,
        kingmanTransition_of_card_roots_le_one isForest_empty (by simp), ite_eq_left rfl]
    · rw [extForest_val, extForest_val]
      rfl

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- `Finset.mem_univ`, for an instance given by unification. -/
theorem mem_univ_of {α : Type*} (i : Fintype α) (x : α) : x ∈ @Finset.univ α i := @Finset.mem_univ α i x

include hN in
/-- A history of nonzero weight in the parameters of a parent choice carries nothing off the arcs of its
network: the deleted arcs have inheritance `0`, and a lineage on an arc came up from a taxon below it. -/
theorem eq_empty_of_historyWeight_ne_zero {θ : MetricData E}
    {bot top : E → Finset (Finset X)} (h : historyWeight N (N.choiceMetric θ c) ρ bot top ≠ 0) {f : E}
    (hf : ¬ N.IsKeptArc c f) : bot f = ∅ ∧ top f = ∅ := by
  rw [historyWeight_eq_injWeight hN] at h
  have hinj := validInj_taxaInj (N := N) (univ : Finset X)
  have hW := downClosed_erase_root (N := N) hN
  have hf' : N.graph.target f ∈ univ.erase N.root :=
    mem_erase.2 ⟨target_ne_root hN f, mem_univ _⟩
  have hFr := frontier_of_prod_ne_zero hN hinj hW h
  have hl : ∀ x, x ∉ lineages (top f) := fun x hx => by
    obtain ⟨hfD, u, hu, hxu⟩ := notMem_and_reachesOff_of_mem_lineages_top hN hinj
      (D := N.deletedArcs c) (fun g hg => choiceMetric_inheritance_of_mem θ hg) hW h hf' hx
    obtain ⟨-, rfl⟩ := mem_lineages_taxaInj.1 hxu
    exact hf ⟨hfD, x, hu⟩
  have htop : top f = ∅ := eq_empty_of_forall_notMem fun A hA => by
    obtain ⟨x, hx⟩ := (hFr.good_top f hf').1.1 A hA
    exact hl x (mem_lineages.2 ⟨A, hA, hx⟩)
  have hK : kingmanTransition ((N.choiceMetric θ c).length f) (bot f) (top f) ≠ 0 :=
    prod_ne_zero_iff.1 (right_ne_zero_of_mul (prod_ne_zero_iff.1 h _ hf')) f (mem_arcsInto.2 rfl)
  refine ⟨?_, htop⟩
  have := (kingmanTransition_support_good (hFr.good_bot f hf') hK).2.1
  rw [htop] at this
  exact subset_empty.1 this

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- Forests vanishing off the arcs of the network of a choice are extended from those arcs. -/
theorem eq_extForest_of_forall [DecidableEq X] {bot : E → Finset (Finset X)}
    (h : ∀ f, ¬ N.IsKeptArc c f → bot f = ∅) : bot = extForest c fun f => bot f.val := by
  funext f
  by_cases hf : N.IsKeptArc c f
  · exact (extForest_val (b := fun f => bot f.val) c ⟨f, hf⟩).symm
  · rw [h f hf, extForest_of_not c hf]

/-- **The gene tree distribution in the parameters of a parent choice is that of its network.** -/
theorem geneTreeDist_choiceNetwork (hρ : 0 ≤ ρ) (θ : MetricData E) (G : Finset (Finset X)) :
    geneTreeDist (N.choiceNetwork hN c x₀) (N.choiceNetworkMetric θ c) ρ G =
      geneTreeDist N (N.choiceMetric θ c) ρ G := by
  unfold geneTreeDist
  refine Finset.sum_of_injOn (extForest c) (extForest_injective c).injOn (fun _ _ => mem_coe.2 (mem_univ _))
    (fun bot _ hbot => ?_) fun b _ => ?_
  · refine sum_eq_zero fun top _ => ?_
    by_contra hne
    have hw := left_ne_zero_of_mul hne
    exact hbot ⟨_, mem_coe.2 (mem_univ_of _ _), (eq_extForest_of_forall c fun f hf =>
      (eq_empty_of_historyWeight_ne_zero hN c hw hf).1).symm⟩
  · refine Finset.sum_of_injOn (extForest c) (extForest_injective c).injOn
      (fun _ _ => mem_coe.2 (mem_univ _)) (fun top _ htop => ?_) fun t _ => ?_
    · by_contra hne
      have hw := left_ne_zero_of_mul hne
      exact htop ⟨_, mem_coe.2 (mem_univ_of _ _), (eq_extForest_of_forall c fun f hf =>
        (eq_empty_of_historyWeight_ne_zero hN c hw hf).2).symm⟩
    · rw [historyWeight_extForest hN c x₀ hρ θ b t]
      exact congrArg (_ * ·) (congrArg (kingmanAbsorption · G)
        (arrivingForest_extForest hN c x₀ t (N.choiceNetwork hN c x₀).root).symm)

/-- The concordance factors in the parameters of a parent choice are those of its network. -/
theorem nmscCF_choiceNetwork (hρ : 0 ≤ ρ) (θ : MetricData E) (s : QuartetTree X) :
    nmscCF (N.choiceNetwork hN c x₀) (N.choiceNetworkMetric θ c) ρ s =
      nmscCF N (N.choiceMetric θ c) ρ s := by
  unfold nmscCF
  simp only [geneTreeDist_choiceNetwork hN c x₀ hρ θ]

end Pruned

/-! ### On a rooted tree

The argument of `Phylogenetics.NMSC.TreeCF`, on a network with no reticulations, with the lower
bound on the difference of the concordance factors in terms of one arc on the path between the cherries of
the quartet tree. The fork of that file may be above that arc. -/

section TreeNetwork

open NMSC

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {μ : MetricData E} {ρ : ℝ}

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- In a rooted tree, every root path to a vertex below an arc uses the arc. -/
theorem not_avoidingReach_of_tree (hN : N.IsPhylogenetic)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) {e : E} {u : V}
    (hu : N.graph.Reaches (N.graph.target e) u) : ¬ N.AvoidingReach e N.root u := by
  induction hu with
  | refl =>
    intro hav
    rcases Relation.ReflTransGen.cases_tail hav with h | ⟨y, -, f, hfe, -, hft⟩
    · exact target_ne_root_of_isPhylogenetic hN e h
    · exact hfe (htree _ _ hft)
  | @tail a b _ hab ih =>
    obtain ⟨g, hgs, hgt⟩ := hab
    intro hav
    rcases Relation.ReflTransGen.cases_tail hav with h | ⟨y, hy, f, -, hfs, hft⟩
    · exact target_ne_root_of_isPhylogenetic hN g (hgt.trans h)
    · have hfg := htree _ _ (hft.trans hgt.symm)
      subst hfg
      exact ih (hgs ▸ hfs ▸ hy)

omit [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] in
/-- **The fork above an arc.** Let the taxa of the nonempty set `Q` not be below the arc `g₀`. Going up from
`g₀`, there is a first arc `g` whose source has a taxon `c` of `Q` below it, along another arc `f`. -/
theorem exists_fork [Fintype X] [DecidableEq X] (hN : N.IsPhylogenetic) {Q : Finset X} (hQ : Q.Nonempty)
    (g₀ : E) (h₀ : ∀ x ∈ Q, ¬ N.IsBelow g₀ x) :
    ∃ g f c, N.graph.source f = N.graph.source g ∧
      (g = g₀ ∨ N.graph.Reaches (N.graph.target g) (N.graph.source g₀)) ∧
      (∀ x ∈ Q, ¬ N.IsBelow g x) ∧ c ∈ Q ∧ N.IsBelow f c := by
  have : Finite E := hN.finite_arcs
  have key : ∀ u g, N.graph.source g = u → (∀ x ∈ Q, ¬ N.IsBelow g x) →
      (g = g₀ ∨ N.graph.Reaches (N.graph.target g) (N.graph.source g₀)) →
      ∃ g f c, N.graph.source f = N.graph.source g ∧
        (g = g₀ ∨ N.graph.Reaches (N.graph.target g) (N.graph.source g₀)) ∧
        (∀ x ∈ Q, ¬ N.IsBelow g x) ∧ c ∈ Q ∧ N.IsBelow f c := by
    intro u
    induction u using (wellFounded_transGen_adj hN).induction with
    | _ u ih =>
      intro g hgu hgQ hg
      by_cases hex : ∃ c ∈ Q, N.graph.Reaches u (N.leaf c)
      · obtain ⟨c, hc, hr⟩ := hex
        rcases Relation.ReflTransGen.cases_head hr with h | ⟨w, ⟨f, hfs, hft⟩, hw⟩
        · exact absurd (hgu.trans h) ((N.graph.outdegree_eq_zero_iff _).1 ((hN.leaves _).2 ⟨c, rfl⟩) g)
        · refine ⟨g, f, c, hfs.trans hgu.symm, hg, hgQ, hc, ?_⟩
          rw [RootedNetwork.IsBelow, hft]
          exact hw
      · have hne : u ≠ N.root := by
          rintro rfl
          obtain ⟨c, hc⟩ := hQ
          exact hex ⟨c, hc, hN.root_reaches _⟩
        have : ∃ e, N.graph.target e = u := (N.graph.one_le_indegree_iff u).1 (hN.nonroot_indegree u hne)
        obtain ⟨g₁, hg₁⟩ := this
        refine ih _ (.single ⟨g₁, rfl, hg₁⟩) g₁ rfl (fun x hx hb => hex ⟨x, hx, hg₁ ▸ hb⟩) (Or.inr ?_)
        rw [hg₁]
        rcases hg with rfl | hr
        · rw [hgu]
          exact .refl
        · exact Relation.ReflTransGen.head ⟨g, hgu, rfl⟩ hr
  exact key _ g₀ rfl h₀ (Or.inl rfl)

/-- With the lineages of the cherry `P` at the source of the arc `e`, no outcome favours an alternative:
go up from `e` to the fork. -/
theorem cherryMass_hubInj_le_of_tree (hN : N.IsPhylogenetic) (hμ : N.IsMetric μ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) (s : QuartetTree X) {P : Finset X}
    (hP : P ∈ s.val) {e : E} (hbP : ∀ x ∈ P, N.IsBelow e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    cherryMass N μ ρ (hubInj N s.taxa P (N.graph.source e)) r ≤
      cherryMass N μ ρ (hubInj N s.taxa P (N.graph.source e)) s := by
  have hQne : (s.taxa \ P).Nonempty := card_pos.1 (by rw [s.card_of_mem (s.sdiff_mem hP)]; omega)
  have hnQ : ∀ x ∈ s.taxa \ P, ¬ N.IsBelow e x := fun x hx =>
    hn x (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2
  obtain ⟨g, f, c, hfs, hge, hgQ, hcQ, hcf⟩ := exists_fork hN hQne e hnQ
  obtain ⟨hcq, hcP⟩ := mem_sdiff.1 hcQ
  have hdf : ∀ x ∈ s.taxa, x ∉ P → N.IsBelow f x → N.Dominates f x := fun x _ _ hb =>
    not_avoidingReach_of_tree hN htree hb
  rcases hge with rfl | hw
  · exact cherryMass_hubInj_le hN hμ hρ s hP hfs hcq hcP hcf hdf hr
  set w := N.graph.source e with hwdef
  have hv := validInj_hubInj (N := N) s.taxa P w
  have hdom : DominatedInj N g (hubInj N s.taxa P w) := fun u hu _ =>
    not_avoidingReach_of_tree hN htree (mem_belowSet.1 hu)
  have hwB : w ∈ belowSet N g := mem_belowSet.2 hw
  have hnotQ : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow g x := fun x hx hxP => hgQ x (mem_sdiff.2 ⟨hx, hxP⟩)
  have hbg : ∀ x ∈ P, N.IsBelow g x := fun x hx =>
    hw.trans (Relation.ReflTransGen.head ⟨e, rfl, rfl⟩ (hbP x hx))
  have hpos := belowMass_pos (N := N) (X := X) g
  refine le_of_mul_le_mul_left ?_ hpos
  rw [belowMass_mul_cherryMass hN hμ hρ hv hdom r, belowMass_mul_cherryMass hN hμ hρ hv hdom s]
  refine sum_le_sum fun bot _ => sum_le_sum fun top _ => ?_
  by_cases hz : ∏ u ∈ belowSet N g, vertexWeight N μ ρ (hubInj N s.taxa P w) u bot top = 0
  · simp [hz]
  refine mul_le_mul_of_nonneg_left ?_ (prod_vertexWeight_nonneg hμ hρ _ _ _ _)
  have hgood := good_top_of_prod_ne_zero hN hv hz
  have hlin : ∀ x, x ∈ lineages (top g) ↔ x ∈ P := fun x => by
    refine (lineages_top_of_prod_ne_zero hN hv hdom hz x).trans ⟨?_, fun hx => ⟨w, hwB, ?_⟩⟩
    · rintro ⟨u, hu, hx⟩
      rcases (mem_lineages_hubInj x).1 hx with ⟨hxq, rfl⟩ | ⟨-, hxP⟩
      · exact absurd (mem_belowSet.1 hu) (hnotQ x (mem_sdiff.1 hxq).1 (mem_sdiff.1 hxq).2)
      · exact hxP
    · exact (mem_lineages_hubInj x).2 (Or.inr ⟨rfl, hx⟩)
  have heq : liftInj N g (hubInj N s.taxa P w) (top g) = liftInj N g (taxaInj N s.taxa) (top g) := by
    funext u
    unfold liftInj
    by_cases hu : u ∈ belowSet N g
    · simp [hu]
    · simp only [hu, ↓reduceIte]
      congr 1
      have huw : u ≠ w := fun h => hu (h ▸ hwB)
      unfold hubInj
      rw [ite_eq_right huw, union_empty]
      ext A
      simp only [taxaInj, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨x, ⟨hx, hxu⟩, rfl⟩
        exact ⟨x, ⟨(mem_sdiff.1 hx).1, hxu⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxu⟩, rfl⟩
        refine ⟨x, ⟨mem_sdiff.2 ⟨hx, fun hxP => hu ?_⟩, hxu⟩, rfl⟩
        exact hxu ▸ mem_belowSet.2 (hbg x hxP)
  rw [heq]
  exact cherryMass_lift_le hN hμ hρ s hP hfs hbg hnotQ hcq hcP hcf hdf hgood hlin hr

/-- The forest `F` of the lineages of the cherry `P` at the top of the arc `e`: no outcome favours an
alternative. -/
theorem cherryMass_lift_le_of_tree (hN : N.IsPhylogenetic) (hμ : N.IsMetric μ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) (s : QuartetTree X) {P : Finset X}
    (hP : P ∈ s.val) {e : E} (hbP : ∀ x ∈ P, N.IsBelow e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {F : Finset (Finset X)} (hgood : IsGoodForest F) (hlin : ∀ x, x ∈ lineages F ↔ x ∈ P)
    {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    cherryMass N μ ρ (liftInj N e (taxaInj N s.taxa) F) r ≤
      cherryMass N μ ρ (liftInj N e (taxaInj N s.taxa) F) s := by
  by_cases h2 : ∃ C ∈ F, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    have hCP : C = P := eq_of_subset_of_card_le
      (fun x hx => (hlin x).1 (mem_lineages.2 ⟨C, hC, hx⟩)) (by rw [s.card_of_mem hP, hC2])
    have hl : ValidInj (liftInj N e (taxaInj N s.taxa) F) :=
      validInj_liftInj (validInj_taxaInj _) hgood fun x hx => by
        have hxP := (hlin x).1 hx
        exact (exists_mem_below_taxaInj x).2 ⟨s.subset_taxa hP hxP, hbP x hxP⟩
    have hmem : C ∈ liftInj N e (taxaInj N s.taxa) F (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hC)
    obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hμ hρ hl hmem (hCP ▸ hP) hr
    rw [h0, h1]
    exact zero_le_one
  · have hF : F = P.image fun x => ({x} : Finset X) := by
      have := hgood.eq_singletons h2
      rwa [show lineages F = P from Finset.ext hlin] at this
    have hlift := liftInj_hubInj (q := s.taxa) (T := ∅) (L := P) (v := N.graph.source e) hN rfl hbP
      (fun x hxq _ hxP => hn x hxq hxP)
    rw [hubInj_empty, empty_union] at hlift
    rw [hF, hlift]
    exact cherryMass_hubInj_le_of_tree hN hμ hρ htree s hP hbP hn hr

/-- Two lineages below the arc `e` have merged at its top with probability at least `1 - exp (-ℓ e)`. -/
theorem one_sub_exp_mul_belowMass_le_of_tree (hN : N.IsPhylogenetic) (hμ : N.IsMetric μ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) (s : QuartetTree X) {P : Finset X}
    (hP : P ∈ s.val) {e : E} (hbP : ∀ x ∈ P, N.IsBelow e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) :
    (1 - Real.exp (-μ.length e)) * belowMass X N e ≤
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ u ∈ belowSet N e, vertexWeight N μ ρ (taxaInj N s.taxa) u bot top) *
          (if P ∈ top e then 1 else 0) := by
  have hinj := validInj_taxaInj (N := N) s.taxa
  have hP2 := s.card_of_mem hP
  have hB : (0 : ℝ) < Fintype.card (Finset (Finset X)) := by exact_mod_cast Fintype.card_pos
  let φ : (E → Finset (Finset X)) → ℝ := fun top => if P ∈ top e then 1 else 0
  have hD₀ := downClosed_belowSet_erase (N := N) hN e
  have hdel : N.IsDeletion (∅ : Set E) := isDeletion_empty hN
  have hd : ∀ x ∈ P, N.DominatesOff ∅ e x := fun x hx =>
    dominatesOff_empty_iff.2 (not_avoidingReach_of_tree hN htree (hbP x hx))
  have hQ : ∀ x ∈ s.taxa \ P, ¬ N.IsBelowOff ∅ e x := fun x hx h =>
    hn x (mem_sdiff.1 hx).1 (mem_sdiff.1 hx).2 (isBelowOff_empty_iff.1 h)
  have hte : N.IsTreeArc e := by
    refine (N.graph.indegree_eq_one_iff _).2 ⟨e, fun f => ⟨fun h => htree _ _ h, fun h => h ▸ rfl⟩⟩
  have h1 : μ.inheritance e = 1 := hμ.2.2.1 e hte
  have h0 : ∀ f, N.graph.target f = N.graph.target e → f ≠ e → μ.inheritance f = 0 :=
    fun f hf hne => absurd (htree _ _ hf) hne
  have hge := le_sum_of_le_vertexKernel (θ := μ) (ρ := ρ) (c₀ := 1 - Real.exp (-μ.length e)) hN
    hμ.isNormalized hρ.1 hinj hD₀
    (fun h => root_notMem_belowSet hN e (mem_of_mem_erase h)) (notMem_erase _ _)
    (fun f hf => target_mem_belowSet_erase hN hf) φ
    (fun bot top => prod_vertexWeight_nonneg hμ hρ _ _ _ _)
    (fun bot top hg => by
      have hF := (frontier_of_prod_ne_zero hN hinj hD₀ hg).good_arriving hinj (notMem_erase _ _)
        fun f hf => target_mem_belowSet_erase hN hf
      have hlin := lineages_arriving_eq hN hdel (fun _ h => absurd h (Set.notMem_empty _))
        (Set.notMem_empty _) (s.subset_taxa hP) hd hQ hg
      have hψ : (fun t => φ (overwrite (arcsInto N (N.graph.target e)) top t)) =
          fun t => if P ∈ t e then 1 else 0 := by
        funext t
        simp only [φ, overwrite_of_mem (mem_arcsInto.2 rfl : e ∈ arcsInto N (N.graph.target e))]
      rw [hψ]
      exact one_sub_exp_mul_le_vertexKernel hρ.1 rfl h1 h0 hF hlin hP2)
  rw [insert_erase (target_mem_belowSet e)] at hge
  unfold belowMass
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  exact hge.trans_eq (mul_comm _ _)

/-- **On a rooted tree the split of an arc has the largest concordance factor**, by at least the
probability that two lineages coalesce on the arc: given the forest at the top of the arc, a cherry there
decides the quartet tree, and otherwise no outcome favours an alternative. -/
theorem one_sub_exp_le_sub_nmscCF_of_tree (hN : N.IsPhylogenetic) (hμ : N.IsMetric μ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) (s : QuartetTree X) {P : Finset X}
    (hP : P ∈ s.val) {e : E} (hbP : ∀ x ∈ P, N.IsBelow e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x)
    {r : QuartetTree X} (hr : r ∈ s.alternatives) :
    1 - Real.exp (-μ.length e) ≤ nmscCF N μ ρ s - nmscCF N μ ρ r := by
  rw [nmscCF_eq_cherryMass hN hμ hρ r, nmscCF_eq_cherryMass hN hμ hρ s,
    (QuartetTree.mem_alternatives.1 hr).1]
  have hv := validInj_taxaInj (N := N) s.taxa
  have hdom : DominatedInj N e (taxaInj N s.taxa) := fun u hu _ =>
    not_avoidingReach_of_tree hN htree (mem_belowSet.1 hu)
  have hPq := s.subset_taxa hP
  have hpos := belowMass_pos (N := N) (X := X) e
  refine le_of_mul_le_mul_right ?_ hpos
  refine (one_sub_exp_mul_belowMass_le_of_tree hN hμ hρ htree s hP hbP hn).trans ?_
  rw [mul_comm (_ - _), mul_sub, belowMass_mul_cherryMass hN hμ hρ hv hdom r,
    belowMass_mul_cherryMass hN hμ hρ hv hdom s, ← sum_sub_distrib]
  refine sum_le_sum fun bot _ => ?_
  rw [← sum_sub_distrib]
  refine sum_le_sum fun top _ => ?_
  rw [← mul_sub]
  by_cases hz : ∏ u ∈ belowSet N e, vertexWeight N μ ρ (taxaInj N s.taxa) u bot top = 0
  · simp [hz]
  refine mul_le_mul_of_nonneg_left ?_ (prod_vertexWeight_nonneg hμ hρ _ _ _ _)
  have hgood := good_top_of_prod_ne_zero hN hv hz
  have hlin : ∀ x, x ∈ lineages (top e) ↔ x ∈ P := fun x =>
    (lineages_top_of_prod_ne_zero hN hv hdom hz x).trans <|
      (exists_mem_below_taxaInj x).trans
        ⟨fun h => by
          by_contra hxP
          exact hn x h.1 hxP h.2, fun h => ⟨hPq h, hbP x h⟩⟩
  by_cases hPt : P ∈ top e
  · have hl : ValidInj (liftInj N e (taxaInj N s.taxa) (top e)) :=
      validInj_liftInj hv hgood fun x hx => (lineages_top_of_prod_ne_zero hN hv hdom hz x).1 hx
    have hmem : P ∈ liftInj N e (taxaInj N s.taxa) (top e) (N.graph.source e) := by
      unfold liftInj
      exact mem_union_right _ (by simpa using hPt)
    obtain ⟨h0, h1⟩ := cherryMass_of_mem_val hN hμ hρ hl hmem hP hr
    rw [h0, h1, ite_eq_left hPt]
    norm_num
  · rw [ite_eq_right hPt]
    exact sub_nonneg.2 (cherryMass_lift_le_of_tree hN hμ hρ htree s hP hbP hn hgood hlin hr)

end TreeNetwork

/-! ### Common inheritance

Going through the displayed trees, the concordance factors at `ρ = 1` compare as on trees. -/

section Common

open NMSC

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E}

/-- **In the parameters of a parent choice, an arc separating the cherry `P` of `s` from its other two taxa
makes `s` the most probable**, when all lengths are positive. The arc is kept, whatever the choice, and a
deletion may only leave more arcs on the path between the cherries. -/
theorem one_sub_exp_le_sub_nmscCF_choiceMetric (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hℓ : ∀ f, 0 < θ.length f) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) :
    1 - Real.exp (-θ.length e) ≤
      nmscCF N (N.choiceMetric θ c) 1 s - nmscCF N (N.choiceMetric θ c) 1 r := by
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [s.card_of_mem hP]; omega)
  have hdel := isDeletion_deletedArcs hN c
  have hb : ∀ x ∈ P, e ∉ N.deletedArcs c ∧ N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x) :=
    fun x hx => (hd x hx).dominatesOff.isBelowOff hN hdel
  have he : N.IsKeptArc c e := ⟨(hb a ha).1, a, (hb a ha).2⟩
  have hM := isPhylogenetic_choiceNetwork hN c a
  rw [← nmscCF_choiceNetwork hN c a zero_le_one θ s, ← nmscCF_choiceNetwork hN c a zero_le_one θ r]
  refine one_sub_exp_le_sub_nmscCF_of_tree hM (isMetric_choiceNetworkMetric hN c a fun f _ => hℓ f)
    ⟨zero_le_one, le_rfl⟩ (fun f g h => eq_of_target_choiceNetwork hN c a h) s hP (e := ⟨e, he⟩)
    (fun x hx => reaches_choiceNetwork hN c a _ _ (hb x hx).2) (fun x hx hxP hb' => hn x hx hxP ?_) hr
  exact (reachesOff_of_reaches_choiceNetwork hN c a hb').reaches

/-- The bound at `ρ = 1`, when all lengths are positive. -/
theorem one_sub_exp_le_sub_nmscCF_rho_one_of_pos (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (hℓ : ∀ f, 0 < θ.length f) (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) :
    1 - Real.exp (-θ.length e) ≤ nmscCF N θ 1 s - nmscCF N θ 1 r := by
  rw [nmscCF_rho_one hN hθ.isNormalized s, nmscCF_rho_one hN hθ.isNormalized r, ← sum_sub_distrib]
  simp only [← mul_sub]
  calc 1 - Real.exp (-θ.length e)
      = ∑ c : N.ParentChoice, N.choiceWeight θ c * (1 - Real.exp (-θ.length e)) := by
        rw [← Finset.sum_mul, sum_choiceWeight hN hθ.isNormalized, one_mul]
    _ ≤ _ := sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
        (one_sub_exp_le_sub_nmscCF_choiceMetric hN c hℓ s hP hd hn hr) (choiceWeight_nonneg hθ c)

/-- The parameters `θ` with `ε` added to all the lengths. -/
def addLength (θ : MetricData E) (ε : ℝ) : MetricData E where
  length f := θ.length f + ε
  inheritance := θ.inheritance

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype E] in
theorem addLength_zero (θ : MetricData E) : addLength θ 0 = θ := by
  cases θ
  simp [addLength]

/-- **At `ρ = 1`, an arc separating the cherry `P` of `s` from its other two taxa makes `s` the most
probable, by at least the probability that two lineages coalesce on the arc.** The parameters may have
length zero on any arc, and inheritance zero on hybrid arcs. For positive lengths the bound averages over
the displayed trees; the lengths then go down to those of `θ`, by continuity.

The bound on a tree conditions at the arc `e` (`one_sub_exp_le_sub_nmscCF_of_tree`), and a hybrid arc of length zero
becomes a tree arc on a displayed tree, hence the limit. -/
theorem one_sub_exp_le_sub_nmscCF_rho_one (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E}
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) :
    1 - Real.exp (-θ.length e) ≤ nmscCF N θ 1 s - nmscCF N θ 1 r := by
  have hℓ : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (addLength θ ε).length f) Set.univ := fun f =>
    analyticOnNhd_const.add analyticOnNhd_id
  have hγ : ∀ f, AnalyticOnNhd ℝ (fun ε : ℝ => (addLength θ ε).inheritance f) Set.univ := fun f =>
    analyticOnNhd_const
  have hcont : ∀ t : QuartetTree X, Continuous fun ε : ℝ => nmscCF N (addLength θ ε) 1 t := fun t =>
    continuousOn_univ.1 (analyticOnNhd_nmscCF N (θ := addLength θ) 1 hℓ hγ t).continuousOn
  have hlim : Filter.Tendsto (fun ε : ℝ => nmscCF N (addLength θ ε) 1 s - nmscCF N (addLength θ ε) 1 r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (nmscCF N θ 1 s - nmscCF N θ 1 r)) := by
    have he : nmscCF N (addLength θ 0) 1 s - nmscCF N (addLength θ 0) 1 r =
        nmscCF N θ 1 s - nmscCF N θ 1 r := by rw [addLength_zero]
    rw [← he]
    exact ((hcont s).sub (hcont r)).tendsto 0 |>.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hw : N.IsWeakMetric (addLength θ ε) :=
    ⟨fun f => add_nonneg (hθ.1 f) hε'.le, hθ.2.1, hθ.2.2⟩
  have h := one_sub_exp_le_sub_nmscCF_rho_one_of_pos hN hw
    (fun f => add_pos_of_nonneg_of_pos (hθ.1 f) hε') s hP hd hn hr
  refine le_trans ?_ h
  have : Real.exp (-(addLength θ ε).length e) ≤ Real.exp (-θ.length e) :=
    Real.exp_le_exp.2 (by simp only [addLength]; linarith)
  linarith

/-- **At `ρ = 1`, an arc of positive length separating the cherry `P` of `s` from its other two taxa makes
`s` strictly the most probable.** -/
theorem nmscCF_lt_rho_one_of_separates (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ)
    (s : QuartetTree X) {P : Finset X} (hP : P ∈ s.val) {e : E} (hℓ : 0 < θ.length e)
    (hd : ∀ x ∈ P, N.Dominates e x) (hn : ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x) {r : QuartetTree X}
    (hr : r ∈ s.alternatives) : nmscCF N θ 1 r < nmscCF N θ 1 s := by
  have h := one_sub_exp_le_sub_nmscCF_rho_one hN hθ s hP hd hn hr
  have : Real.exp (-θ.length e) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

omit [Fintype V] [Fintype E] in
/-- A quartet tree that the tree of blobs displays is separated by a bridge. -/
theorem exists_isBridge_separating (hN : N.IsPhylogenetic) {s : QuartetTree X}
    (hs : Displays (treeOfBlobs N) s) :
    ∃ P ∈ s.val, ∃ e, N.graph.underlying.IsBridge e ∧ (∀ x ∈ P, N.Dominates e x) ∧
      ∀ x ∈ s.taxa, x ∉ P → ¬ N.IsBelow e x := by
  obtain ⟨A, hA, hAs⟩ := hs
  obtain ⟨e, S, hS, hSA⟩ : N.HasCutSplit (A : Set X) := (mem_filter.1 hA).2.2.2
  have hmem : ∀ x, N.leaf x ∈ S ↔ x ∈ A := fun x => by
    have := Set.ext_iff.1 hSA x
    simpa using this
  have hanc : ∀ f, f ∈ N.ancestralArcs Set.univ := fun f => by
    obtain ⟨x, hx⟩ := exists_reaches_leaf hN (N.graph.target f)
    exact ⟨x, Set.mem_univ x, hx⟩
  rcases (hS e).2 rfl with ⟨hs₁, ht₁⟩ | ⟨ht₁, hs₁⟩
  · obtain ⟨-, hdom, hnb⟩ := separates_of_crossing (Y := Set.univ) (T := Sᶜ) hN (hanc e)
      (fun f _ hfe hc => hfe ((hS f).1 ((N.graph.crosses_compl f S).1 hc))) ht₁ (not_not.2 hs₁)
    refine ⟨s.taxa \ (A ∩ s.taxa), s.sdiff_mem hAs, e, (N.graph.isBridge_iff e).2 ⟨S, hS⟩, fun x hx => ?_, fun x hx hxP => ?_⟩
    · refine hdom x (Set.mem_univ x) fun h => (mem_sdiff.1 hx).2 ?_
      exact mem_inter.2 ⟨(hmem x).1 h, (mem_sdiff.1 hx).1⟩
    · refine hnb x (Set.mem_univ x) (not_not.2 ((hmem x).2 ?_))
      by_contra hxA
      exact hxP (mem_sdiff.2 ⟨hx, fun h => hxA (mem_inter.1 h).1⟩)
  · obtain ⟨-, hdom, hnb⟩ := separates_of_crossing (Y := Set.univ) (T := S) hN (hanc e)
      (fun f _ hfe hc => hfe ((hS f).1 hc)) ht₁ hs₁
    refine ⟨A ∩ s.taxa, hAs, e, (N.graph.isBridge_iff e).2 ⟨S, hS⟩, fun x hx => ?_, fun x hx hxP => ?_⟩
    · exact hdom x (Set.mem_univ x) ((hmem x).2 (mem_inter.1 hx).1)
    · refine hnb x (Set.mem_univ x) fun h => hxP (mem_inter.2 ⟨(hmem x).1 h, hx⟩)

end Common

/-! ### Parameters on the boundary

The identities of the network multispecies coalescent that are proved for valid parameters persist at the
boundary: a concordance factor is continuous in the parameters. -/

section Boundary

open NMSC

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E}

variable (N) in
/-- A segment from `θ` into the valid parameters: add `t` to the lengths, and move the inheritance
towards the uniform one. -/
def approxMetric (θ : MetricData E) (t : ℝ) : MetricData E where
  length f := θ.length f + t
  inheritance f := (1 - t) * θ.inheritance f + t * (N.graph.indegree (N.graph.target f) : ℝ)⁻¹

omit [Fintype V] [Fintype X] [DecidableEq X] [Fintype E] in
theorem approxMetric_zero (θ : MetricData E) : N.approxMetric θ 0 = θ := by
  cases θ
  simp [approxMetric]

omit [Fintype V] [Fintype X] [DecidableEq X] in
/-- The segment is in the valid parameters at once. -/
theorem isMetric_approxMetric (hθ : N.IsWeakMetric θ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    N.IsMetric (N.approxMetric θ t) := by
  have hpos : ∀ e, 0 < (N.graph.indegree (N.graph.target e) : ℝ) := fun e => by
    exact_mod_cast (N.graph.one_le_indegree_iff _).2 ⟨e, rfl⟩
  refine ⟨fun e _ => add_pos_of_nonneg_of_pos (hθ.1 e) h0,
    fun e _ => add_nonneg (hθ.1 e) h0.le, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · change (1 - t) * θ.inheritance e + t * (N.graph.indegree (N.graph.target e) : ℝ)⁻¹ = 1
    rw [hθ.2.2.1 e he, he]
    norm_num
  · have h2 := hθ.2.1 e he
    have h3 : 0 ≤ (1 - t) * θ.inheritance e := mul_nonneg (by linarith) h2
    have h4 : 0 < t * (N.graph.indegree (N.graph.target e) : ℝ)⁻¹ := mul_pos h0 (inv_pos.2 (hpos e))
    exact add_pos_of_nonneg_of_pos h3 h4
  · have hsum := hθ.2.2.2 v hv
    have hc : (#(arcsInto N v) : ℝ) = (N.graph.indegree v : ℝ) := by
      rw [indegree_eq_card]
    have hne : (N.graph.indegree v : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ N.graph.indegree v := by exact_mod_cast hv
      linarith
    have hterm : ∀ e, (if N.graph.target e = v then (N.approxMetric θ t).inheritance e else 0) =
        (1 - t) * (if N.graph.target e = v then θ.inheritance e else 0) +
          t * (N.graph.indegree v : ℝ)⁻¹ * (if N.graph.target e = v then 1 else 0) := fun e => by
      by_cases he : N.graph.target e = v
      · simp only [he, ↓reduceIte, approxMetric]
        ring
      · simp [he]
    simp only [hterm]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum, ← sum_filter]
    have hcount : ∑ e with N.graph.target e = v, (1 : ℝ) = (N.graph.indegree v : ℝ) := by
      rw [sum_const, nsmul_eq_mul, mul_one]
      exact hc
    rw [hcount]
    field_simp
    ring

/-- An identity between two concordance factors at all valid parameters holds at the boundary. -/
theorem nmscCF_eq_of_forall_isMetric (hθ : N.IsWeakMetric θ) (ρ : ℝ) (s s' : QuartetTree X)
    (h : ∀ θ', N.IsMetric θ' → nmscCF N θ' ρ s = nmscCF N θ' ρ s') :
    nmscCF N θ ρ s = nmscCF N θ ρ s' := by
  have hℓ : ∀ f, AnalyticOnNhd ℝ (fun t : ℝ => (N.approxMetric θ t).length f) Set.univ := fun f =>
    analyticOnNhd_const.add analyticOnNhd_id
  have hγ : ∀ f, AnalyticOnNhd ℝ (fun t : ℝ => (N.approxMetric θ t).inheritance f) Set.univ := fun f =>
    ((analyticOnNhd_const.sub analyticOnNhd_id).mul analyticOnNhd_const).add
      (analyticOnNhd_id.mul analyticOnNhd_const)
  have hcont : ∀ r : QuartetTree X, Filter.Tendsto (fun t : ℝ => nmscCF N (N.approxMetric θ t) ρ r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (nmscCF N θ ρ r)) := fun r => by
    have hc : Continuous fun t : ℝ => nmscCF N (N.approxMetric θ t) ρ r :=
      continuousOn_univ.1 (analyticOnNhd_nmscCF N (θ := N.approxMetric θ) ρ hℓ hγ r).continuousOn
    have h0 := hc.tendsto 0
    simp only [approxMetric_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique_of_eventuallyEq (hcont s) (hcont s') ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact h _ (isMetric_approxMetric hθ ht.1 ht.2.le)

/-- **Exchangeability of the network multispecies coalescent at the boundary of the parameters**: some
inheritance may vanish, and any length. -/
theorem exchangeability_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {ρ : ℝ}
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1) : CutExchangeable N (nmscCF N θ ρ) := fun s s' a a' ha ha' hs' hex =>
  nmscCF_eq_of_forall_isMetric hθ ρ s s' fun _ hθ' =>
    NMSC.exchangeability hN hθ' hρ s s' a a' ha ha' hs' hex

/-- `NMSC.cut_alternatives` at the boundary of the parameters. -/
theorem cut_alternatives_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (s : QuartetTree X) (hs : InducedCutSplit N s) :
    ∀ r ∈ s.alternatives, ∀ r' ∈ s.alternatives, nmscCF N θ ρ r = nmscCF N θ ρ r' := fun r hr r' hr' =>
  nmscCF_eq_of_forall_isMetric hθ ρ r r' fun _ hθ' => NMSC.cut_alternatives hN hθ' hρ s hs r hr r' hr'

end Boundary

/-! ### Replacing a taxon in a displayed quartet tree -/

section Replace

open NMSC

variable [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The replacement of a taxon in a quartet tree is the relabelling by a transposition. -/
theorem eq_relabelQuartet_swap_of_image {s s' : QuartetTree X} {a a' : X} (ha' : a' ∉ s.taxa)
    (hs' : s'.val = s.val.image (fun B => if a ∈ B then insert a' (B.erase a) else B)) :
    s' = relabelQuartet (Equiv.swap a a') s := by
  refine Subtype.ext ?_
  rw [hs']
  change _ = relabelFamily _ _
  unfold relabelFamily
  refine image_congr fun B hB => ?_
  have hB' : a' ∉ B := fun h => ha' (s.subset_taxa hB h)
  change (if a ∈ B then insert a' (B.erase a) else B) = _
  ext z
  rw [mem_map_equiv, Equiv.symm_swap]
  by_cases hza : z = a
  · subst hza
    rw [Equiv.swap_apply_left]
    split_ifs with h
    · have hne : z ≠ a' := fun h' => hB' (h' ▸ h)
      simp [hB', hne]
    · simp [h, hB']
  by_cases hza' : z = a'
  · subst hza'
    rw [Equiv.swap_apply_right]
    split_ifs with h
    · simp [h]
    · simp [h, hB']
  rw [Equiv.swap_apply_of_ne_of_ne hza hza']
  split_ifs with h
  · simp [hza, hza']
  · rfl

/-- **A tree with a side grouping `a, a'` away from the other three taxa of `r`** treats `a` and `a'`
alike: a split of the tree restricts to `r` exactly when it has `a` and `a'` on the same side. -/
theorem displays_relabelQuartet_swap {T : Finset (Finset X)} (hT : IsUnrootedTree T) {A : Finset X}
    (hA : A ∈ T) {a a' : X} (haA : a ∈ A) (ha'A : a' ∈ A) {r : QuartetTree X} (ha'r : a' ∉ r.taxa)
    (hoth : ∀ x ∈ r.taxa, x ≠ a → x ∉ A) (hd : Displays T r) :
    Displays T (relabelQuartet (Equiv.swap a a') r) := by
  obtain ⟨B, hB, hBr⟩ := hd
  have hsd := r.sdiff_mem hBr
  have hc1 := r.card_of_mem hBr
  have hc2 := r.card_of_mem hsd
  have key : a ∈ B ↔ a' ∈ B := by
    constructor
    · intro haB
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (by omega : 1 < #(B ∩ r.taxa)) a
      obtain ⟨d, hd⟩ : (r.taxa \ (B ∩ r.taxa)).Nonempty := card_pos.1 (by omega)
      obtain ⟨hdq, hdn⟩ := mem_sdiff.1 hd
      have hdB : d ∉ B := fun h => hdn (mem_inter.2 ⟨h, hdq⟩)
      have hda : d ≠ a := by
        rintro rfl
        exact hdB haB
      rcases hT.compatible hA hB with h | h | h | h
      · exact h ha'A
      · exact absurd (h (mem_inter.1 hb).1) (hoth b (mem_inter.1 hb).2 hba)
      · exact absurd haB (disjoint_left.1 h haA)
      · have := mem_univ d
        rw [← h, mem_union] at this
        exact absurd (this.resolve_right hdB) (hoth d hdq hda)
    · intro ha'B
      by_contra haB
      obtain ⟨b, hb⟩ : (B ∩ r.taxa).Nonempty := card_pos.1 (by omega)
      obtain ⟨d, hd, hda⟩ := exists_mem_ne (by omega : 1 < #(r.taxa \ (B ∩ r.taxa))) a
      obtain ⟨hdq, hdn⟩ := mem_sdiff.1 hd
      have hdB : d ∉ B := fun h => hdn (mem_inter.2 ⟨h, hdq⟩)
      have hba : b ≠ a := by
        rintro rfl
        exact haB (mem_inter.1 hb).1
      rcases hT.compatible hA hB with h | h | h | h
      · exact haB (h haA)
      · exact absurd (h (mem_inter.1 hb).1) (hoth b (mem_inter.1 hb).2 hba)
      · exact absurd ha'B (disjoint_left.1 h ha'A)
      · have := mem_univ d
        rw [← h, mem_union] at this
        exact absurd (this.resolve_right hdB) (hoth d hdq hda)
  refine ⟨B, hB, ?_⟩
  have hmem : (B ∩ r.taxa).map (Equiv.swap a a').toEmbedding ∈ (relabelQuartet (Equiv.swap a a') r).val :=
    map_mem_relabelFamily.2 hBr
  have heq : B ∩ (relabelQuartet (Equiv.swap a a') r).taxa =
      (B ∩ r.taxa).map (Equiv.swap a a').toEmbedding := by
    rw [taxa_relabelQuartet]
    ext z
    rw [mem_inter, mem_map_equiv, mem_map_equiv, mem_inter, Equiv.symm_swap]
    by_cases hza : z = a
    · subst hza
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => absurd h.2 ha'r, fun h => absurd h.2 ha'r⟩
    by_cases hza' : z = a'
    · subst hza'
      rw [Equiv.swap_apply_right]
      exact and_congr_left fun _ => key.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hza hza']
  rw [heq]
  exact hmem

end Replace

/-! ### Long edges: the displayed trees

As the lengths grow, a gene tree under common inheritance is resolved as its displayed tree is. -/

section Long

open NMSC

variable [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- In a rooted tree, an arc is the only one crossing the vertices below it. -/
theorem crosses_below_iff_of_tree (hN : N.IsPhylogenetic)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) (f g : E) :
    N.graph.Crosses g {u | N.graph.Reaches (N.graph.target f) u} ↔ g = f := by
  constructor
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · exact absurd (Relation.ReflTransGen.tail hs ⟨g, rfl, rfl⟩) ht
    · rcases Relation.ReflTransGen.cases_tail ht with h | ⟨y, hy, k, hks, hkt⟩
      · exact htree _ _ h
      · have hkg : k = g := htree _ _ hkt
        subst hkg
        exact absurd (hks ▸ hy) hs
  · rintro rfl
    exact Or.inr ⟨Relation.ReflTransGen.refl, not_reaches_target_source hN.acyclic g⟩

omit [Fintype X] in
/-- **On a rooted tree, four taxa that no vertex splits two against two form a trivial 4-blob**: at the lowest
vertex with three of them below it, these three are below distinct arcs leaving it. -/
theorem hasTrivialFourBlob_of_tree [Fintype X] [Fintype V] (hN : N.IsPhylogenetic)
    (htree : ∀ f g, N.graph.target f = N.graph.target g → f = g) {q : Finset X} (hq : #q = 4)
    (hne : ∀ u : V, #(q.filter fun x => N.graph.Reaches u (N.leaf x)) ≠ 2) :
    HasTrivialFourBlob N q := by
  have : Finite E := hN.finite_arcs
  set B : V → Finset X := fun u => q.filter fun x => N.graph.Reaches u (N.leaf x) with hB
  have hmemB : ∀ {u x}, x ∈ B u ↔ x ∈ q ∧ N.graph.Reaches u (N.leaf x) := fun {u x} => by simp [hB]
  have hroot : 3 ≤ #(B N.root) := by
    have : B N.root = q := filter_true_of_mem fun x _ => hN.root_reaches _
    rw [this, hq]
    norm_num
  obtain ⟨v, hv, hmin⟩ := exists_lowest hN (S := {u | 3 ≤ #(B u)}) ⟨N.root, hroot⟩
  have hv3 : 3 ≤ #(B v) := hv
  have hchild : ∀ f, N.graph.source f = v → #(B (N.graph.target f)) ≤ 1 := by
    intro f hf
    by_contra hcon
    have h2 := hne (N.graph.target f)
    have h3 : 3 ≤ #(B (N.graph.target f)) := by
      change #(q.filter fun x => N.graph.Reaches (N.graph.target f) (N.leaf x)) ≠ 2 at h2
      simp only [hB] at hcon ⊢
      omega
    have := hmin _ h3 (.single ⟨f, hf, rfl⟩)
    exact NMSC.source_ne_target hN f (hf.trans this.symm)
  refine ⟨v, fun x hx => ?_⟩
  by_cases hxv : N.graph.Reaches v (N.leaf x)
  · rcases Relation.ReflTransGen.cases_head hxv with h | ⟨w, ⟨f, hfs, hft⟩, hw⟩
    · exfalso
      have hsub : B v ⊆ {x} := fun y hy => by
        have hr := (hmemB.1 hy).2
        rw [h] at hr
        exact mem_singleton.2 (eq_of_leaf_reachesOff_leaf (D := ∅) hN (reachesOff_empty_iff.2 hr))
      have := card_le_card hsub
      rw [card_singleton] at this
      omega
    · subst hft
      refine ⟨f, ⟨x, hx, hw⟩, {u | N.graph.Reaches (N.graph.target f) u}, fun g _ =>
        crosses_below_iff_of_tree hN htree f g, fun y hy => ⟨fun hyb => ?_, ?_⟩, ?_, Or.inl hfs⟩
      · exact card_le_one.1 (hchild f hfs) y (hmemB.2 ⟨hy, hyb⟩) x (hmemB.2 ⟨hx, hw⟩)
      · rintro rfl
        exact hw
      · change ¬ N.graph.Reaches (N.graph.target f) v
        rw [← hfs]
        exact not_reaches_target_source hN.acyclic f
  · have hvr : v ≠ N.root := by
      rintro rfl
      exact hxv (hN.root_reaches _)
    obtain ⟨e, rfl⟩ := (N.graph.one_le_indegree_iff v).1 (hN.nonroot_indegree v hvr)
    obtain ⟨y₀, hy₀⟩ : (B (N.graph.target e)).Nonempty := card_pos.1 (by omega)
    refine ⟨e, ⟨y₀, (hmemB.1 hy₀).1, (hmemB.1 hy₀).2⟩, {u | N.graph.Reaches (N.graph.target e) u}ᶜ,
      fun g _ => (N.graph.crosses_compl g _).trans (crosses_below_iff_of_tree hN htree e g),
      fun y hy => ⟨fun hyb => ?_, ?_⟩, not_not.2 Relation.ReflTransGen.refl, Or.inr rfl⟩
    · by_contra hyx
      have hsub : B (N.graph.target e) ⊆ (q.erase x).erase y := fun z hz => by
        obtain ⟨hzq, hzr⟩ := hmemB.1 hz
        refine mem_erase.2 ⟨?_, mem_erase.2 ⟨?_, hzq⟩⟩
        · rintro rfl
          exact hyb hzr
        · rintro rfl
          exact hxv hzr
      have hc := card_le_card hsub
      rw [card_erase_of_mem (mem_erase.2 ⟨hyx, hy⟩), card_erase_of_mem hx, hq] at hc
      omega
    · rintro rfl
      exact hxv

variable [Fintype V] [Fintype E] {θ : MetricData E}

omit [Fintype E] in
/-- A quartet tree displayed by a parent choice is separated by an arc of the network of the choice. -/
theorem exists_isKeptArc_of_displays (hN : N.IsPhylogenetic) {c : N.ParentChoice} {r : QuartetTree X}
    (hd : Displays (N.displayedSides c) r) :
    ∃ P ∈ r.val, ∃ e, N.IsKeptArc c e ∧
      (∀ x ∈ P, N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x)) ∧
      ∀ x ∈ r.taxa, x ∉ P → ¬ N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x) := by
  have key : ∀ {P C : Finset X}, P ∈ r.val → (∀ x ∈ r.taxa, x ∈ P ↔ x ∈ C) → C ≠ univ → C ≠ ∅ →
      (∃ u, N.displayedCluster c u = C) →
      ∃ P ∈ r.val, ∃ e, N.IsKeptArc c e ∧
        (∀ x ∈ P, N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x)) ∧
        ∀ x ∈ r.taxa, x ∉ P → ¬ N.ReachesOff (N.deletedArcs c) (N.graph.target e) (N.leaf x) := by
    rintro P C hP hPC hCu hCe ⟨u, rfl⟩
    have hur : u ≠ N.root := by
      rintro rfl
      exact hCu (eq_univ_of_forall fun x => mem_displayedCluster.2
        ((isDeletion_deletedArcs hN c).root_reachesOff hN _))
    have ht : N.graph.target (c ⟨u, hur⟩).val = u := (c ⟨u, hur⟩).property
    obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.2 hCe
    refine ⟨P, hP, (c ⟨u, hur⟩).val, ⟨notMem_deletedArcs_choice c _, x₀, ?_⟩, fun x hx => ?_,
      fun x hxq hxP hr => ?_⟩
    · rw [ht]
      exact mem_displayedCluster.1 hx₀
    · rw [ht]
      exact mem_displayedCluster.1 ((hPC x (r.subset_taxa hP hx)).1 hx)
    · rw [ht] at hr
      exact hxP ((hPC x hxq).2 (mem_displayedCluster.2 hr))
  obtain ⟨A, hA, hAr⟩ := hd
  rcases mem_unroot.1 hA with ⟨hAH, hAu⟩ | ⟨hAH, hAu⟩
  · obtain ⟨hne, hu⟩ := mem_displayedClusters.1 hAH
    exact key hAr (fun x hx => by simp [hx]) hAu hne hu
  · obtain ⟨hne, hu⟩ := mem_displayedClusters.1 hAH
    refine key (r.sdiff_mem hAr) (fun x hx => ?_) hAu hne hu
    simp [hx]

/-- **With all lengths at least `m`, a quartet tree displayed by a parent choice has concordance factor at least
`1 - exp (-m)` in the parameters of the choice**, and its alternatives at most `exp (-m)`. -/
theorem nmscCF_choiceMetric_bounds_of_displays (hN : N.IsPhylogenetic) (c : N.ParentChoice) {m : ℝ}
    (hm : 0 < m) (hℓ : ∀ f, m ≤ θ.length f) {r : QuartetTree X}
    (hd : Displays (N.displayedSides c) r) :
    1 - Real.exp (-m) ≤ nmscCF N (N.choiceMetric θ c) 1 r ∧
      nmscCF N (N.choiceMetric θ c) 1 r ≤ 1 ∧
      ∀ r' ∈ r.alternatives, nmscCF N (N.choiceMetric θ c) 1 r' ≤ Real.exp (-m) := by
  have hpos : ∀ f, 0 < θ.length f := fun f => lt_of_lt_of_le hm (hℓ f)
  obtain ⟨P, hP, e, he, hb, hn⟩ := exists_isKeptArc_of_displays hN hd
  obtain ⟨a, ha⟩ : P.Nonempty := card_pos.1 (by rw [r.card_of_mem hP]; omega)
  have hM := isPhylogenetic_choiceNetwork hN c a
  have hw := isWeakMetric_choiceMetric hN (fun f => (hpos f).le) c
  have hnonneg := nmscCF_nonneg_weak (ρ := 1) hN hw ⟨zero_le_one, le_rfl⟩
  have hsum := sum_nmscCF_weak (ρ := 1) hN hw.isNormalized zero_le_one r.card_taxa
  have hle : ∀ t ∈ treesOn r.taxa, nmscCF N (N.choiceMetric θ c) 1 t ≤ 1 := fun t ht =>
    (single_le_sum (f := fun t' => nmscCF N (N.choiceMetric θ c) 1 t') (fun t' _ => hnonneg t') ht).trans
      hsum.le
  have hbound : ∀ r' ∈ r.alternatives, 1 - Real.exp (-θ.length e) ≤
      nmscCF N (N.choiceMetric θ c) 1 r - nmscCF N (N.choiceMetric θ c) 1 r' := fun r' hr' => by
    rw [← nmscCF_choiceNetwork hN c a zero_le_one θ r, ← nmscCF_choiceNetwork hN c a zero_le_one θ r']
    exact one_sub_exp_le_sub_nmscCF_of_tree hM (isMetric_choiceNetworkMetric hN c a fun f _ => hpos f)
      ⟨zero_le_one, le_rfl⟩ (fun f g h => eq_of_target_choiceNetwork hN c a h) r hP (e := ⟨e, he⟩)
      (fun x hx => reaches_choiceNetwork hN c a _ _ (hb x hx))
      (fun x hx hxP hb' => hn x hx hxP (reachesOff_of_reaches_choiceNetwork hN c a hb')) hr'
  have hexp : Real.exp (-θ.length e) ≤ Real.exp (-m) := Real.exp_le_exp.2 (by linarith [hℓ e])
  have hr1 := hle r (mem_treesOn.2 rfl)
  refine ⟨?_, hr1, fun r' hr' => ?_⟩
  · obtain ⟨r', hr'⟩ := card_pos.1 (by rw [r.card_alternatives]; omega : 0 < #r.alternatives)
    linarith [hbound r' hr', hnonneg r']
  · linarith [hbound r' hr']

/-- **Taxa that a parent choice leaves unresolved have concordance factors `1/3` in the parameters of the
choice**, as a polytomy of the displayed tree gives no information, whatever the lengths. -/
theorem nmscCF_choiceMetric_eq_third (hN : N.IsPhylogenetic) (c : N.ParentChoice)
    (hℓ : ∀ f, 0 < θ.length f) {q : Finset X} (hq : #q = 4)
    (hstar : ∀ r ∈ treesOn q, ¬ Displays (N.displayedSides c) r) {r : QuartetTree X}
    (hr : r ∈ treesOn q) : nmscCF N (N.choiceMetric θ c) 1 r = 1 / 3 := by
  obtain ⟨a, -⟩ : q.Nonempty := card_pos.1 (by omega)
  have hM := isPhylogenetic_choiceNetwork hN c a
  have hmem : ∀ (u : {v // N.IsKeptVertex c v}) (x : X),
      (N.choiceNetwork hN c a).graph.Reaches u ((N.choiceNetwork hN c a).leaf x) ↔
        x ∈ N.displayedCluster c u.val := fun u x =>
    ⟨fun h => mem_displayedCluster.2 (reachesOff_of_reaches_choiceNetwork hN c a h),
      fun h => reaches_choiceNetwork hN c a u.property (isKeptVertex_leaf c x)
        (mem_displayedCluster.1 h)⟩
  have hne : ∀ u : {v // N.IsKeptVertex c v},
      #(q.filter fun x => (N.choiceNetwork hN c a).graph.Reaches u
        ((N.choiceNetwork hN c a).leaf x)) ≠ 2 := by
    intro u h2
    have heq : (q.filter fun x => (N.choiceNetwork hN c a).graph.Reaches u
        ((N.choiceNetwork hN c a).leaf x)) = N.displayedCluster c u.val ∩ q := by
      ext x
      simp [hmem, and_comm]
    rw [heq] at h2
    have hAne : N.displayedCluster c u.val ≠ ∅ := by
      intro h
      rw [h, empty_inter] at h2
      simp at h2
    have hAu : N.displayedCluster c u.val ≠ univ := by
      intro h
      rw [h, univ_inter, hq] at h2
      norm_num at h2
    have hA : N.displayedCluster c u.val ∈ N.displayedSides c :=
      mem_unroot.2 (Or.inl ⟨mem_displayedClusters.2 ⟨hAne, _, rfl⟩, hAu⟩)
    exact hstar _ (mem_treesOn.2 (quartetOfCherry_taxa _ _ hq inter_subset_right h2))
      (displays_quartetOfCherry hA hq h2)
  have ht := hasTrivialFourBlob_of_tree hM (fun f g h => eq_of_target_choiceNetwork hN c a h) hq hne
  rw [← nmscCF_choiceNetwork hN c a zero_le_one θ r]
  exact NMSC.trivial_uniform hM (isMetric_choiceNetworkMetric hN c a fun f _ => hℓ f)
    ⟨zero_le_one, le_rfl⟩ q hq ht r hr

/-- `NMSC.trivial_uniform` at the boundary of the parameters. -/
theorem trivial_uniform_weak (hN : N.IsPhylogenetic) (hθ : N.IsWeakMetric θ) {ρ : ℝ} (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) (ht : HasTrivialFourBlob N q) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    nmscCF N θ ρ r = 1 / 3 := by
  have heq : ∀ r' ∈ treesOn q, nmscCF N θ ρ r' = nmscCF N θ ρ r := fun r' hr' =>
    nmscCF_eq_of_forall_isMetric hθ ρ r' r fun _ hθ' => by
      rw [NMSC.trivial_uniform hN hθ' hρ q hq ht r' hr', NMSC.trivial_uniform hN hθ' hρ q hq ht r hr]
  have hsum := sum_nmscCF_weak (θ := θ) (ρ := ρ) hN hθ.isNormalized hρ.1 hq
  rw [sum_congr rfl heq, sum_const, card_treesOn hq] at hsum
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hsum
  linarith

/-- **On a trivial 4-blob, no displayed tree resolves the four taxa**: the concordance factors of a parent choice
are `1/3` for all lengths, while long edges would make a displayed quartet tree more likely than that. -/
theorem not_displays_of_hasTrivialFourBlob (hN : N.IsPhylogenetic) (c : N.ParentChoice) {q : Finset X}
    (hq : #q = 4) (ht : HasTrivialFourBlob N q) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    ¬ Displays (N.displayedSides c) r := by
  intro hd
  let θ₀ : MetricData E := ⟨fun _ => 2, fun _ => 1⟩
  have hw := isWeakMetric_choiceMetric hN (θ := θ₀) (fun _ => zero_le_two) c
  have hthird := trivial_uniform_weak (ρ := 1) hN hw ⟨zero_le_one, le_rfl⟩ hq ht hr
  have hb := (nmscCF_choiceMetric_bounds_of_displays (θ := θ₀) hN c (m := 2) two_pos (fun _ => le_rfl) hd).1
  rw [hthird] at hb
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have h4 : Real.exp (-2) ≤ 1 / 3 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h3
  linarith

end Long

/-! ### The Markov property at a set closed under children

`Phylogenetics.NMSC.Factor` proves the Markov property at an arc that dominates the lineages below it.
Here it is at any set `D` of vertices closed under children: given the forests at the top of the arcs leaving `D`,
what is above is the process with these forests injected at the sources of the arcs. No domination is needed. -/

section MarkovSet

open NMSC

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq X] {θ : MetricData E} {ρ : ℝ}

local notation "𝔅" => ((Fintype.card (Finset (Finset X)) : ℕ) : ℝ)

variable (N) in
/-- The arcs entering a set of vertices. -/
def arcsIn (D : Finset V) : Finset E := univ.filter fun f => N.graph.target f ∈ D

omit [Fintype V] [Fintype X] [DecidableEq X] in
theorem mem_arcsIn {D : Finset V} {f : E} : f ∈ arcsIn N D ↔ N.graph.target f ∈ D := by
  simp [arcsIn]

variable (N) in
/-- The injected forests after moving what is in `D` to the sources of the arcs leaving `D`, as the forests `τ`
at the top of these arcs. -/
def liftSet (D : Finset V) (inj : V → Finset (Finset X)) (τ : E → Finset (Finset X)) :
    V → Finset (Finset X) := fun v =>
  if v ∈ D then ∅ else
    inj v ∪ (univ.filter fun f => N.graph.source f = v ∧ N.graph.target f ∈ D).biUnion τ

variable (N θ ρ) in
/-- The factors of the vertices outside `D`, with the root. -/
def restSet (inj : V → Finset (Finset X)) (D : Finset V) (G : Finset (Finset X))
    (bot top : E → Finset (Finset X)) : ℝ :=
  (∏ v ∈ (univ.erase N.root) \ D, vertexWeight N θ ρ inj v bot top) *
    kingmanAbsorption (arriving N inj top N.root) G

variable (N θ ρ) in
/-- The part of the process above `D`, given the forests `τ` at the top of the arcs leaving `D`. -/
def aboveSet (inj : V → Finset (Finset X)) (D : Finset V) (G : Finset (Finset X))
    (τ : E → Finset (Finset X)) : ℝ :=
  ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
    restSet N θ ρ inj D G b (overwrite (arcsIn N D) t τ)

variable (N X) in
/-- The total mass of the part of the process on `D`, independent of the injected forests. -/
def setMass (D : Finset V) : ℝ :=
  (𝔅 ^ Fintype.card E) ^ 2 / (𝔅 ^ #(arcsIn N D)) ^ 2

omit [DecidableEq X] [Fintype V] in
theorem setMass_pos (D : Finset V) : 0 < setMass X N D := by
  have hB : (0 : ℝ) < 𝔅 := by exact_mod_cast Fintype.card_pos
  unfold setMass
  positivity

theorem sum_sum_prod_eq_setMass (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) :
    ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      ∏ u ∈ D, vertexWeight N θ ρ inj u bot top = setMass X N D := by
  have h := sum_sum_prod_vertexWeight_weak (θ := θ) (ρ := ρ) hN hθ hρ hinj hD hroot
  have hB : (0 : ℝ) < 𝔅 := by exact_mod_cast Fintype.card_pos
  unfold setMass arcsIn
  rw [eq_div_iff (pow_ne_zero 2 (pow_ne_zero _ hB.ne')), mul_comm]
  exact h

omit [DecidableEq X] in
theorem card_fun_eq_pow_arcs : ((Fintype.card (E → Finset (Finset X)) : ℕ) : ℝ) = 𝔅 ^ Fintype.card E := by
  rw [Fintype.card_fun, Nat.cast_pow]

omit [Fintype V] [Fintype X] [DecidableEq X] in
theorem notMem_compl_arcsIn {D : Finset V} {f : E} (hf : N.graph.target f ∈ D) :
    f ∉ (arcsIn N D)ᶜ := fun h => mem_compl.1 h (mem_arcsIn.2 hf)

omit [Fintype V] in
theorem prod_set_overwrite_bot {D : Finset V} (inj : V → Finset (Finset X))
    (top bot y : E → Finset (Finset X)) :
    ∏ u ∈ D, vertexWeight N θ ρ inj u (overwrite (arcsIn N D)ᶜ bot y) top =
      ∏ u ∈ D, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsIn (hf ▸ hu)) _ _)
    (fun _ _ => rfl) (fun _ _ => rfl)

omit [Fintype V] in
theorem prod_set_overwrite_top {D : Finset V} (hD : DownClosed N D) (inj : V → Finset (Finset X))
    (bot top y : E → Finset (Finset X)) :
    ∏ u ∈ D, vertexWeight N θ ρ inj u bot (overwrite (arcsIn N D)ᶜ top y) =
      ∏ u ∈ D, vertexWeight N θ ρ inj u bot top :=
  prod_congr rfl fun _ hu => vertexWeight_congr rfl (fun _ _ => rfl)
    (fun _ hf => overwrite_of_notMem (notMem_compl_arcsIn (hf ▸ hu)) _ _)
    (fun f hf => overwrite_of_notMem (notMem_compl_arcsIn (hD f (hf ▸ hu))) _ _)

/-- The part above `D` only sees the arcs not entering `D`, and the tops of the arcs leaving `D`. -/
theorem restSet_congr {inj : V → Finset (Finset X)} {D : Finset V} {G : Finset (Finset X)}
    (hroot : N.root ∉ D) {bot bot' top top' : E → Finset (Finset X)}
    (h1 : ∀ f, f ∉ arcsIn N D → bot f = bot' f) (h2 : ∀ f, f ∉ arcsIn N D → top f = top' f)
    (h3 : ∀ f, f ∈ arcsIn N D → N.graph.source f ∉ D → top f = top' f) :
    restSet N θ ρ inj D G bot top = restSet N θ ρ inj D G bot' top' := by
  have hch : ∀ v, v ∉ D → ∀ f, N.graph.source f = v → top f = top' f := by
    intro v hv f hf
    by_cases hfS : f ∈ arcsIn N D
    · exact h3 f hfS (hf ▸ hv)
    · exact h2 f hfS
  have hin : ∀ v, v ∉ D → ∀ f, N.graph.target f = v → f ∉ arcsIn N D :=
    fun v hv f hf hfS => hv (hf ▸ mem_arcsIn.1 hfS)
  unfold restSet
  rw [arriving_congr rfl (hch _ hroot)]
  refine congrArg (· * _) (prod_congr rfl fun v hv => ?_)
  have hv' := (mem_sdiff.1 hv).2
  exact vertexWeight_congr rfl (fun f hf => h1 f (hin v hv' f hf))
    (fun f hf => h2 f (hin v hv' f hf)) (hch v hv')

/-- The weight of a history splits at `D`. -/
theorem injDist_eq_sum_set (inj : V → Finset (Finset X)) {D : Finset V}
    (hroot : N.root ∉ D) (G : Finset (Finset X)) :
    injDist N θ ρ inj G = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
      (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) * restSet N θ ρ inj D G bot top := by
  have hsub : D ⊆ univ.erase N.root := fun v hv => mem_erase.2 ⟨fun h => hroot (h ▸ hv), mem_univ _⟩
  have hw : ∀ bot top : E → Finset (Finset X), injWeight N θ ρ inj bot top =
      (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
        ∏ v ∈ (univ.erase N.root) \ D, vertexWeight N θ ρ inj v bot top := fun bot top => by
    unfold injWeight
    rw [← prod_sdiff hsub, mul_comm]
  unfold injDist restSet
  simp only [hw, mul_assoc]

/-- The history splits at `D`, up to the number of values of the arcs. -/
theorem card_sq_mul_injDist_set (inj : V → Finset (Finset X)) {D : Finset V}
    (hroot : N.root ∉ D) (hD : DownClosed N D) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ inj G) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) * aboveSet N θ ρ inj D G top := by
  have htop : ∀ bot : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ top : E → Finset (Finset X),
          (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) * restSet N θ ρ inj D G bot top =
        ∑ top : E → Finset (Finset X), (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
          ∑ t : E → Finset (Finset X),
            restSet N θ ρ inj D G bot (overwrite (arcsIn N D)ᶜ top t) := fun bot =>
    card_mul_sum_mul (arcsIn N D)ᶜ _ _ fun top y => prod_set_overwrite_top hD inj bot top y
  have hbot : ∀ top : E → Finset (Finset X),
      (Fintype.card (E → Finset (Finset X)) : ℝ) * ∑ bot : E → Finset (Finset X),
          (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
            ∑ t : E → Finset (Finset X),
              restSet N θ ρ inj D G bot (overwrite (arcsIn N D)ᶜ top t) =
        ∑ bot : E → Finset (Finset X), (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
          ∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
            restSet N θ ρ inj D G (overwrite (arcsIn N D)ᶜ bot b)
              (overwrite (arcsIn N D)ᶜ top t) := fun top =>
    card_mul_sum_mul (arcsIn N D)ᶜ (fun bot => ∏ v ∈ D, vertexWeight N θ ρ inj v bot top)
      (fun bot => ∑ t : E → Finset (Finset X),
        restSet N θ ρ inj D G bot (overwrite (arcsIn N D)ᶜ top t))
      fun bot y => prod_set_overwrite_bot inj top bot y
  have hpt : ∀ bot top : E → Finset (Finset X),
      (∑ b : E → Finset (Finset X), ∑ t : E → Finset (Finset X),
        restSet N θ ρ inj D G (overwrite (arcsIn N D)ᶜ bot b) (overwrite (arcsIn N D)ᶜ top t)) =
      aboveSet N θ ρ inj D G top := by
    intro bot top
    unfold aboveSet
    refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => restSet_congr hroot ?_ ?_ ?_
    · exact fun f hf => overwrite_of_mem (mem_compl.2 hf) _ _
    · intro f hf
      rw [overwrite_of_mem (mem_compl.2 hf), overwrite_of_notMem hf]
    · intro f hf _
      rw [overwrite_of_notMem (fun h => mem_compl.1 h hf), overwrite_of_mem hf]
  rw [injDist_eq_sum_set inj hroot G, mul_sum]
  simp only [htop]
  rw [sum_comm, mul_sum]
  simp only [hbot, hpt]
  rw [sum_comm]

omit [Fintype V] [Fintype X] in
/-- The forest arriving outside `D` is the same when the forests at the top of the arcs leaving `D` are injected at
their sources. -/
theorem arriving_liftSet [Fintype X] (inj : V → Finset (Finset X)) (D : Finset V) (τ t : E → Finset (Finset X)) {v : V}
    (hv : v ∉ D) :
    arriving N (liftSet N D inj τ) (overwrite (arcsIn N D) t fun _ => ∅) v =
      arriving N inj (overwrite (arcsIn N D) t τ) v := by
  ext C
  simp only [arriving, liftSet, hv, ↓reduceIte, mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ((h | ⟨f, ⟨hfs, hft⟩, hC⟩) | ⟨f, hf, hC⟩)
    · exact Or.inl h
    · refine Or.inr ⟨f, hfs, ?_⟩
      rwa [overwrite_of_mem (mem_arcsIn.2 hft)]
    · by_cases hfS : f ∈ arcsIn N D
      · rw [overwrite_of_mem hfS] at hC
        exact absurd hC (notMem_empty _)
      · rw [overwrite_of_notMem hfS] at hC
        exact Or.inr ⟨f, hf, by rwa [overwrite_of_notMem hfS]⟩
  · rintro (h | ⟨f, hf, hC⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hfS : f ∈ arcsIn N D
      · rw [overwrite_of_mem hfS] at hC
        exact Or.inl (Or.inr ⟨f, ⟨hf, mem_arcsIn.1 hfS⟩, hC⟩)
      · rw [overwrite_of_notMem hfS] at hC
        exact Or.inr ⟨f, hf, by rwa [overwrite_of_notMem hfS]⟩

/-- The part above `D`, given the forests at the top of the arcs leaving it, is the process with these forests
injected at the sources of the arcs. -/
theorem aboveSet_liftSet (inj : V → Finset (Finset X)) {D : Finset V} (hroot : N.root ∉ D)
    (G τ' : _) (τ : E → Finset (Finset X)) (hτ' : τ' = fun _ : E => (∅ : Finset (Finset X))) :
    aboveSet N θ ρ (liftSet N D inj τ) D G τ' = aboveSet N θ ρ inj D G τ := by
  subst hτ'
  unfold aboveSet restSet
  refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => ?_
  rw [arriving_liftSet inj D τ t hroot]
  refine congrArg (· * _) (prod_congr rfl fun v hv => ?_)
  have hv' := (mem_sdiff.1 hv).2
  unfold vertexWeight
  rw [arriving_liftSet inj D τ t hv']
  refine congrArg (_ * ·) (prod_congr rfl fun f hf => ?_)
  have hfS : f ∉ arcsIn N D := fun h => hv' (mem_arcsInto.1 hf ▸ mem_arcsIn.1 h)
  rw [overwrite_of_notMem hfS, overwrite_of_notMem hfS]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- The lineages of the lifted forests. -/
theorem mem_lineages_liftSet [Fintype E] [Fintype X] {inj : V → Finset (Finset X)} {D : Finset V} {τ : E → Finset (Finset X)} {v : V} {x : X} :
    x ∈ lineages (liftSet N D inj τ v) ↔ v ∉ D ∧ (x ∈ lineages (inj v) ∨
      ∃ f, N.graph.source f = v ∧ N.graph.target f ∈ D ∧ x ∈ lineages (τ f)) := by
  by_cases hv : v ∈ D
  · simp [liftSet, hv]
  · simp only [liftSet, hv, ↓reduceIte, not_false_eq_true, true_and]
    rw [lineages_union, mem_union]
    refine or_congr Iff.rfl ?_
    rw [mem_lineages]
    constructor
    · rintro ⟨A, hA, hx⟩
      obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
      obtain ⟨hfs, hft⟩ := (mem_filter.1 hf).2
      exact ⟨f, hfs, hft, mem_lineages.2 ⟨A, hAf, hx⟩⟩
    · rintro ⟨f, hfs, hft, hx⟩
      obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx
      exact ⟨A, mem_biUnion.2 ⟨f, mem_filter.2 ⟨mem_univ _, hfs, hft⟩, hA⟩, hxA⟩

omit [Fintype V] in
/-- Lifting what is in `D` keeps the injected forests valid. -/
theorem validInj_liftSet {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V}
    {bot top : E → Finset (Finset X)} (hF : Frontier N inj D bot top) :
    ValidInj (liftSet N D inj top) := by
  have hout : ∀ x f, N.graph.target f ∈ D → N.graph.source f ∉ D → x ∈ lineages (top f) →
      ∀ v, v ∉ D → x ∉ lineages (inj v) := by
    intro x f hft hfs hx v hv hxv
    obtain ⟨u, hu, hxu⟩ := (hF.mem x).1 ⟨f, hft, hfs, hx⟩
    exact disjoint_left.1 (hinj.disj u v fun h => hv (h ▸ hu)) hxu hxv
  refine ⟨fun v => ?_, fun u v huv => disjoint_left.2 fun x hxu hxv => ?_⟩
  · unfold liftSet
    split_ifs with hv
    · exact isGoodForest_empty
    refine IsGoodForest.union (hinj.good v) (IsGoodForest.biUnion _ _ ?_ ?_) ?_
    · intro f hf
      exact hF.good_top f (mem_filter.1 hf).2.2
    · intro e he f hf hef
      obtain ⟨he₁, he₂⟩ := (mem_filter.1 he).2
      obtain ⟨hf₁, hf₂⟩ := (mem_filter.1 hf).2
      exact hF.disj e f he₂ (he₁ ▸ hv) hf₂ (hf₁ ▸ hv) hef
    · rw [disjoint_left]
      intro x hx hx'
      obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx'
      obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
      obtain ⟨hf₁, hf₂⟩ := (mem_filter.1 hf).2
      exact hout x f hf₂ (hf₁ ▸ hv) (mem_lineages.2 ⟨A, hAf, hxA⟩) v hv hx
  · obtain ⟨hu, hxu'⟩ := mem_lineages_liftSet.1 hxu
    obtain ⟨hv, hxv'⟩ := mem_lineages_liftSet.1 hxv
    rcases hxu' with h₁ | ⟨f, hf₁, hf₂, hf₃⟩ <;> rcases hxv' with h₂ | ⟨g, hg₁, hg₂, hg₃⟩
    · exact disjoint_left.1 (hinj.disj u v huv) h₁ h₂
    · exact hout x g hg₂ (hg₁ ▸ hv) hg₃ u hu h₁
    · exact hout x f hf₂ (hf₁ ▸ hu) hf₃ v hv h₂
    · have hfg : f ≠ g := by
        rintro rfl
        exact huv (hf₁.symm.trans hg₁)
      exact disjoint_left.1 (hF.disj f g hf₂ (hf₁ ▸ hu) hg₂ (hg₁ ▸ hv) hfg) hf₃ hg₃

/-- With nothing injected in `D`, the forests at the top of the arcs entering `D` are empty. -/
theorem top_eq_empty_of_inj_empty (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {D : Finset V}
    (hD : DownClosed N D) (hl : ValidInj inj) (hemp : ∀ u ∈ D, inj u = ∅)
    {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ D, vertexWeight N θ ρ inj v bot top ≠ 0) {f : E}
    (hf : N.graph.target f ∈ D) : top f = ∅ := by
  have hF := frontier_of_prod_ne_zero hN hl hD h
  by_contra hne
  obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨x, hx⟩ := (hF.good_top f hf).1.1 A hA
  obtain ⟨u, hu, hxu⟩ := hF.below f hf x (mem_lineages.2 ⟨A, hA, hx⟩)
  have key : ∀ w, N.graph.Reaches (N.graph.target f) w → w ∈ D := fun w hw => by
    induction hw with
    | refl => exact hf
    | tail _ hab ih =>
      obtain ⟨g, hgs, hgt⟩ := hab
      exact hgt ▸ hD g (hgs ▸ ih)
  rw [hemp u (key u hu)] at hxu
  simp at hxu

/-- With nothing injected in `D`, the forests at the top of the arcs entering `D` are empty. -/
theorem top_eq_empty_of_liftSet (hN : N.IsPhylogenetic) {inj : V → Finset (Finset X)} {D : Finset V}
    (hD : DownClosed N D) {τ : E → Finset (Finset X)} (hl : ValidInj (liftSet N D inj τ))
    {bot top : E → Finset (Finset X)}
    (h : ∏ v ∈ D, vertexWeight N θ ρ (liftSet N D inj τ) v bot top ≠ 0) {f : E}
    (hf : N.graph.target f ∈ D) : top f = ∅ :=
  top_eq_empty_of_inj_empty hN hD hl (fun u hu => by simp [liftSet, hu]) h hf

/-- The part above `D` depends on the forests at the top of the arcs leaving `D`. -/
theorem aboveSet_congr {inj : V → Finset (Finset X)} {D : Finset V} {G : Finset (Finset X)}
    (hroot : N.root ∉ D) {τ τ' : E → Finset (Finset X)}
    (h : ∀ f, f ∈ arcsIn N D → N.graph.source f ∉ D → τ f = τ' f) :
    aboveSet N θ ρ inj D G τ = aboveSet N θ ρ inj D G τ' := by
  unfold aboveSet
  refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => restSet_congr hroot (fun _ _ => rfl) ?_ ?_
  · intro f hf
    rw [overwrite_of_notMem hf, overwrite_of_notMem hf]
  · intro f hf hs
    rw [overwrite_of_mem hf, overwrite_of_mem hf, h f hf hs]

/-- The process with the forests `τ` injected at the sources of the arcs leaving `D`, up to the number of values
of the arcs, is the part above `D`. -/
theorem card_sq_mul_injDist_liftSet (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    (inj : V → Finset (Finset X)) {D : Finset V} (hD : DownClosed N D) (hroot : N.root ∉ D)
    {τ : E → Finset (Finset X)} (hl : ValidInj (liftSet N D inj τ)) (G : Finset (Finset X)) :
    (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        injDist N θ ρ (liftSet N D inj τ) G) =
      setMass X N D * aboveSet N θ ρ inj D G τ := by
  rw [card_sq_mul_injDist_set _ hroot hD G, ← aboveSet_liftSet inj hroot G _ τ rfl,
    ← sum_sum_prod_eq_setMass (θ := θ) (ρ := ρ) hN hθ hρ hl hD hroot, sum_mul]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun top _ => ?_
  by_cases hg : ∏ v ∈ D, vertexWeight N θ ρ (liftSet N D inj τ) v bot top = 0
  · simp [hg]
  · refine congrArg (_ * ·) (aboveSet_congr hroot fun f hf _ => ?_)
    exact top_eq_empty_of_liftSet hN hD hl hg (mem_arcsIn.1 hf)

/-- **The Markov property at a set closed under children.** The process is the mixture, over the part of the
history in `D`, of the process with the forests at the top of the arcs leaving `D` injected at their sources. -/
theorem setMass_mul_injDist (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) (G : Finset (Finset X)) :
    setMass X N D * injDist N θ ρ inj G =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) * injDist N θ ρ (liftSet N D inj top) G := by
  have hM : (Fintype.card (E → Finset (Finset X)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine mul_left_cancel₀ hM (mul_left_cancel₀ hM ?_)
  have h1 := card_sq_mul_injDist_set (θ := θ) (ρ := ρ) inj hroot hD G
  calc (Fintype.card (E → Finset (Finset X)) : ℝ) * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
        (setMass X N D * injDist N θ ρ inj G))
      = setMass X N D * ((Fintype.card (E → Finset (Finset X)) : ℝ) *
          ((Fintype.card (E → Finset (Finset X)) : ℝ) * injDist N θ ρ inj G)) := by ring
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
            (setMass X N D * aboveSet N θ ρ inj D G top) := by
        rw [h1, mul_sum]
        refine sum_congr rfl fun bot _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun top _ => ?_
        ring
    _ = ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
          (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
            ((Fintype.card (E → Finset (Finset X)) : ℝ) *
              ((Fintype.card (E → Finset (Finset X)) : ℝ) *
                injDist N θ ρ (liftSet N D inj top) G)) := by
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        by_cases hg : ∏ v ∈ D, vertexWeight N θ ρ inj v bot top = 0
        · simp [hg]
        · exact congrArg (_ * ·) (card_sq_mul_injDist_liftSet hN hθ hρ inj hD hroot
            (validInj_liftSet hinj (frontier_of_prod_ne_zero hN hinj hD hg)) G).symm
    _ = _ := by
        simp only [mul_sum]
        refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
        ring

/-- **The Markov property at a set closed under children**, for the mass of a quartet tree. -/
theorem setMass_mul_cherryMass (hN : N.IsPhylogenetic) (hθ : N.IsNormalized θ) (hρ : 0 ≤ ρ)
    {inj : V → Finset (Finset X)} (hinj : ValidInj inj) {D : Finset V} (hD : DownClosed N D)
    (hroot : N.root ∉ D) (r : QuartetTree X) :
    setMass X N D * cherryMass N θ ρ inj r =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) * cherryMass N θ ρ (liftSet N D inj top) r := by
  unfold cherryMass
  simp only [mul_sum]
  have h : ∀ H : Finset (Finset X), setMass X N D *
      (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ inj H else 0) =
      ∑ bot : E → Finset (Finset X), ∑ top : E → Finset (Finset X),
        (∏ v ∈ D, vertexWeight N θ ρ inj v bot top) *
          (if ∃ B ∈ r.val, B ∈ H then injDist N θ ρ (liftSet N D inj top) H else 0) := by
    intro H
    split_ifs
    · exact setMass_mul_injDist hN hθ hρ hinj hD hroot H
    · simp
  simp only [h]
  rw [sum_comm]
  refine sum_congr rfl fun bot _ => ?_
  rw [sum_comm]

/-! ### Singleton lineages at given vertices -/

/-- The singleton lineages of the taxa `q`, each at its position. -/
def placeInj (q : Finset X) (P : X → V) (u : V) : Finset (Finset X) :=
  (q.filter fun x => P x = u).image fun x => ({x} : Finset X)

omit [Fintype V] [Fintype E] [Fintype X] in
theorem mem_lineages_placeInj [Fintype X] {q : Finset X} {P : X → V} {u : V} {x : X} :
    x ∈ lineages (placeInj q P u) ↔ x ∈ q ∧ P x = u := by
  unfold placeInj
  rw [lineages_image_singleton, mem_filter]

omit [Fintype V] [Fintype E] [Fintype X] in
theorem validInj_placeInj [Fintype X] (q : Finset X) (P : X → V) : ValidInj (placeInj q P) :=
  ⟨fun _ => isGoodForest_singletons _, fun _ _ huv => disjoint_left.2 fun _ hxu hxv =>
    huv ((mem_lineages_placeInj.1 hxu).2.symm.trans (mem_lineages_placeInj.1 hxv).2)⟩

omit [Fintype V] [Fintype E] in
theorem placeInj_leaf (q : Finset X) : placeInj q N.leaf = taxaInj N q := by
  funext u
  unfold placeInj taxaInj
  congr 1
  ext x
  simp

omit [Fintype V] [Fintype E] [Fintype X] in
theorem placeInj_congr {q : Finset X} {P P' : X → V} (h : ∀ x ∈ q, P x = P' x) :
    placeInj q P = placeInj q P' := by
  funext u
  unfold placeInj
  congr 1
  refine filter_congr fun x hx => ?_
  rw [h x hx]

omit [Fintype V] [Fintype E] [Fintype X] in
/-- Relabelling the singleton lineages. -/
theorem relabelInj_placeInj (π : Equiv.Perm X) (q : Finset X) (P : X → V) :
    relabelInj π (placeInj q P) = placeInj (q.map π.toEmbedding) (P ∘ π.symm) := by
  funext u
  unfold relabelInj placeInj relabelFamily
  ext A
  simp only [mem_image, mem_filter, exists_exists_and_eq_and, mem_map, Function.comp]
  constructor
  · rintro ⟨x, ⟨hx, hu⟩, rfl⟩
    refine ⟨π x, ⟨⟨x, hx, rfl⟩, by simpa using hu⟩, ?_⟩
    simp
  · rintro ⟨y, ⟨⟨x, hx, rfl⟩, hu⟩, rfl⟩
    refine ⟨x, ⟨hx, by simpa using hu⟩, ?_⟩
    simp

/-- A lineage alone below an arc that dominates it moves up to the source of the arc. -/
theorem cherryMass_placeInj_lift (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} {P : X → V} {x : X} (hx : x ∈ q) {e : E}
    (hb : N.graph.Reaches (N.graph.target e) (P x)) (hd : ¬ N.AvoidingReach e N.root (P x))
    (hoth : ∀ y ∈ q, y ≠ x → ¬ N.graph.Reaches (N.graph.target e) (P y)) (r : QuartetTree X) :
    cherryMass N θ ρ (placeInj q P) r =
      cherryMass N θ ρ (placeInj q (Function.update P x (N.graph.source e))) r := by
  have hinj := validInj_placeInj q P
  have hdom : DominatedInj N e (placeInj q P) := by
    rintro u hu ⟨A, hA⟩
    obtain ⟨z, hz⟩ := (hinj.good u).1.1 A hA
    obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 (mem_lineages.2 ⟨A, hA, hz⟩)
    have hzx : z = x := by
      by_contra hne
      exact hoth z hzq hne (mem_belowSet.1 hu)
    rw [hzx]
    exact hd
  have hlift : liftInj N e (placeInj q P) {{x}} =
      placeInj q (Function.update P x (N.graph.source e)) := by
    funext u
    ext A
    by_cases hu : u ∈ belowSet N e
    · simp only [liftInj, hu, ↓reduceIte, empty_union, placeInj, mem_image, mem_filter]
      have hus : u ≠ N.graph.source e := fun h => source_notMem_belowSet hN e (h ▸ hu)
      simp only [hus, ↓reduceIte, notMem_empty, false_iff, not_exists, not_and]
      rintro z ⟨hzq, hzu⟩ rfl
      by_cases hzx : z = x
      · subst hzx
        rw [Function.update_self] at hzu
        exact hus hzu.symm
      · rw [Function.update_of_ne hzx] at hzu
        exact hoth z hzq hzx (hzu ▸ mem_belowSet.1 hu)
    · simp only [liftInj, hu, ↓reduceIte, placeInj, mem_union, mem_image, mem_filter]
      constructor
      · rintro (⟨z, ⟨hzq, hzu⟩, rfl⟩ | h)
        · refine ⟨z, ⟨hzq, ?_⟩, rfl⟩
          rw [Function.update_of_ne]
          · exact hzu
          · rintro rfl
            exact hu (hzu ▸ mem_belowSet.2 hb)
        · split_ifs at h with hus
          · obtain rfl := mem_singleton.1 h
            exact ⟨x, ⟨hx, by rw [Function.update_self, hus]⟩, rfl⟩
          · exact absurd h (notMem_empty _)
      · rintro ⟨z, ⟨hzq, hzu⟩, rfl⟩
        by_cases hzx : z = x
        · subst hzx
          rw [Function.update_self] at hzu
          right
          rw [ite_eq_left hzu.symm]
          exact mem_singleton_self _
        · rw [Function.update_of_ne hzx] at hzu
          exact Or.inl ⟨z, ⟨hzq, hzu⟩, rfl⟩
  unfold cherryMass
  refine sum_congr rfl fun H _ => ?_
  have hsing : injDist N θ ρ (placeInj q P) H = injDist N θ ρ (placeInj q
      (Function.update P x (N.graph.source e))) H := by
    rw [← hlift]
    refine injDist_eq_lift_singleton hN hθ hρ hinj hdom
      ⟨P x, mem_belowSet.2 hb, mem_lineages_placeInj.2 ⟨hx, rfl⟩⟩ (fun u hu z hz => ?_) H
    obtain ⟨hzq, rfl⟩ := mem_lineages_placeInj.1 hz
    by_contra hne
    exact hoth z hzq hne (mem_belowSet.1 hu)
  rw [hsing]

/-- **Three singleton lineages at one vertex, the fourth anywhere, make the three quartet trees equally likely.** -/
theorem cherryMass_placeInj_eq_third (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) {P : X → V} {a : X} (ha : a ∈ q) {v : V}
    (hP : ∀ x ∈ q, x ≠ a → P x = v) {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (placeInj q P) r = 1 / 3 := by
  refine cherryMass_eq_third hN hθ hρ (validInj_placeInj q P) hq (fun x => ?_) ha
    (fun x hx y hy hxa hya => ?_) hr
  · constructor
    · rintro ⟨u, hu⟩
      exact (mem_lineages_placeInj.1 hu).1
    · exact fun hx => ⟨P x, mem_lineages_placeInj.2 ⟨hx, rfl⟩⟩
  · have hmap : q.map (Equiv.swap x y).toEmbedding = q := by
      ext z
      rw [mem_map_equiv, Equiv.symm_swap]
      by_cases hzx : z = x
      · subst hzx
        rw [Equiv.swap_apply_left]
        exact ⟨fun _ => hx, fun _ => hy⟩
      by_cases hzy : z = y
      · subst hzy
        rw [Equiv.swap_apply_right]
        exact ⟨fun _ => hy, fun _ => hx⟩
      rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
    rw [relabelInj_placeInj, hmap]
    refine placeInj_congr fun z hz => ?_
    simp only [Function.comp, Equiv.symm_swap]
    by_cases hzx : z = x
    · subst hzx
      rw [Equiv.swap_apply_left, hP y hy hya, hP z hx hxa]
    by_cases hzy : z = y
    · subst hzy
      rw [Equiv.swap_apply_right, hP x hx hxa, hP z hy hya]
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- **Below a vertex with three lineages, only what arrives there matters.** Let `e₀` enter `v₀`, and let at least
three of the four lineages `q` be at or below `v₀` in each of two placements, which agree strictly below `v₀`. Then the
masses of the quartet trees are equal. Given the forest arriving at `v₀`, a cherry decides, and otherwise three
singletons at `v₀` make the three quartet trees equally likely. -/
theorem cherryMass_placeInj_eq_of_below (hN : N.IsPhylogenetic) (hθ : N.IsMetric θ) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    {q : Finset X} (hq : #q = 4) {e₀ : E} {P₁ P₂ : X → V}
    (hagree : ∀ x ∈ q, (P₁ x ∈ (belowSet N e₀).erase (N.graph.target e₀) ∨
      P₂ x ∈ (belowSet N e₀).erase (N.graph.target e₀)) → P₁ x = P₂ x)
    (h₁ : ∃ a ∈ q, ∀ x ∈ q, x ≠ a → P₁ x ∈ belowSet N e₀)
    (h₂ : ∃ a ∈ q, ∀ x ∈ q, x ≠ a → P₂ x ∈ belowSet N e₀)
    (hdom : ∀ x ∈ q, P₁ x ∈ (belowSet N e₀).erase (N.graph.target e₀) →
      ¬ N.AvoidingReach e₀ N.root (P₁ x))
    {r : QuartetTree X} (hr : r ∈ treesOn q) :
    cherryMass N θ ρ (placeInj q P₁) r = cherryMass N θ ρ (placeInj q P₂) r := by
  have hrq := mem_treesOn.1 hr
  set v₀ := N.graph.target e₀ with hv₀
  set D := (belowSet N e₀).erase v₀ with hDdef
  have hD : DownClosed N D := downClosed_belowSet_erase hN e₀
  have hroot : N.root ∉ D := fun h => root_notMem_belowSet hN e₀ (mem_of_mem_erase h)
  have hv₀D : v₀ ∉ D := notMem_erase _ _
  have hbelow : ∀ u, u ∈ belowSet N e₀ ↔ u = v₀ ∨ u ∈ D := fun u => by
    rw [hDdef, mem_erase]
    constructor
    · intro h
      by_cases hu : u = v₀
      · exact Or.inl hu
      · exact Or.inr ⟨hu, h⟩
    · rintro (rfl | h)
      · exact target_mem_belowSet e₀
      · exact h.2
  have hv₁ := validInj_placeInj q P₁
  have hv₂ := validInj_placeInj q P₂
  have hsame : ∀ u ∈ D, placeInj q P₁ u = placeInj q P₂ u := by
    intro u hu
    unfold placeInj
    congr 1
    refine filter_congr fun x hx => ⟨fun h => ?_, fun h => ?_⟩
    · rw [← hagree x hx (Or.inl (h ▸ hu)), h]
    · rw [hagree x hx (Or.inr (h ▸ hu)), h]
  have hprod : ∀ bot top : E → Finset (Finset X), ∏ u ∈ D, vertexWeight N θ ρ (placeInj q P₁) u bot top =
      ∏ u ∈ D, vertexWeight N θ ρ (placeInj q P₂) u bot top := fun bot top =>
    prod_congr rfl fun u hu => vertexWeight_congr (hsame u hu) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  refine mul_left_cancel₀ (setMass_pos (X := X) (N := N) D).ne' ?_
  rw [setMass_mul_cherryMass hN hθ.isNormalized hρ.1 hv₁ hD hroot,
    setMass_mul_cherryMass hN hθ.isNormalized hρ.1 hv₂ hD hroot]
  refine sum_congr rfl fun bot _ => sum_congr rfl fun top _ => ?_
  rw [← hprod bot top]
  by_cases hz : ∏ u ∈ D, vertexWeight N θ ρ (placeInj q P₁) u bot top = 0
  · simp [hz]
  refine congrArg (_ * ·) ?_
  have hF₁ := frontier_of_prod_ne_zero hN hv₁ hD hz
  have hF₂ := frontier_of_prod_ne_zero hN hv₂ hD (by rwa [← hprod bot top])
  have hl₁ := validInj_liftSet hv₁ hF₁
  have hl₂ := validInj_liftSet hv₂ hF₂
  -- the arcs leaving `D` that carry lineages leave `v₀`
  have hsrc : ∀ f x, N.graph.target f ∈ D → N.graph.source f ∉ D → x ∈ lineages (top f) →
      N.graph.source f = v₀ := by
    intro f x hft hfs hx
    by_contra hne
    obtain ⟨u, hu, hxu⟩ := hF₁.below f hft x hx
    obtain ⟨hxq, rfl⟩ := mem_lineages_placeInj.1 hxu
    have hfb : N.graph.Reaches (N.graph.target e₀) (N.graph.target f) := mem_belowSet.1 (mem_of_mem_erase hft)
    have hud : P₁ x ∈ D := by
      have hx' : x ∈ lineages (top f) := hx
      obtain ⟨u', hu', hxu'⟩ := (hF₁.mem x).1 ⟨f, hft, hfs, hx'⟩
      rwa [(mem_lineages_placeInj.1 hxu').2]
    refine hdom x hxq hud ?_
    have h1 : N.AvoidingReach e₀ N.root (N.graph.source f) := by
      by_contra hn
      have := target_reaches_of_not_avoidingReach (hN.root_reaches _) hn
      rcases (hbelow _).1 (mem_belowSet.2 this) with h | h
      · exact hne h
      · exact hfs h
    have hfe : f ≠ e₀ := by
      rintro rfl
      exact hv₀D hft
    exact (h1.tail ⟨f, hfe, rfl, rfl⟩).trans (avoidingReach_of_target_reaches hN.acyclic hfb hu)
  have hemp : ∀ f, N.graph.target f ∈ D → N.graph.source f ∉ D → N.graph.source f ≠ v₀ → top f = ∅ := by
    intro f hft hfs hne
    refine eq_empty_of_forall_notMem fun A hA => ?_
    obtain ⟨x, hx⟩ := (hF₁.good_top f hft).1.1 A hA
    exact hne (hsrc f x hft hfs (mem_lineages.2 ⟨A, hA, hx⟩))
  -- the forest arriving at `v₀` from `D`
  set F : Finset (Finset X) := (univ.filter fun f => N.graph.source f = v₀ ∧ N.graph.target f ∈ D).biUnion top with hF
  have hlift : ∀ {P : X → V} (_ : ∀ x ∈ q, (P x ∈ D ↔ P₁ x ∈ D)) (u : V),
      liftSet N D (placeInj q P) top u =
        if u ∈ D then ∅ else placeInj q P u ∪ if u = v₀ then F else ∅ := by
    intro P _ u
    unfold liftSet
    split_ifs with hu huv
    · rfl
    · rw [huv]
    · rw [union_empty, union_eq_left]
      intro A hA
      obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
      obtain ⟨hf₁, hf₂⟩ := (mem_filter.1 hf).2
      rw [hemp f hf₂ (hf₁ ▸ hu) (hf₁ ▸ huv)] at hAf
      exact absurd hAf (notMem_empty _)
  have hP₂D : ∀ x ∈ q, (P₂ x ∈ D ↔ P₁ x ∈ D) := fun x hx =>
    ⟨fun h => by rw [hagree x hx (Or.inr h)]; exact h, fun h => by rw [← hagree x hx (Or.inl h)]; exact h⟩
  have hlin : ∀ x, x ∈ lineages F ↔ x ∈ q ∧ P₁ x ∈ D := by
    intro x
    rw [mem_lineages]
    constructor
    · rintro ⟨A, hA, hxA⟩
      obtain ⟨f, hf, hAf⟩ := mem_biUnion.1 hA
      obtain ⟨hf₁, hf₂⟩ := (mem_filter.1 hf).2
      obtain ⟨u, hu, hxu⟩ := (hF₁.mem x).1 ⟨f, hf₂, hf₁ ▸ hv₀D, mem_lineages.2 ⟨A, hAf, hxA⟩⟩
      obtain ⟨hxq, rfl⟩ := mem_lineages_placeInj.1 hxu
      exact ⟨hxq, hu⟩
    · rintro ⟨hxq, hxD⟩
      obtain ⟨f, hft, hfs, hx⟩ := (hF₁.mem x).2 ⟨P₁ x, hxD, mem_lineages_placeInj.2 ⟨hxq, rfl⟩⟩
      obtain ⟨A, hA, hxA⟩ := mem_lineages.1 hx
      exact ⟨A, mem_biUnion.2 ⟨f, mem_filter.2 ⟨mem_univ _, hsrc f x hft hfs hx, hft⟩, hA⟩, hxA⟩
  have hgoodF : IsGoodForest F := by
    refine IsGoodForest.biUnion _ _ (fun f hf => hF₁.good_top f (mem_filter.1 hf).2.2) ?_
    intro e he f hf hef
    obtain ⟨he₁, he₂⟩ := (mem_filter.1 he).2
    obtain ⟨hf₁, hf₂⟩ := (mem_filter.1 hf).2
    exact hF₁.disj e f he₂ (he₁ ▸ hv₀D) hf₂ (hf₁ ▸ hv₀D) hef
  have hmemlift : ∀ {P : X → V} (hP : ∀ x ∈ q, (P x ∈ D ↔ P₁ x ∈ D)) {C : Finset X}, C ∈ F →
      C ∈ liftSet N D (placeInj q P) top v₀ := by
    intro P hP C hC
    rw [hlift hP, ite_eq_right hv₀D, ite_eq_left rfl]
    exact mem_union_right _ hC
  have hsubq : ∀ {C : Finset X}, C ∈ F → C ⊆ r.taxa := fun {C} hC x hx => by
    rw [hrq]
    exact ((hlin x).1 (mem_lineages.2 ⟨C, hC, hx⟩)).1
  by_cases h2 : ∃ C ∈ F, #C = 2
  · obtain ⟨C, hC, hC2⟩ := h2
    rw [cherryMass_of_mem hN hθ hρ hl₁ (hmemlift (fun _ _ => Iff.rfl) hC) hC2 (hsubq hC),
      cherryMass_of_mem hN hθ hρ hl₂ (hmemlift hP₂D hC) hC2 (hsubq hC)]
  -- no cherry: three singletons at `v₀`
  have hFs : F = (q.filter fun x => P₁ x ∈ D).image fun x => ({x} : Finset X) := by
    have := hgoodF.eq_singletons h2
    rw [this]
    congr 1
    ext x
    rw [hlin, mem_filter]
  have heval : ∀ {P : X → V} (_ : ∀ x ∈ q, (P x ∈ D ↔ P₁ x ∈ D)) (_ : ∃ a ∈ q, ∀ x ∈ q, x ≠ a → P x ∈ belowSet N e₀),
      cherryMass N θ ρ (liftSet N D (placeInj q P) top) r = 1 / 3 := by
    intro P hP ⟨a, ha, hbel⟩
    have heq : liftSet N D (placeInj q P) top = placeInj q fun x => if P x ∈ D then v₀ else P x := by
      funext u
      rw [hlift hP]
      ext A
      by_cases hu : u ∈ D
      · simp only [hu, ↓reduceIte, notMem_empty, false_iff]
        intro hA
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
        obtain ⟨hxq, hxu⟩ := mem_filter.1 hx
        change (if P x ∈ D then v₀ else P x) = u at hxu
        split_ifs at hxu with h
        · exact hv₀D (hxu ▸ hu)
        · exact h (hxu ▸ hu)
      · simp only [hu, ↓reduceIte, placeInj, mem_union, mem_image, mem_filter]
        constructor
        · rintro (⟨x, ⟨hxq, hxu⟩, rfl⟩ | h)
          · refine ⟨x, ⟨hxq, ?_⟩, rfl⟩
            rw [ite_eq_right (fun h => hu (hxu ▸ h)), hxu]
          · split_ifs at h with huv
            · rw [hFs] at h
              obtain ⟨x, hx, rfl⟩ := mem_image.1 h
              obtain ⟨hxq, hxD⟩ := mem_filter.1 hx
              exact ⟨x, ⟨hxq, by rw [ite_eq_left ((hP x hxq).2 hxD), huv]⟩, rfl⟩
            · exact absurd h (notMem_empty _)
        · rintro ⟨x, ⟨hxq, hxu⟩, rfl⟩
          change (if P x ∈ D then v₀ else P x) = u at hxu
          split_ifs at hxu with hxD
          · right
            rw [ite_eq_left hxu.symm, hFs]
            exact mem_image_of_mem _ (mem_filter.2 ⟨hxq, (hP x hxq).1 hxD⟩)
          · exact Or.inl ⟨x, ⟨hxq, hxu⟩, rfl⟩
    rw [heq]
    refine cherryMass_placeInj_eq_third hN hθ hρ hq ha (v := v₀) (fun x hx hxa => ?_) hr
    rcases (hbelow _).1 (hbel x hx hxa) with h | h
    · simp only [h, ite_self]
    · rw [ite_eq_left h]
  rw [heval (fun _ _ => Iff.rfl) h₁, heval hP₂D h₂]

end MarkovSet

end Phylogenetics.RootedNetwork
