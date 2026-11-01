module

public import Phylogenetics.NMSC.Defs
public import Phylogenetics.ForMathlib.MeasureTheory.HaarPreimage
public import Phylogenetics.Network.InducedMetric

/-!
# The numerical parameters of an induced network

The map from the numerical parameters of a network `N` to those of its induced network on a set of taxa
`Y` (`inducedMetric`, `Phylogenetics.Network.InducedMetric`), and three facts that carry a generic condition on an induced
network to one on the network:

* the induced network of a binary network is binary (`inducedNetwork_isBinary`);
* the map sends valid parameters to valid parameters (`isMetric_inducedMetric`);
* the preimage of a null set of parameters is null (`isGenericNull_inducedMetric`).

The map is the composite of two steps, which are treated separately: restriction to the arcs below the
LSA (`belowMetric`), then suppression of the chain vertices (`suppressMetric`). In the coordinates of
`IsGenericNull` each step is a surjective linear map, since a length on a suppressed network is a sum
along a chain, chains are disjoint, and an inheritance probability on it is that of the chain's last arc
(`chainLast`). So preimages of null sets are null (`MeasureTheory.Measure.prod_pi_volume_preimage_eq_zero`).

## Main results

* `chainLast`, `chainHead`: the last and first arcs of a chain, inverse to each other
  (`chainLast_chainHead`, `chainHead_chainLast`);
* `suppress_indegree`, `belowNetwork_indegree`: kept vertices keep their indegree;
* `inducedNetwork_isBinary`;
* `isMetric_suppressMetric`, `isMetric_belowMetric`, `isMetric_inducedMetric`;
* `isGenericNull_comap`, `isGenericNull_suppressMetric`, `isGenericNull_belowMetric`,
  `isGenericNull_inducedMetric`.

## References

* E. S. Allman, H. Baños, J. D. Mitchell, J. A. Rhodes, *The tree of blobs of a species network:
  identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Classical

namespace Phylogenetics.RootedNetwork

variable {V E X : Type*} {N : RootedNetwork V E X}

/-! ### The first and last arcs of a chain -/

/-- A chain has a last arc, which enters the end of the chain. -/
theorem exists_isOnChain_target_eq_chainEnd (hN : N.IsPhylogenetic) (f : E) :
    ∃ g, N.IsOnChain f g ∧ N.graph.target g = chainEnd hN (N.graph.target f) := by
  rcases Relation.ReflTransGen.cases_tail (chainReach_chainEnd hN (N.graph.target f)) with
    h | ⟨a, hr, hc, g, hs, ht⟩
  · exact ⟨f, Or.inl rfl, h.symm⟩
  · subst hs
    exact ⟨g, Or.inr ⟨hc, hr⟩, ht⟩

/-- The last arc of the chain starting with `f`. -/
def chainLast (hN : N.IsPhylogenetic) (f : E) : E :=
  Classical.choose (exists_isOnChain_target_eq_chainEnd hN f)

theorem isOnChain_chainLast (hN : N.IsPhylogenetic) (f : E) : N.IsOnChain f (chainLast hN f) :=
  (Classical.choose_spec (exists_isOnChain_target_eq_chainEnd hN f)).1

theorem target_chainLast (hN : N.IsPhylogenetic) (f : E) :
    N.graph.target (chainLast hN f) = chainEnd hN (N.graph.target f) :=
  (Classical.choose_spec (exists_isOnChain_target_eq_chainEnd hN f)).2

/-- The arc starting the chain through `g`. -/
def chainHead (hN : N.IsPhylogenetic) (g : E) : {e // ¬ N.IsChainVertex (N.graph.source e)} :=
  ⟨Classical.choose (exists_isOnChain hN g), (Classical.choose_spec (exists_isOnChain hN g)).1⟩

theorem isOnChain_chainHead (hN : N.IsPhylogenetic) (g : E) : N.IsOnChain (chainHead hN g).1 g :=
  (Classical.choose_spec (exists_isOnChain hN g)).2

/-- The arcs of a chain have the same chain end. -/
theorem IsOnChain.chainEnd_eq (hN : N.IsPhylogenetic) {f g : E} (h : N.IsOnChain f g) :
    chainEnd hN (N.graph.target f) = chainEnd hN (N.graph.target g) := by
  rcases h with rfl | ⟨hc, hr⟩
  · rfl
  · exact (chainEnd_eq_of_chainReach_left hN hr).trans (chainEnd_eq_of_adj hN hc ⟨g, rfl, rfl⟩)

/-- All arcs but the last on a chain enter chain vertices. -/
theorem IsOnChain.eq_chainLast_or (hN : N.IsPhylogenetic) {f g : E} (h : N.IsOnChain f g) :
    g = chainLast hN f ∨ N.IsChainVertex (N.graph.target g) := by
  by_cases hg : N.IsChainVertex (N.graph.target g)
  · exact Or.inr hg
  · refine Or.inl (h.eq_of_target (isOnChain_chainLast hN f) ?_ hg)
    rw [target_chainLast, h.chainEnd_eq hN, chainEnd_eq_self hN hg]

/-- An arc entering a kept vertex is the last arc of its chain. -/
theorem chainLast_chainHead (hN : N.IsPhylogenetic) {g : E}
    (hg : ¬ N.IsChainVertex (N.graph.target g)) : chainLast hN (chainHead hN g).1 = g :=
  (((isOnChain_chainHead hN g).eq_chainLast_or hN).resolve_right hg).symm

/-- An arc leaving a kept vertex starts its chain. -/
theorem chainHead_chainLast (hN : N.IsPhylogenetic) {f : E}
    (hf : ¬ N.IsChainVertex (N.graph.source f)) : chainHead hN (chainLast hN f) = ⟨f, hf⟩ :=
  Subtype.ext ((isOnChain_chainHead hN _).unique (isOnChain_chainLast hN f) (chainHead hN _).2 hf)

/-- Chains are disjoint: distinct chains have distinct last arcs. -/
theorem chainLast_injective (hN : N.IsPhylogenetic) :
    Function.Injective fun e : {e // ¬ N.IsChainVertex (N.graph.source e)} => chainLast hN e.1 := by
  intro e e' h
  have h₁ := chainHead_chainLast hN e.2
  have h₂ := chainHead_chainLast hN e'.2
  simp only at h
  rw [h] at h₁
  exact h₁.symm.trans h₂

/-! ### Suppression: kept vertices keep their indegree -/

/-- The arcs entering a kept vertex of the suppressed network are, through their last arcs, the arcs
entering it in the network. -/
def suppressTargetEquiv (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    {e // (N.suppress hN).graph.target e = v} ≃ {g // N.graph.target g = v.1} where
  toFun e := ⟨chainLast hN e.1.1, (target_chainLast hN e.1.1).trans (congrArg Subtype.val e.2)⟩
  invFun g := ⟨chainHead hN g.1, Subtype.ext <|
    ((isOnChain_chainHead hN g.1).chainEnd_eq hN).trans (by rw [g.2]; exact chainEnd_eq_self hN v.2)⟩
  left_inv e := Subtype.ext (chainHead_chainLast hN e.1.2)
  right_inv g := Subtype.ext (chainLast_chainHead hN (by rw [g.2]; exact v.2))

/-- **A kept vertex keeps its indegree under suppression.** -/
theorem suppress_indegree (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) :
    (N.suppress hN).graph.indegree v = N.graph.indegree v.1 :=
  Set.ncard_congr' (suppressTargetEquiv hN v)

theorem suppress_isTreeArc_iff (hN : N.IsPhylogenetic)
    (e : {e // ¬ N.IsChainVertex (N.graph.source e)}) :
    (N.suppress hN).IsTreeArc e ↔ N.IsTreeArc (chainLast hN e.1) := by
  unfold IsTreeArc
  rw [suppress_indegree, target_chainLast]
  rfl

theorem suppress_isHybridArc_iff (hN : N.IsPhylogenetic)
    (e : {e // ¬ N.IsChainVertex (N.graph.source e)}) :
    (N.suppress hN).IsHybridArc e ↔ N.IsHybridArc (chainLast hN e.1) := by
  unfold IsHybridArc
  rw [suppress_indegree, target_chainLast]
  rfl

/-- A composite tree arc is made of tree arcs. -/
theorem IsOnChain.isTreeArc (hN : N.IsPhylogenetic) {f g : E} (h : N.IsOnChain f g)
    (hl : N.IsTreeArc (chainLast hN f)) : N.IsTreeArc g := by
  rcases h.eq_chainLast_or hN with rfl | hc
  · exact hl
  · exact hc.1

/-! ### Suppression: valid parameters -/

/-- An arc of a network with valid parameters has nonnegative length. -/
theorem length_nonneg_of_isMetric [Fintype E] {θ : MetricData E} (hθ : N.IsMetric θ) (e : E) :
    0 ≤ θ.length e := by
  have h := (N.graph.one_le_indegree_iff (N.graph.target e)).mpr ⟨e, rfl⟩
  by_cases he : 2 ≤ N.graph.indegree (N.graph.target e)
  · exact hθ.2.1 e he
  · exact (hθ.1 e (by unfold IsTreeArc; omega)).le

/-- The inheritance of a composite arc is that of its last arc, since the others are tree arcs. -/
theorem suppressMetric_inheritance [Fintype E] (hN : N.IsPhylogenetic) {θ : MetricData E}
    (hθ : N.IsMetric θ) (e : {e // ¬ N.IsChainVertex (N.graph.source e)}) :
    (N.suppressMetric θ).inheritance e = θ.inheritance (chainLast hN e.1) := by
  refine Finset.prod_eq_single_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
    isOnChain_chainLast hN e.1⟩) fun g hg hne => ?_
  rcases (Finset.mem_filter.1 hg).2.eq_chainLast_or hN with h | hc
  · exact absurd h hne
  · exact hθ.2.2.1 g hc.1

/-- The inheritance sums of the suppressed network are those of the network. -/
theorem sum_suppress_target [Fintype E] [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) (v : {v // ¬ N.IsChainVertex v}) (γ : E → ℝ) :
    (∑ e : {e // ¬ N.IsChainVertex (N.graph.source e)},
        @ite _ ((N.suppress hN).graph.target e = v) (Classical.propDecidable _)
          (γ (chainLast hN e.1)) 0) =
      ∑ g, if N.graph.target g = v.1 then γ g else 0 := by
  refine (@Finset.sum_filter _ _ _ _ _ (fun _ => Classical.propDecidable _) _).symm.trans ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun e => chainLast hN e.1) (chainHead hN) ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact (suppressTargetEquiv hN v ⟨e, he⟩).2
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact ((suppressTargetEquiv hN v).symm ⟨g, hg⟩).2
  · intro e _
    exact chainHead_chainLast hN e.2
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact chainLast_chainHead hN (by rw [hg]; exact v.2)

/-- **Suppression sends valid parameters to valid parameters.** All arcs but the last on a chain enter
vertices of indegree one, so they are tree arcs. A composite tree arc is all tree arcs, with positive total
length; a composite hybrid arc has nonnegative length; its inheritance is the last arc's; and the
inheritance sums at a reticulation are those of the network. -/
theorem isMetric_suppressMetric [Fintype E] [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}]
    (hN : N.IsPhylogenetic) {θ : MetricData E} (hθ : N.IsMetric θ) :
    (N.suppress hN).IsMetric (N.suppressMetric θ) := by
  refine ⟨fun e he => ?_, fun e _ => ?_, fun e he => ?_, fun e he => ?_, fun v hv => ?_⟩
  · have hl := (suppress_isTreeArc_iff hN e).1 he
    refine Finset.sum_pos (fun g hg => hθ.1 g ?_)
      ⟨e.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩⟩
    exact (Finset.mem_filter.1 hg).2.isTreeArc hN hl
  · exact Finset.sum_nonneg fun g _ => length_nonneg_of_isMetric hθ g
  · rw [suppressMetric_inheritance hN hθ]
    exact hθ.2.2.1 _ ((suppress_isTreeArc_iff hN e).1 he)
  · rw [suppressMetric_inheritance hN hθ]
    exact hθ.2.2.2.1 _ ((suppress_isHybridArc_iff hN e).1 he)
  · refine (Finset.sum_congr rfl fun e _ => ?_).trans ((sum_suppress_target hN v θ.inheritance).trans
      (hθ.2.2.2.2 v.1 (by rwa [suppress_indegree] at hv)))
    rw [suppressMetric_inheritance hN hθ]

/-! ### Below a stable ancestor: kept vertices keep their parents -/

/-- A path from a vertex that does not reach `w` avoids `w`. -/
theorem hasPathAvoiding_of_not_reaches {u t w : V} (h : N.graph.Reaches u t)
    (hw : ¬ N.graph.Reaches u w) : N.HasPathAvoiding u t w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have hne : t ≠ w := fun h => hw (h ▸ .refl)
    exact ⟨hne, hne, .refl⟩
  | @head a b hab _ ih =>
    exact hasPathAvoiding_head hab (fun h => hw (h ▸ .refl)) (ih fun h => hw (h.head hab))

/-- **Every parent of a vertex strictly below a stable ancestor is below it.** -/
theorem IsStableAncestor.reaches_source (hN : N.IsPhylogenetic) {Y : Set X} {l : V}
    (hst : N.IsStableAncestor Y l) {x : X} (hx : x ∈ Y) {f : E}
    (ht : N.graph.Reaches (N.graph.target f) (N.leaf x))
    (hne : ¬ N.graph.Reaches (N.graph.target f) l) : N.graph.Reaches l (N.graph.source f) := by
  have key : ∀ a, N.graph.Reaches a (N.graph.source f) → ¬ N.HasPathAvoiding a (N.leaf x) l →
      N.graph.Reaches l (N.graph.source f) := by
    intro a ha
    induction ha using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro h
      by_contra hl
      exact h (hasPathAvoiding_head ⟨f, rfl, rfl⟩ (fun e => hl (e ▸ .refl))
        (hasPathAvoiding_of_not_reaches ht hne))
    | @head a b hab hb ih =>
      intro h
      by_cases ha : a = l
      · subst ha
        exact hb.head hab
      · exact ih fun hp => h (hasPathAvoiding_head hab ha hp)
  exact key N.root (hN.root_reaches _) (hst x hx)

section Below

variable {l : V} {Y : Set X} {hl : l ∈ N.ancestralVertices Y}
  {hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)}

/-- An arc entering a kept vertex other than the stable ancestor is kept. -/
theorem mem_belowArcs_of_target (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    (v : N.belowVertices l Y) (hv : v.1 ≠ l) {g : E} (hg : N.graph.target g = v.1) :
    g ∈ N.belowArcs l Y := by
  obtain ⟨x, hx, hr⟩ := v.2.2
  refine ⟨hst.reaches_source hN hx (by rwa [hg]) fun h => hv ?_, ?_⟩
  · rw [hg] at h
    exact eq_of_reaches_of_reaches hN.acyclic h v.2.1
  · change N.graph.target g ∈ N.ancestralVertices Y
    rw [hg]
    exact v.2.2

/-- A kept arc does not enter the stable ancestor. -/
theorem target_ne_of_mem_belowArcs (hN : N.IsPhylogenetic) (e : N.belowArcs l Y) :
    N.graph.target e.1 ≠ l := fun h =>
  not_reaches_target_source hN.acyclic e.1 (by rw [h]; exact e.2.1)

/-- The arcs entering a kept vertex other than the stable ancestor are those of the network. -/
def belowTargetEquiv (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    (v : N.belowVertices l Y) (hv : v.1 ≠ l) :
    {e // (N.belowNetwork l Y hl hleaf).graph.target e = v} ≃ {g // N.graph.target g = v.1} where
  toFun e := ⟨e.1.1, congrArg Subtype.val e.2⟩
  invFun g := ⟨⟨g.1, mem_belowArcs_of_target hN hst v hv g.2⟩, Subtype.ext g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A vertex strictly below a stable ancestor keeps its indegree.** -/
theorem belowNetwork_indegree (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    (v : N.belowVertices l Y) (hv : v.1 ≠ l) :
    (N.belowNetwork l Y hl hleaf).graph.indegree v = N.graph.indegree v.1 :=
  Set.ncard_congr' (belowTargetEquiv hN hst v hv)

theorem belowNetwork_isTreeArc_iff (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    (e : N.belowArcs l Y) : (N.belowNetwork l Y hl hleaf).IsTreeArc e ↔ N.IsTreeArc e.1 := by
  unfold IsTreeArc
  rw [belowNetwork_indegree hN hst _ (target_ne_of_mem_belowArcs hN e)]
  rfl

theorem belowNetwork_isHybridArc_iff (hN : N.IsPhylogenetic) (hst : N.IsStableAncestor Y l)
    (e : N.belowArcs l Y) : (N.belowNetwork l Y hl hleaf).IsHybridArc e ↔ N.IsHybridArc e.1 := by
  unfold IsHybridArc
  rw [belowNetwork_indegree hN hst _ (target_ne_of_mem_belowArcs hN e)]
  rfl

/-- The inheritance sums below a stable ancestor are those of the network. -/
theorem sum_belowArcs_target [Fintype E] [Fintype (N.belowArcs l Y)] (hN : N.IsPhylogenetic)
    (hst : N.IsStableAncestor Y l) (v : N.belowVertices l Y) (hv : v.1 ≠ l) (γ : E → ℝ) :
    (∑ e : N.belowArcs l Y,
        @ite _ ((N.belowNetwork l Y hl hleaf).graph.target e = v) (Classical.propDecidable _)
          (γ e.1) 0) =
      ∑ g, if N.graph.target g = v.1 then γ g else 0 := by
  refine (@Finset.sum_filter _ _ _ _ _ (fun _ => Classical.propDecidable _) _).symm.trans ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun e => e.1) ?_ (fun _ _ _ _ h => Subtype.ext h) ?_ fun _ _ => rfl
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact congrArg Subtype.val he
  · intro g hg
    have hg' : N.graph.target g = v.1 := by simpa using hg
    exact ⟨⟨g, mem_belowArcs_of_target hN hst v hv hg'⟩, by
      simpa using Subtype.ext hg', rfl⟩

/-- **Restriction below a stable ancestor sends valid parameters to valid parameters**: the arcs and their
parameters stay, and so do the sets of arcs entering a vertex. -/
theorem isMetric_belowMetric [Fintype E] [Fintype (N.belowArcs l Y)] (hN : N.IsPhylogenetic)
    (hst : N.IsStableAncestor Y l) {θ : MetricData E} (hθ : N.IsMetric θ) :
    (N.belowNetwork l Y hl hleaf).IsMetric (belowMetric l Y θ) := by
  refine ⟨fun e he => hθ.1 e.1 ((belowNetwork_isTreeArc_iff hN hst e).1 he),
    fun e he => hθ.2.1 e.1 ((belowNetwork_isHybridArc_iff hN hst e).1 he),
    fun e he => hθ.2.2.1 e.1 ((belowNetwork_isTreeArc_iff hN hst e).1 he),
    fun e he => hθ.2.2.2.1 e.1 ((belowNetwork_isHybridArc_iff hN hst e).1 he), fun v hv => ?_⟩
  have hvl : v.1 ≠ l := by
    intro h
    obtain ⟨e, he⟩ := (DirectedMultigraph.one_le_indegree_iff _ v).mp (by omega :
      1 ≤ (N.belowNetwork l Y hl hleaf).graph.indegree v)
    exact target_ne_of_mem_belowArcs hN e ((congrArg Subtype.val he).trans h)
  refine (sum_belowArcs_target (hl := hl) (hleaf := hleaf) hN hst v hvl θ.inheritance).trans ?_
  exact hθ.2.2.2.2 v.1 (by rwa [belowNetwork_indegree hN hst v hvl] at hv)

/-- Arcs below a vertex leave a vertex with at most its outdegree in the network. -/
theorem belowNetwork_outdegree_le [Finite E] (v : N.belowVertices l Y) :
    (N.belowNetwork l Y hl hleaf).graph.outdegree v ≤ N.graph.outdegree v.1 :=
  Set.ncard_le_ncard_of_injOn (fun e => e.1) (fun _ he => congrArg Subtype.val he)
    (fun _ _ _ _ h => Subtype.ext h) (Set.toFinite _)

end Below

/-! ### The induced network of a binary network is binary -/

/-- The part from `w` on of a path avoiding `c`, when the path cannot avoid `w`. -/
theorem HasPathAvoiding.suffix_of_not_hasPathAvoiding {u t c w : V} (h : N.HasPathAvoiding u t c)
    (hw : ¬ N.HasPathAvoiding u t w) : N.HasPathAvoiding w t c := by
  obtain ⟨-, ht, hp⟩ := h
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have : t = w := by
      by_contra hne
      exact hw ⟨hne, hne, .refl⟩
    subst this
    exact ⟨ht, ht, .refl⟩
  | @head a b hab hbt ih =>
    by_cases ha : a = w
    · subst ha
      exact ⟨hab.2.1, ht, hbt.head hab⟩
    · exact ih fun h => hw (hasPathAvoiding_head hab.1 ha h)

/-- **The unique child of a stable ancestor is a stable ancestor**: below `l`, the paths to the taxa start
with the arc to it, when no other arc leaving `l` is ancestral to the taxa. -/
theorem IsStableAncestor.target_of_unique (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial)
    {l : V} (hst : N.IsStableAncestor Y l) {e : E}
    (huniq : ∀ f, N.graph.source f = l → f ∈ N.ancestralArcs Y → f = e) :
    N.IsStableAncestor Y (N.graph.target e) := by
  intro x hx hp
  obtain ⟨-, -, hq⟩ := hp.suffix_of_not_hasPathAvoiding (hst x hx)
  rcases Relation.ReflTransGen.cases_head hq with h | ⟨a, ⟨⟨f, hfs, hft⟩, -, ha⟩, hat⟩
  · exact hst.leaf_ne hN hY x h.symm
  · have hfa : f ∈ N.ancestralArcs Y := by
      refine ⟨x, hx, ?_⟩
      rw [hft]
      exact Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hat
    rw [huniq f hfs hfa] at hft
    exact ha hft.symm

/-- **The LSA does not have just one child below it**, else that child would be a lower stable ancestor. -/
theorem lsaNetwork_outdegree_root_ne_one (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial) :
    (lsaNetwork hN Y hY.nonempty).graph.outdegree (lsaNetwork hN Y hY.nonempty).root ≠ 1 := by
  intro h
  obtain ⟨e, he⟩ := (DirectedMultigraph.outdegree_eq_one_iff _ _).mp h
  obtain ⟨hst, hleast⟩ := lsa_spec hN Y hY.nonempty
  have hes : N.graph.source e.1 = lsa hN Y hY.nonempty := congrArg Subtype.val ((he e).mpr rfl)
  have hc := hleast _ (hst.target_of_unique hN hY (e := e.1) fun f hfs hfa => by
    have hf : f ∈ N.belowArcs (lsa hN Y hY.nonempty) Y := ⟨by rw [hfs]; exact .refl, hfa⟩
    exact congrArg Subtype.val ((he ⟨f, hf⟩).mp (Subtype.ext hfs)))
  refine hN.acyclic _ (Relation.TransGen.head' ⟨e.1, hes, rfl⟩ hc)

/-- The root of the part below the LSA has outdegree two. -/
theorem lsaNetwork_outdegree_root (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {Y : Set X}
    (hY : Y.Nontrivial) :
    (lsaNetwork hN Y hY.nonempty).graph.outdegree (lsaNetwork hN Y hY.nonempty).root = 2 := by
  have : Finite E := hN.finite_arcs
  have hne := lsaNetwork_outdegree_root_ne_one hN hY
  have hst := (lsa_spec hN Y hY.nonempty).1
  have h0 : (lsaNetwork hN Y hY.nonempty).graph.outdegree (lsaNetwork hN Y hY.nonempty).root ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := ((lsaNetwork_isPhylogenetic hN hY).leaves _).mp h
    exact hst.leaf_ne hN hY x.1 (congrArg Subtype.val hx)
  have hle : (lsaNetwork hN Y hY.nonempty).graph.outdegree (lsaNetwork hN Y hY.nonempty).root ≤
      N.graph.outdegree (lsa hN Y hY.nonempty) :=
    belowNetwork_outdegree_le _
  have hle2 : N.graph.outdegree (lsa hN Y hY.nonempty) ≤ 2 := by
    by_cases hr : lsa hN Y hY.nonempty = N.root
    · rw [hr, hBin.1]
    · have h₁ := hN.nonroot_indegree _ hr
      have h₂ := hBin.2 _ hr (by omega)
      omega
  omega

/-- **The vertices kept below the LSA have degree three**, or are taxa. A kept vertex of indegree one with
one retained child is suppressed, and a reticulation keeps its two parents. -/
theorem lsaNetwork_degree_three (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {Y : Set X}
    (hY : Y.Nontrivial) (v : N.belowVertices (lsa hN Y hY.nonempty) Y)
    (hv : ¬ (lsaNetwork hN Y hY.nonempty).IsChainVertex v)
    (hroot : v.1 ≠ lsa hN Y hY.nonempty) (h0 : (lsaNetwork hN Y hY.nonempty).graph.outdegree v ≠ 0) :
    (lsaNetwork hN Y hY.nonempty).graph.indegree v +
      (lsaNetwork hN Y hY.nonempty).graph.outdegree v = 3 := by
  have : Finite E := hN.finite_arcs
  have hst := (lsa_spec hN Y hY.nonempty).1
  have hin : (lsaNetwork hN Y hY.nonempty).graph.indegree v = N.graph.indegree v.1 :=
    belowNetwork_indegree hN hst v hroot
  have hout : (lsaNetwork hN Y hY.nonempty).graph.outdegree v ≤ N.graph.outdegree v.1 :=
    belowNetwork_outdegree_le v
  have hvr : v.1 ≠ N.root := fun h => hroot <|
    eq_of_reaches_of_reaches hN.acyclic (h ▸ hN.root_reaches _) v.2.1
  have h3 := hBin.2 v.1 hvr (by omega)
  have h1 := hN.nonroot_indegree _ hvr
  have hnc : ¬ ((lsaNetwork hN Y hY.nonempty).graph.indegree v = 1 ∧
      (lsaNetwork hN Y hY.nonempty).graph.outdegree v = 1) := hv
  omega

/-- **The induced network of a binary network is binary**, for at least two taxa. A retained vertex of
indegree one with one retained child is suppressed; a reticulation keeps its two parents, since every parent
of a vertex strictly below the LSA is itself below the LSA and ancestral to `Y`; the LSA has outdegree two
below it, else its unique child would be a lower stable ancestor. -/
theorem inducedNetwork_isBinary (hN : N.IsPhylogenetic) (hBin : N.IsBinary) {Y : Set X}
    (hY : Y.Nontrivial) : (inducedNetwork hN Y hY).IsBinary := by
  have hM := lsaNetwork_isPhylogenetic hN hY
  refine ⟨?_, fun v hv h0 => ?_⟩
  · exact (suppress_outdegree hM _).trans (lsaNetwork_outdegree_root hN hBin hY)
  · have hv' : v.1.1 ≠ lsa hN Y hY.nonempty := fun h =>
      hv (Subtype.ext (Subtype.ext h))
    change ((lsaNetwork hN Y hY.nonempty).suppress hM).graph.indegree v +
      ((lsaNetwork hN Y hY.nonempty).suppress hM).graph.outdegree v = 3
    rw [suppress_indegree, suppress_outdegree]
    exact lsaNetwork_degree_three hN hBin hY v.1 v.2 hv' fun h => h0 ((suppress_outdegree hM v).trans h)

/-! ### Null sets of parameters -/

section Null

variable {V' E' X' : Type*}

/-- **Preimages of null sets of parameters are null**, for a map of parameters that, for each choice of the
left-out coordinates of `N`, reads in some choice for `N'` as a surjective linear map of the coordinates. -/
theorem isGenericNull_comap [Fintype E] [Fintype E'] {N : RootedNetwork V E X}
    {N' : RootedNetwork V' E' X'} (φ : MetricData E → MetricData E')
    (hφ : ∀ θ, N.IsMetric θ → N'.IsMetric (φ θ))
    (h : ∀ d : V → E, (∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) →
      ∃ d' : V' → E', (∀ v, 2 ≤ N'.graph.indegree v → N'.graph.target (d' v) = v) ∧
        ∃ L : ((E → ℝ) × (E → ℝ)) →ₗ[ℝ] ((E' → ℝ) × (E' → ℝ)), Function.Surjective L ∧
          ∀ (θ : MetricData E) (x : (E → ℝ) × (E → ℝ)), N.IsMetric θ → θ.length = x.1 →
            (∀ e, N.IsHybridArc e → e ≠ d (N.graph.target e) → θ.inheritance e = x.2 e) →
            (φ θ).length = (L x).1 ∧ ∀ e', N'.IsHybridArc e' → e' ≠ d' (N'.graph.target e') →
              (φ θ).inheritance e' = (L x).2 e')
    {A' : Set (MetricData E')} (hA' : IsGenericNull N' A') :
    IsGenericNull N {θ | N.IsMetric θ ∧ φ θ ∈ A'} := by
  intro d hd
  obtain ⟨d', hd', L, hL, hx⟩ := h d hd
  refine measure_mono_null ?_ (Measure.prod_pi_volume_preimage_eq_zero L hL (hA' d' hd'))
  rintro x ⟨θ, ⟨hθ, hφA⟩, -, hℓ, hg⟩
  obtain ⟨h₁, h₂⟩ := hx θ x hθ hℓ hg
  exact ⟨φ θ, hφA, hφ θ hθ, h₁, h₂⟩

end Null

/-- The lengths of a suppressed network, as a linear function of the lengths: sums along chains. -/
def suppressLengthMap [Fintype E] (N : RootedNetwork V E X) :
    (E → ℝ) →ₗ[ℝ] ({e // ¬ N.IsChainVertex (N.graph.source e)} → ℝ) where
  toFun ℓ e := ∑ f with N.IsOnChain e.1 f, ℓ f
  map_add' ℓ ℓ' := by
    funext e
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c ℓ := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Chains are disjoint and each starts with its own arc, so the lengths of the composite arcs can be
anything. -/
theorem suppressLengthMap_surjective [Fintype E] (N : RootedNetwork V E X) :
    Function.Surjective (suppressLengthMap N) := by
  intro ℓ'
  refine ⟨fun f => if h : ¬ N.IsChainVertex (N.graph.source f) then ℓ' ⟨f, h⟩ else 0, ?_⟩
  funext e
  change (∑ f with N.IsOnChain e.1 f,
    if h : ¬ N.IsChainVertex (N.graph.source f) then ℓ' ⟨f, h⟩ else 0) = ℓ' e
  rw [Finset.sum_eq_single_of_mem e.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩)
    ?_, dite_eq_left e.2]
  intro g hg hne
  rcases (Finset.mem_filter.1 hg).2 with h | ⟨hc, -⟩
  · exact absurd h hne
  · exact dite_eq_right (not_not.2 hc)

/-- **Preimages of null sets under suppression are null.** Given the left-out parents `d` on the network,
leave out on the suppressed network, at each reticulation, the composite arc whose last arc is the left-out
parent. The map of coordinates is then linear and surjective: the lengths add along chains, and the inheritance
of a composite arc is that of its last arc. -/
theorem isGenericNull_suppressMetric [Fintype E]
    [Fintype {e // ¬ N.IsChainVertex (N.graph.source e)}] (hN : N.IsPhylogenetic)
    {A' : Set (MetricData {e // ¬ N.IsChainVertex (N.graph.source e)})}
    (hA' : IsGenericNull (N.suppress hN) A') :
    IsGenericNull N {θ | N.IsMetric θ ∧ N.suppressMetric θ ∈ A'} := by
  refine isGenericNull_comap N.suppressMetric (fun θ hθ => isMetric_suppressMetric hN hθ)
    (fun d hd => ⟨fun v => chainHead hN (d v.1), fun v hv => ?_,
      (suppressLengthMap N).prodMap (LinearMap.funLeft ℝ ℝ fun e => chainLast hN e.1), ?_,
      fun θ x hθ hℓ hg => ⟨?_, fun e he hne => ?_⟩⟩) hA'
  · rw [suppress_indegree] at hv
    apply Subtype.ext
    change chainEnd hN (N.graph.target (chainHead hN (d v.1)).1) = v.1
    rw [(isOnChain_chainHead hN (d v.1)).chainEnd_eq hN, hd v.1 hv]
    exact chainEnd_eq_self hN v.2
  · rw [LinearMap.coe_prodMap]
    exact (suppressLengthMap_surjective N).prodMap
      (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ (chainLast_injective hN))
  · funext e
    change (∑ f with N.IsOnChain e.1 f, θ.length f) = ∑ f with N.IsOnChain e.1 f, x.1 f
    rw [hℓ]
  · have hl := (suppress_isHybridArc_iff hN e).1 he
    rw [suppressMetric_inheritance hN hθ]
    refine hg _ hl fun hlast => hne ?_
    have h₁ : chainHead hN (d (N.graph.target (chainLast hN e.1))) = e := by
      rw [← hlast]
      exact chainHead_chainLast hN e.2
    have h₂ : N.graph.target (chainLast hN e.1) = ((N.suppress hN).graph.target e).1 :=
      target_chainLast hN e.1
    rw [h₂] at h₁
    exact h₁.symm

section Below

variable {l : V} {Y : Set X} {hl : l ∈ N.ancestralVertices Y}
  {hleaf : ∀ x ∈ Y, N.graph.Reaches l (N.leaf x)}

/-- **Preimages of null sets under restriction below a stable ancestor are null.** The map of coordinates is
the restriction to the kept arcs, which is linear and surjective. -/
theorem isGenericNull_belowMetric [Fintype E] [Fintype (N.belowArcs l Y)] (hN : N.IsPhylogenetic)
    (hst : N.IsStableAncestor Y l) (e₀ : N.belowArcs l Y) {A : Set (MetricData (N.belowArcs l Y))}
    (hA : IsGenericNull (N.belowNetwork l Y hl hleaf) A) :
    IsGenericNull N {θ | N.IsMetric θ ∧ belowMetric l Y θ ∈ A} := by
  have hval : Function.Injective (Subtype.val : N.belowArcs l Y → E) := Subtype.val_injective
  have htarget : ∀ {d : V → E}, (∀ v, 2 ≤ N.graph.indegree v → N.graph.target (d v) = v) →
      ∀ v : N.belowVertices l Y, 2 ≤ (N.belowNetwork l Y hl hleaf).graph.indegree v →
        v.1 ≠ l ∧ N.graph.target (d v.1) = v.1 := by
    intro d hd v hv
    have hvl : v.1 ≠ l := by
      intro h
      obtain ⟨e, he⟩ := (DirectedMultigraph.one_le_indegree_iff _ v).mp (by omega :
        1 ≤ (N.belowNetwork l Y hl hleaf).graph.indegree v)
      exact target_ne_of_mem_belowArcs hN e ((congrArg Subtype.val he).trans h)
    rw [belowNetwork_indegree hN hst v hvl] at hv
    exact ⟨hvl, hd v.1 hv⟩
  refine isGenericNull_comap (belowMetric l Y) (fun θ hθ => isMetric_belowMetric hN hst hθ)
    (fun d hd => ⟨fun v => if h : d v.1 ∈ N.belowArcs l Y then ⟨d v.1, h⟩ else e₀, fun v hv => ?_,
      (LinearMap.funLeft ℝ ℝ Subtype.val).prodMap (LinearMap.funLeft ℝ ℝ Subtype.val), ?_,
      fun θ x hθ hℓ hg => ⟨?_, fun e he hne => ?_⟩⟩) hA
  · obtain ⟨hvl, ht⟩ := htarget hd v hv
    have hmem : d v.1 ∈ N.belowArcs l Y := mem_belowArcs_of_target hN hst v hvl ht
    simp only [dite_eq_left hmem]
    exact Subtype.ext ht
  · rw [LinearMap.coe_prodMap]
    exact (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval).prodMap
      (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ hval)
  · funext e
    exact congrFun hℓ e.1
  · refine hg e.1 ((belowNetwork_isHybridArc_iff hN hst e).1 he) fun hd' => hne ?_
    have hmem : d (N.graph.target e.1) ∈ N.belowArcs l Y := by
      rw [← hd']
      exact e.2
    change e = if h : d (N.graph.target e.1) ∈ N.belowArcs l Y then ⟨d (N.graph.target e.1), h⟩ else e₀
    rw [dite_eq_left hmem]
    exact Subtype.ext hd'

end Below

/-! ### The induced network -/

/-- At least two taxa give an arc below the LSA. -/
theorem nonempty_lsa_belowArcs (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial) :
    Nonempty (N.belowArcs (lsa hN Y hY.nonempty) Y) := by
  obtain ⟨x, hx⟩ := hY.nonempty
  have hst := (lsa_spec hN Y hY.nonempty).1
  rcases Relation.ReflTransGen.cases_tail (hst.reaches_leaf hN hx) with h | ⟨a, ha, f, hs, ht⟩
  · exact absurd h (hst.leaf_ne hN hY x)
  · refine ⟨⟨f, hs ▸ ha, x, hx, ?_⟩⟩
    rw [ht]
    exact .refl

/-- **The map of parameters sends valid parameters to valid parameters.** -/
theorem isMetric_inducedMetric [Fintype E] (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial)
    [Fintype {e : N.belowArcs (lsa hN Y hY.nonempty) Y //
      ¬ (lsaNetwork hN Y hY.nonempty).IsChainVertex ((lsaNetwork hN Y hY.nonempty).graph.source e)}]
    {θ : MetricData E} (hθ : N.IsMetric θ) :
    (inducedNetwork hN Y hY).IsMetric (inducedMetric hN Y hY.nonempty θ) := by
  let _ : Fintype (N.belowArcs (lsa hN Y hY.nonempty) Y) := Fintype.ofFinite _
  exact isMetric_suppressMetric (lsaNetwork_isPhylogenetic hN hY)
    (isMetric_belowMetric hN (lsa_spec hN Y hY.nonempty).1 hθ)

/-- **Preimages of null sets under the map of parameters are null.** -/
theorem isGenericNull_inducedMetric [Fintype E] (hN : N.IsPhylogenetic) {Y : Set X} (hY : Y.Nontrivial)
    [Fintype {e : N.belowArcs (lsa hN Y hY.nonempty) Y //
      ¬ (lsaNetwork hN Y hY.nonempty).IsChainVertex ((lsaNetwork hN Y hY.nonempty).graph.source e)}]
    {A' : Set (MetricData {e : N.belowArcs (lsa hN Y hY.nonempty) Y //
      ¬ (lsaNetwork hN Y hY.nonempty).IsChainVertex ((lsaNetwork hN Y hY.nonempty).graph.source e)})}
    (hA' : IsGenericNull (inducedNetwork hN Y hY) A') :
    IsGenericNull N {θ | N.IsMetric θ ∧ inducedMetric hN Y hY.nonempty θ ∈ A'} := by
  let _ : Fintype (N.belowArcs (lsa hN Y hY.nonempty) Y) := Fintype.ofFinite _
  have hst := (lsa_spec hN Y hY.nonempty).1
  obtain ⟨e₀⟩ := nonempty_lsa_belowArcs hN hY
  have h₁ := isGenericNull_suppressMetric (lsaNetwork_isPhylogenetic hN hY) hA'
  have h₂ := isGenericNull_belowMetric hN hst e₀ h₁
  intro d hd
  refine measure_mono_null ?_ (h₂ d hd)
  rintro x ⟨θ, ⟨hθ, hA⟩, rest⟩
  exact ⟨θ, ⟨hθ, isMetric_belowMetric hN hst hθ, hA⟩, rest⟩

end Phylogenetics.RootedNetwork
