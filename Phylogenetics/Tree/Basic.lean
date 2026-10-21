module

public import Phylogenetics.Defs
/-!
# Rooted binary gene trees

Rooted binary trees whose leaves are labelled by taxa, as an inductive type
(`Phylogenetics.GeneTree`), with their leaves, their internal nodes, their clusters, the restriction
`G|S` of a gene tree to a set of taxa, and the quartets that a gene tree displays
(`Phylogenetics.GeneTree.Displays`: `G|{a, b, c, e} = ab|ce`).

The NMSC (`Phylogenetics.Net.geneTreeDist`) and `Phylogenetics.geneTreeDisplays` represent a rooted
gene tree by its set of clusters, a `Finset (Finset X)`. The bridge between the two representations
is `Phylogenetics.GeneTree.clusters`, with `Phylogenetics.GeneTree.displays_iff_geneTreeDisplays`: a
gene tree displays a quartet of its taxa exactly when `Phylogenetics.geneTreeDisplays` says so of
its clusters. -/

@[expose] public section

namespace Phylogenetics

universe u

/-- A rooted binary gene tree whose leaves are labelled by taxa of `X`: a leaf
labelled `x`, or an internal node whose two children are the roots of the subtrees `l` and `r`.
The type allows repeated leaf labels; a gene tree `t` has distinct leaf labels when
`t.leaves.Nodup`. -/
inductive GeneTree (X : Type u) where
  | leaf (x : X)
  | node (l r : GeneTree X)

namespace GeneTree

variable {X : Type u}

/-- The labels of the leaves of a gene tree, from left to right. -/
def leaves : GeneTree X → List X
  | leaf x => [x]
  | node l r => l.leaves ++ r.leaves

/-- The internal nodes `V_G` of a gene tree, in postorder (the root last). An internal node `v`
is given by the subtrees `(G_{v1}, G_{v2})` below its two children `v1, v2`; in a gene tree with
distinct leaf labels, these determine `v`. -/
def internalNodes : GeneTree X → List (GeneTree X × GeneTree X)
  | leaf _ => []
  | node l r => l.internalNodes ++ r.internalNodes ++ [(l, r)]

/-- Every gene tree has a leaf. -/
theorem leaves_ne_nil (t : GeneTree X) : t.leaves ≠ [] := by
  induction t with
  | leaf x => simp [leaves]
  | node l r ihl _ => simp [leaves, ihl]

/-- A gene tree has at least one leaf. -/
theorem one_le_length_leaves (t : GeneTree X) : 1 ≤ t.leaves.length :=
  List.length_pos_iff.2 t.leaves_ne_nil

/-- A rooted binary tree with `n` leaves has `n - 1` internal nodes. -/
theorem length_internalNodes (t : GeneTree X) : t.internalNodes.length + 1 = t.leaves.length := by
  induction t with
  | leaf x => simp [internalNodes, leaves]
  | node l r ihl ihr =>
    simp only [internalNodes, leaves, List.length_append, List.length_singleton]
    omega

/-- The leaves below an internal node, those of its two subtrees, form a block of consecutive
leaves of the gene tree. -/
theorem leaves_infix_of_mem_internalNodes {t : GeneTree X} {v : GeneTree X × GeneTree X}
    (hv : v ∈ t.internalNodes) : v.1.leaves ++ v.2.leaves <:+: t.leaves := by
  induction t with
  | leaf x => simp [internalNodes] at hv
  | node l r ihl ihr =>
    simp only [internalNodes, List.mem_append, List.mem_singleton] at hv
    simp only [leaves]
    rcases hv with (hv | hv) | rfl
    · exact (ihl hv).trans (List.prefix_append _ _).isInfix
    · exact (ihr hv).trans (List.suffix_append _ _).isInfix
    · exact List.infix_refl _

/-- In a gene tree with distinct leaf labels, `t.internalNodes` lists the internal nodes without
repetition. -/
theorem nodup_internalNodes {t : GeneTree X} (ht : t.leaves.Nodup) : t.internalNodes.Nodup := by
  induction t with
  | leaf x => simp [internalNodes]
  | node l r ihl ihr =>
    simp only [leaves, List.nodup_append] at ht
    obtain ⟨hl, hr, hlr⟩ := ht
    -- a leaf of the left subtree of an internal node of `l` (or `r`) is a leaf of `l` (or `r`)
    have hsub : ∀ s : GeneTree X, ∀ v ∈ s.internalNodes, ∀ x ∈ v.1.leaves, x ∈ s.leaves :=
      fun s v hv x hx =>
        (leaves_infix_of_mem_internalNodes hv).subset (List.mem_append_left _ hx)
    simp only [internalNodes, List.nodup_append, List.mem_append, List.mem_singleton]
    refine ⟨⟨ihl hl, ihr hr, ?_⟩, List.nodup_singleton _, ?_⟩
    · -- an internal node of `l` is not one of `r`: their leaves would be leaves of both
      rintro v hv w hw rfl
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ v.1.leaves_ne_nil
      exact hlr x (hsub l v hv x hx) x (hsub r v hw x hx) rfl
    · -- the root `(l, r)` is not an internal node of `l` or `r`: its leaves are too many
      rintro v hv w rfl rfl
      rcases hv with hv | hv
      · have := (leaves_infix_of_mem_internalNodes hv).length_le
        simp only [List.length_append] at this
        exact r.leaves_ne_nil (List.length_eq_zero_iff.1 (by omega))
      · have := (leaves_infix_of_mem_internalNodes hv).length_le
        simp only [List.length_append] at this
        exact l.leaves_ne_nil (List.length_eq_zero_iff.1 (by omega))

variable [DecidableEq X]

/-- The set `L_G` of the taxa at the leaves of a gene tree. -/
def leafSet (t : GeneTree X) : Finset X := t.leaves.toFinset

/-- The clusters of a gene tree: for each of its nodes, the set of the taxa at the leaves below it.
The rest of the library represents a rooted gene tree by this set
(`Phylogenetics.geneTreeDisplays`, `Phylogenetics.Net.geneTreeDist`). -/
def clusters : GeneTree X → Finset (Finset X)
  | leaf x => {{x}}
  | node l r => insert (l.leafSet ∪ r.leafSet) (l.clusters ∪ r.clusters)

/-- The restriction `G|S` of a gene tree to the taxa of `S`: the tree that it induces on its leaves
labelled in `S`, in which the nodes left with one child are suppressed; `none` if no leaf is
labelled in `S`. -/
def restrict (S : Finset X) : GeneTree X → Option (GeneTree X)
  | leaf x => if x ∈ S then some (leaf x) else none
  | node l r =>
      match l.restrict S, r.restrict S with
      | some l', some r' => some (node l' r')
      | some l', none => some l'
      | none, r' => r'

/-! ### Leaves, clusters and restrictions -/

/-- A taxon is in `L_G` exactly when it labels a leaf. -/
@[simp]
theorem mem_leafSet {t : GeneTree X} {x : X} : x ∈ t.leafSet ↔ x ∈ t.leaves :=
  List.mem_toFinset

/-- The taxon at a leaf. -/
theorem leafSet_leaf (x : X) : (leaf x).leafSet = {x} := by
  simp [leafSet, leaves]

/-- The leaves of a gene tree are those of the subtrees below the children of its root. -/
theorem leafSet_node (l r : GeneTree X) : (node l r).leafSet = l.leafSet ∪ r.leafSet := by
  simp [leafSet, leaves, List.toFinset_append]

/-- The set of all the taxa of a gene tree is its cluster at the root. -/
theorem leafSet_mem_clusters (t : GeneTree X) : t.leafSet ∈ t.clusters := by
  cases t with
  | leaf x => simp [clusters, leafSet_leaf]
  | node l r => simp [clusters, leafSet_node]

/-- A cluster is a set of taxa of the gene tree. -/
theorem subset_leafSet_of_mem_clusters {t : GeneTree X} {C : Finset X} (hC : C ∈ t.clusters) :
    C ⊆ t.leafSet := by
  induction t with
  | leaf x =>
    rw [clusters, Finset.mem_singleton] at hC
    rw [hC, leafSet_leaf]
  | node l r ihl ihr =>
    rw [clusters, Finset.mem_insert, Finset.mem_union] at hC
    rw [leafSet_node]
    rcases hC with rfl | hC | hC
    · exact subset_rfl
    · exact (ihl hC).trans Finset.subset_union_left
    · exact (ihr hC).trans Finset.subset_union_right

/-- The restriction to `S` is empty exactly when no leaf is labelled in `S`. -/
theorem restrict_eq_none_iff {S : Finset X} {t : GeneTree X} :
    t.restrict S = none ↔ ∀ x ∈ t.leaves, x ∉ S := by
  induction t with
  | leaf y => by_cases hy : y ∈ S <;> simp [restrict, leaves, hy]
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append]
    rcases hl : l.restrict S with _ | l' <;> rcases hr : r.restrict S with _ | r' <;>
      simp only [hl, hr, reduceCtorEq, true_iff, false_iff, not_forall, not_not] at ihl ihr <;>
      simp only [restrict, hl, hr, reduceCtorEq, true_iff, false_iff, not_forall, not_not]
    · exact fun x hx => hx.elim (ihl x) (ihr x)
    · obtain ⟨x, hx, hxS⟩ := ihr
      exact ⟨x, Or.inr hx, hxS⟩
    · obtain ⟨x, hx, hxS⟩ := ihl
      exact ⟨x, Or.inl hx, hxS⟩
    · obtain ⟨x, hx, hxS⟩ := ihl
      exact ⟨x, Or.inl hx, hxS⟩

/-- The leaves of the restriction to `S` are the leaves labelled in `S`, in the same order. -/
theorem leaves_restrict {S : Finset X} {t q : GeneTree X} (h : t.restrict S = some q) :
    q.leaves = t.leaves.filter (· ∈ S) := by
  induction t generalizing q with
  | leaf y =>
    by_cases hy : y ∈ S
    · simp only [restrict, hy, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [leaves, hy]
    · simp [restrict, hy] at h
  | node l r ihl ihr =>
    have hnil : ∀ s : GeneTree X, s.restrict S = none → s.leaves.filter (· ∈ S) = [] :=
      fun s hs => List.filter_eq_nil_iff.2 fun x hx => by
        simpa using restrict_eq_none_iff.1 hs x hx
    simp only [leaves, List.filter_append]
    rcases hl : l.restrict S with _ | l' <;> rcases hr : r.restrict S with _ | r' <;>
      simp only [restrict, hl, hr, Option.some.injEq, reduceCtorEq] at h
    · subst h
      rw [hnil l hl, ihr hr, List.nil_append]
    · subst h
      rw [hnil r hr, ihl hl, List.append_nil]
    · subst h
      simp only [leaves, ihl hl, ihr hr]

/-- A gene tree whose leaves are all labelled in `S` is its own restriction to `S`. -/
theorem restrict_eq_some_self {S : Finset X} {t : GeneTree X} (h : ∀ x ∈ t.leaves, x ∈ S) :
    t.restrict S = some t := by
  induction t with
  | leaf y => simp [restrict, h y (by simp [leaves])]
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append] at h
    simp only [restrict, ihl fun x hx => h x (Or.inl hx), ihr fun x hx => h x (Or.inr hx)]

/-- The taxa of the restriction to `S` are the taxa of the gene tree in `S`. -/
theorem leafSet_restrict {S : Finset X} {t q : GeneTree X} (h : t.restrict S = some q) :
    q.leafSet = t.leafSet ∩ S := by
  ext x
  simp [leaves_restrict h]

/-- The restriction of a gene tree with distinct leaf labels has distinct leaf labels. -/
theorem nodup_restrict {S : Finset X} {t q : GeneTree X} (h : t.restrict S = some q)
    (ht : t.leaves.Nodup) : q.leaves.Nodup := by
  rw [leaves_restrict h]
  exact ht.filter _

/-- The clusters of the restriction to `S` are the nonempty traces `C ∩ S` of the clusters `C` of
the gene tree. -/
theorem mem_clusters_restrict {S : Finset X} {t q : GeneTree X} (h : t.restrict S = some q)
    {D : Finset X} : D ∈ q.clusters ↔ D.Nonempty ∧ ∃ C ∈ t.clusters, C ∩ S = D := by
  induction t generalizing q with
  | leaf y =>
    by_cases hy : y ∈ S
    · simp only [restrict, hy, ↓reduceIte, Option.some.injEq] at h
      subst h
      have : ({y} : Finset X) ∩ S = {y} := by simp [hy]
      simp only [clusters, Finset.mem_singleton, exists_eq_left, this]
      constructor
      · rintro rfl
        exact ⟨Finset.singleton_nonempty y, rfl⟩
      · exact fun h => h.2.symm
    · simp [restrict, hy] at h
  | node l r ihl ihr =>
    -- the clusters of a subtree with no leaf in `S` have empty traces
    have htr : ∀ s : GeneTree X, s.restrict S = none → ∀ C ∈ s.clusters, C ∩ S = ∅ := by
      intro s hs C hC
      refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
      rw [Finset.mem_inter] at hx
      exact restrict_eq_none_iff.1 hs x (mem_leafSet.1 (subset_leafSet_of_mem_clusters hC hx.1))
        hx.2
    have hroot : (l.leafSet ∪ r.leafSet) ∩ S = l.leafSet ∩ S ∪ r.leafSet ∩ S :=
      Finset.union_inter_distrib_right _ _ _
    have hne : ∀ s : GeneTree X, s.leafSet.Nonempty := fun s => by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ s.leaves_ne_nil
      exact ⟨x, mem_leafSet.2 hx⟩
    simp only [clusters, Finset.mem_insert, Finset.mem_union, or_and_right, exists_or,
      exists_eq_left]
    rcases hl : l.restrict S with _ | l' <;> rcases hr : r.restrict S with _ | r' <;>
      simp only [restrict, hl, hr, Option.some.injEq, reduceCtorEq] at h
    · -- only `r` has leaves in `S`: the restriction is `r'`
      subst h
      have hlS : l.leafSet ∩ S = ∅ := htr l hl _ (leafSet_mem_clusters l)
      rw [ihr hr, hroot, hlS, Finset.empty_union, ← leafSet_restrict hr]
      constructor
      · rintro ⟨hD, C, hC, rfl⟩
        exact ⟨hD, Or.inr (Or.inr ⟨C, hC, rfl⟩)⟩
      · rintro ⟨hD, rfl | ⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩⟩
        · exact ⟨hD, r.leafSet, leafSet_mem_clusters r, (leafSet_restrict hr).symm⟩
        · rw [htr l hl C hC] at hD
          exact absurd hD Finset.not_nonempty_empty
        · exact ⟨hD, C, hC, rfl⟩
    · -- only `l` has leaves in `S`: the restriction is `l'`
      subst h
      have hrS : r.leafSet ∩ S = ∅ := htr r hr _ (leafSet_mem_clusters r)
      rw [ihl hl, hroot, hrS, Finset.union_empty, ← leafSet_restrict hl]
      constructor
      · rintro ⟨hD, C, hC, rfl⟩
        exact ⟨hD, Or.inr (Or.inl ⟨C, hC, rfl⟩)⟩
      · rintro ⟨hD, rfl | ⟨C, hC, rfl⟩ | ⟨C, hC, rfl⟩⟩
        · exact ⟨hD, l.leafSet, leafSet_mem_clusters l, (leafSet_restrict hl).symm⟩
        · exact ⟨hD, C, hC, rfl⟩
        · rw [htr r hr C hC] at hD
          exact absurd hD Finset.not_nonempty_empty
    · -- both have leaves in `S`: the restriction is `node l' r'`
      subst h
      simp only [clusters, Finset.mem_insert, Finset.mem_union, ihl hl, ihr hr, hroot,
        ← leafSet_restrict hl, ← leafSet_restrict hr]
      constructor
      · rintro (rfl | h | h)
        · exact ⟨(hne l').mono Finset.subset_union_left, Or.inl rfl⟩
        · exact ⟨h.1, Or.inr (Or.inl h.2)⟩
        · exact ⟨h.1, Or.inr (Or.inr h.2)⟩
      · rintro ⟨hD, rfl | h | h⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hD, h⟩)
        · exact Or.inr (Or.inr ⟨hD, h⟩)

/-- The gene tree displays the quartet `ab|ce`, written `G|{a, b, c, e} = ab|ce`: its restriction
to `{a, b, c, e}` is a tree whose leaves are these four taxa and whose unrooted topology is
`ab|ce`, that is, in which `{a, b}` or `{c, e}` is a cluster (the edge above that cluster separates
`a, b` from `c, e`).

Convention: a quartet one of whose taxa is not a leaf of the gene tree is not displayed, since its
restriction is not a quartet tree. (`Phylogenetics.geneTreeDisplays` can hold for such a quartet;
with this convention, sums over the quartets displayed by a gene tree run over its taxa.) -/
def Displays (t : GeneTree X) (a b c e : X) : Prop :=
  ∃ q, t.restrict {a, b, c, e} = some q ∧ q.leafSet = {a, b, c, e} ∧
    ({a, b} ∈ q.clusters ∨ {c, e} ∈ q.clusters)

/-- Whether a gene tree displays a quartet is decidable: compute the restriction. -/
instance (t : GeneTree X) (a b c e : X) : Decidable (t.Displays a b c e) :=
  match h : t.restrict {a, b, c, e} with
  | some q => decidable_of_iff (q.leafSet = {a, b, c, e} ∧
      ({a, b} ∈ q.clusters ∨ {c, e} ∈ q.clusters)) (by simp [Displays, h])
  | none => isFalse (by simp [Displays, h])

/-- **The bridge to gene trees given by their clusters.** For distinct taxa `a, b, c, e` that are
leaves of the gene tree, it displays `ab|ce` exactly when `Phylogenetics.geneTreeDisplays` says so
of its clusters: some cluster contains `a` and `b` but neither `c` nor `e`, or contains `c` and `e`
but neither `a` nor `b`. -/
theorem displays_iff_geneTreeDisplays {t : GeneTree X} {a b c e : X} (hab : a ≠ b) (hac : a ≠ c)
    (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) (ha : a ∈ t.leaves)
    (hb : b ∈ t.leaves) (hc : c ∈ t.leaves) (he : e ∈ t.leaves) :
    t.Displays a b c e ↔ geneTreeDisplays t.clusters a b c e = true := by
  unfold Displays
  set S : Finset X := {a, b, c, e} with hS
  -- the restriction to the four taxa is a tree on exactly these taxa
  obtain ⟨q, hq⟩ : ∃ q, t.restrict S = some q := by
    cases h : t.restrict S with
    | none => exact absurd (restrict_eq_none_iff.1 h a ha) (by simp [S])
    | some q => exact ⟨q, rfl⟩
  have hqS : q.leafSet = S := by
    rw [leafSet_restrict hq, Finset.inter_eq_right]
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simpa
  -- the trace of a cluster on the four taxa is `{x, y}` exactly when it contains `x, y` and
  -- neither `z` nor `w`
  have trace : ∀ (C : Finset X) (x y z w : X), x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w →
      (C ∩ {x, y, z, w} = {x, y} ↔ x ∈ C ∧ y ∈ C ∧ z ∉ C ∧ w ∉ C) := by
    intro C x y z w hxy hxz hxw hyz hyw
    constructor
    · intro h
      have hm : ∀ u, u ∈ C ∩ {x, y, z, w} ↔ u ∈ ({x, y} : Finset X) := fun u => by rw [h]
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hm
      refine ⟨((hm x).2 (Or.inl rfl)).1, ((hm y).2 (Or.inr rfl)).1, fun hz => ?_, fun hw => ?_⟩
      · rcases (hm z).1 ⟨hz, Or.inr (Or.inr (Or.inl rfl))⟩ with h | h
        · exact hxz h.symm
        · exact hyz h.symm
      · rcases (hm w).1 ⟨hw, Or.inr (Or.inr (Or.inr rfl))⟩ with h | h
        · exact hxw h.symm
        · exact hyw h.symm
    · rintro ⟨hx, hy, hz, hw⟩
      ext u
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hu hz
        · exact absurd hu hw
      · rintro (rfl | rfl)
        · exact ⟨hx, Or.inl rfl⟩
        · exact ⟨hy, Or.inr (Or.inl rfl)⟩
  have hSce : S = {c, e, a, b} := by
    ext u
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hab' : ∀ C : Finset X, C ∩ S = {a, b} ↔ a ∈ C ∧ b ∈ C ∧ c ∉ C ∧ e ∉ C :=
    fun C => trace C a b c e hab hac hae hbc hbe
  have hce' : ∀ C : Finset X, C ∩ S = {c, e} ↔ c ∈ C ∧ e ∈ C ∧ a ∉ C ∧ b ∉ C := fun C => by
    rw [hSce]
    exact trace C c e a b hce hac.symm hbc.symm hae.symm hbe.symm
  rw [geneTreeDisplays, decide_eq_true_iff]
  simp only [hq, Option.some.injEq, exists_eq_left', hqS, true_and, mem_clusters_restrict hq,
    hab', hce', Finset.insert_nonempty]
  constructor
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    · exact ⟨C, hC, Or.inl h⟩
    · exact ⟨C, hC, Or.inr h⟩
  · rintro ⟨C, hC, h | h⟩
    · exact Or.inl ⟨C, hC, h⟩
    · exact Or.inr ⟨C, hC, h⟩

end GeneTree

end Phylogenetics
