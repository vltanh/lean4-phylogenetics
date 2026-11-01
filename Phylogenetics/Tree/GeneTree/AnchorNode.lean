module

public import Phylogenetics.Tree.GeneTree.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
/-!
# Anchor nodes of quartets in a rooted binary gene tree

The anchor node of a quartet `ab|ce` displayed by a rooted binary gene tree is the internal node `v`
that separates `a`, `b` and `{c, e}` into three different parts among the leaves below its two
children and the leaves outside it (Mirarab and Warnow, ASTRAL).
`Phylogenetics.GeneTree.parts`, `Phylogenetics.GeneTree.IsAnchor`, and the lemma that a displayed
quartet has exactly one anchor node and a quartet that is not displayed has none
(`Phylogenetics.GeneTree.countP_isAnchor`, `Phylogenetics.GeneTree.existsUnique_isAnchor`,
`Phylogenetics.GeneTree.displays_of_isAnchor`). Only a node whose two subtrees both meet the quartet
can be an anchor node, so the anchor nodes correspond to those of the restriction of the gene tree
to the four taxa, a rooted binary tree with four leaves; its five shapes are checked by computation,
over the `24` ways to place the taxa at the leaves. -/

@[expose] public noncomputable section

open Finset

namespace Phylogenetics

universe u

/-! ### The six orderings of three parts -/

/-- The six permutations of `Fin 3`. -/
private theorem p8abc_univ_perm : (univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 2} := by
  decide

/-- A sum over the permutations `σ` of `Fin 3` of a function of `(σ 0, σ 1, σ 2)` is the sum over
the six orderings of `0, 1, 2`. -/
theorem sum_perm_fin_three {M : Type*} [AddCommMonoid M] (g : Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ σ : Equiv.Perm (Fin 3), g (σ 0) (σ 1) (σ 2) =
      g 0 1 2 + g 1 0 2 + g 0 2 1 + g 2 0 1 + g 1 2 0 + g 2 1 0 := by
  rw [p8abc_univ_perm, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have e1 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have e2 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have e3 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, e1, e2, e3, add_assoc]

/-- There is a permutation `σ` of `Fin 3` with a property of `(σ 0, σ 1, σ 2)` exactly when one of
the six orderings of `0, 1, 2` has it. -/
theorem exists_perm_fin_three (P : Fin 3 → Fin 3 → Fin 3 → Prop) :
    (∃ σ : Equiv.Perm (Fin 3), P (σ 0) (σ 1) (σ 2)) ↔
      P 0 1 2 ∨ P 1 0 2 ∨ P 0 2 1 ∨ P 2 0 1 ∨ P 1 2 0 ∨ P 2 1 0 := by
  have e1 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have e2 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have e3 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have h : (∃ σ : Equiv.Perm (Fin 3), P (σ 0) (σ 1) (σ 2)) ↔
      ∃ σ ∈ (univ : Finset (Equiv.Perm (Fin 3))), P (σ 0) (σ 1) (σ 2) := by
    simp only [Finset.mem_univ, true_and]
  rw [h, p8abc_univ_perm]
  simp only [Finset.exists_mem_insert, Finset.mem_singleton, exists_eq_left,
    Equiv.Perm.coe_one, id_eq, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right, e1, e2, e3]

namespace GeneTree

variable {X : Type u} [DecidableEq X]

/-- The three parts `L_{v1}, L_{v2}, L_{vout}` into which the internal node `v = (G_{v1}, G_{v2})`
of the gene tree `t` separates the taxa of `t`: the leaves of the subtrees below its two children
and the other leaves of `t` (removing `v` and its incident edges leaves three subtrees). At the
root, `L_{vout}` is empty. -/
def parts (t : GeneTree X) (v : GeneTree X × GeneTree X) : Fin 3 → Finset X :=
  ![v.1.leafSet, v.2.leafSet, t.leafSet \ (v.1.leafSet ∪ v.2.leafSet)]

/-- The internal node `v` of the gene tree `t` is an anchor node of the quartet `ab|ce`: it induces
the tripartition `{a}, {b}, {c, e}` on the quartet, that is, `a`, `b` and both of `c, e` lie in
three different parts `L_X, L_Y, L_Z` of `L_{v1}, L_{v2}, L_{vout}`. -/
def IsAnchor (t : GeneTree X) (v : GeneTree X × GeneTree X) (a b c e : X) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), a ∈ t.parts v (σ 0) ∧ b ∈ t.parts v (σ 1) ∧
    c ∈ t.parts v (σ 2) ∧ e ∈ t.parts v (σ 2)

/-- Whether a node is an anchor node is decidable. -/
instance (t : GeneTree X) (v : GeneTree X × GeneTree X) (a b c e : X) :
    Decidable (t.IsAnchor v a b c e) := by
  unfold IsAnchor
  infer_instance

/-! ### Proof of the anchor lemma

The anchor condition at `v` only asks in which of the three parts the four taxa lie: below the
first child, below the second child, or elsewhere (`p8abc_anch`). It is unchanged by restricting
the gene tree to `{a, b, c, e}`, and a node whose two subtrees do not both meet `{a, b, c, e}` is
never an anchor node, so the anchor nodes of `t` correspond to those of its restriction
(`p8abc_countP_anch_restrict`). The restriction is a rooted binary tree on the four taxa, of one of
five shapes, which are checked one by one (`p8abc_countP_anch_four`). -/

/-- The anchor condition at `v` without the gene tree: `a`, `b` and both of `c, e` lie in three
different parts among the taxa below the first subtree, those below the second, and the others; the
six disjuncts are the six orderings, in the order of `Phylogenetics.exists_perm_fin_three`. -/
private def p8abc_anch (a b c e : X) (v : GeneTree X × GeneTree X) : Prop :=
  (a ∈ v.1.leafSet ∧ b ∈ v.2.leafSet ∧ (c ∉ v.1.leafSet ∧ c ∉ v.2.leafSet) ∧
      (e ∉ v.1.leafSet ∧ e ∉ v.2.leafSet)) ∨
    (a ∈ v.2.leafSet ∧ b ∈ v.1.leafSet ∧ (c ∉ v.1.leafSet ∧ c ∉ v.2.leafSet) ∧
      (e ∉ v.1.leafSet ∧ e ∉ v.2.leafSet)) ∨
    (a ∈ v.1.leafSet ∧ (b ∉ v.1.leafSet ∧ b ∉ v.2.leafSet) ∧ c ∈ v.2.leafSet ∧ e ∈ v.2.leafSet) ∨
    ((a ∉ v.1.leafSet ∧ a ∉ v.2.leafSet) ∧ b ∈ v.1.leafSet ∧ c ∈ v.2.leafSet ∧ e ∈ v.2.leafSet) ∨
    (a ∈ v.2.leafSet ∧ (b ∉ v.1.leafSet ∧ b ∉ v.2.leafSet) ∧ c ∈ v.1.leafSet ∧ e ∈ v.1.leafSet) ∨
    ((a ∉ v.1.leafSet ∧ a ∉ v.2.leafSet) ∧ b ∈ v.2.leafSet ∧ c ∈ v.1.leafSet ∧ e ∈ v.1.leafSet)

/-- For four taxa of the gene tree, the anchor condition is `p8abc_anch`: a taxon of the gene tree
lies in `L_{vout}` exactly when it lies below neither subtree of `v`. -/
private theorem p8abc_isAnchor_iff (t : GeneTree X) (v : GeneTree X × GeneTree X) {a b c e : X}
    (ha : a ∈ t.leafSet) (hb : b ∈ t.leafSet) (hc : c ∈ t.leafSet) (he : e ∈ t.leafSet) :
    t.IsAnchor v a b c e ↔ p8abc_anch a b c e v := by
  rw [IsAnchor, exists_perm_fin_three fun i j k =>
    a ∈ t.parts v i ∧ b ∈ t.parts v j ∧ c ∈ t.parts v k ∧ e ∈ t.parts v k]
  simp only [parts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Finset.mem_sdiff, Finset.mem_union, not_or, ha, hb, hc, he,
    true_and, p8abc_anch]

/-- The anchor condition only depends on which of `a, b, c, e` lie below each subtree. -/
private theorem p8abc_anch_congr {a b c e : X} {v w : GeneTree X × GeneTree X}
    (h1 : ∀ x ∈ ({a, b, c, e} : Finset X), x ∈ v.1.leafSet ↔ x ∈ w.1.leafSet)
    (h2 : ∀ x ∈ ({a, b, c, e} : Finset X), x ∈ v.2.leafSet ↔ x ∈ w.2.leafSet) :
    p8abc_anch a b c e v ↔ p8abc_anch a b c e w := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at h1 h2
  simp only [p8abc_anch, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]

/-- If none of `a, b, c, e` lies below the second subtree of `v`, `v` is not an anchor node. -/
private theorem p8abc_not_anch_of_right {a b c e : X} {v : GeneTree X × GeneTree X}
    (h : ∀ x ∈ ({a, b, c, e} : Finset X), x ∉ v.2.leafSet) : ¬ p8abc_anch a b c e v := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at h
  simp [p8abc_anch, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- If none of `a, b, c, e` lies below the first subtree of `v`, `v` is not an anchor node. -/
private theorem p8abc_not_anch_of_left {a b c e : X} {v : GeneTree X × GeneTree X}
    (h : ∀ x ∈ ({a, b, c, e} : Finset X), x ∉ v.1.leafSet) : ¬ p8abc_anch a b c e v := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at h
  simp [p8abc_anch, h.1, h.2.1, h.2.2.1, h.2.2.2]

open Classical in
/-- The anchor nodes of `t` correspond to those of its restriction to `{a, b, c, e}`. -/
private theorem p8abc_countP_anch_restrict (a b c e : X) (t : GeneTree X) :
    t.internalNodes.countP (fun v => decide (p8abc_anch a b c e v)) =
      match t.restrict {a, b, c, e} with
      | some q => q.internalNodes.countP (fun v => decide (p8abc_anch a b c e v))
      | none => 0 := by
  induction t with
  | leaf y => by_cases hy : y ∈ ({a, b, c, e} : Finset X) <;> simp [restrict, hy, internalNodes]
  | node l r ihl ihr =>
    set S : Finset X := {a, b, c, e}
    -- a subtree with no leaf in `S` has none of `a, b, c, e`
    have hout : ∀ s : GeneTree X, s.restrict S = none → ∀ x ∈ S, x ∉ s.leafSet :=
      fun s hs x hx hxs => restrict_eq_none_iff.1 hs x (mem_leafSet.1 hxs) hx
    -- below a subtree with a restriction, the taxa of `S` are those of the restriction
    have hin : ∀ s q : GeneTree X, s.restrict S = some q → ∀ x ∈ S, x ∈ s.leafSet ↔ x ∈ q.leafSet :=
      fun s q hq x hx => by rw [leafSet_restrict hq, Finset.mem_inter, and_iff_left hx]
    simp only [internalNodes, List.countP_append, List.countP_cons, List.countP_nil, zero_add]
    rcases hl : l.restrict S with _ | l' <;> rcases hr : r.restrict S with _ | r' <;>
      simp only [hl, hr] at ihl ihr <;> simp only [restrict, hl, hr, ihl, ihr]
    · simp [p8abc_not_anch_of_left (a := a) (b := b) (c := c) (e := e) (v := (l, r)) (hout l hl)]
    · simp [p8abc_not_anch_of_left (a := a) (b := b) (c := c) (e := e) (v := (l, r)) (hout l hl)]
    · simp [p8abc_not_anch_of_right (a := a) (b := b) (c := c) (e := e) (v := (l, r))
        (hout r hr)]
    · have h := p8abc_anch_congr (a := a) (b := b) (c := c) (e := e) (v := (l, r)) (w := (l', r'))
        (hin l l' hl) (hin r r' hr)
      simp only [internalNodes, List.countP_append, List.countP_cons, List.countP_nil, zero_add, h]

omit [DecidableEq X] in
/-- A gene tree with one leaf is a leaf. -/
private theorem p8abc_len_one {s : GeneTree X} (h : s.leaves.length = 1) : ∃ x, s = leaf x := by
  rcases s with x | ⟨l, r⟩
  · exact ⟨x, rfl⟩
  · simp only [leaves, List.length_append] at h
    have := l.one_le_length_leaves
    have := r.one_le_length_leaves
    omega

omit [DecidableEq X] in
/-- A gene tree with two leaves is a cherry. -/
private theorem p8abc_len_two {s : GeneTree X} (h : s.leaves.length = 2) :
    ∃ x y, s = node (leaf x) (leaf y) := by
  rcases s with x | ⟨l, r⟩
  · simp [leaves] at h
  · simp only [leaves, List.length_append] at h
    have := l.one_le_length_leaves
    have := r.one_le_length_leaves
    obtain ⟨x, rfl⟩ := p8abc_len_one (s := l) (by omega)
    obtain ⟨y, rfl⟩ := p8abc_len_one (s := r) (by omega)
    exact ⟨x, y, rfl⟩

omit [DecidableEq X] in
/-- A gene tree with three leaves has one of two shapes. -/
private theorem p8abc_len_three {s : GeneTree X} (h : s.leaves.length = 3) :
    ∃ x y z, s = node (leaf x) (node (leaf y) (leaf z)) ∨
      s = node (node (leaf x) (leaf y)) (leaf z) := by
  rcases s with x | ⟨l, r⟩
  · simp [leaves] at h
  · simp only [leaves, List.length_append] at h
    have := l.one_le_length_leaves
    have := r.one_le_length_leaves
    rcases Nat.lt_or_ge l.leaves.length 2 with h1 | h1
    · obtain ⟨x, rfl⟩ := p8abc_len_one (s := l) (by omega)
      obtain ⟨y, z, rfl⟩ := p8abc_len_two (s := r) (by omega)
      exact ⟨x, y, z, Or.inl rfl⟩
    · obtain ⟨x, y, rfl⟩ := p8abc_len_two (s := l) (by omega)
      obtain ⟨z, rfl⟩ := p8abc_len_one (s := r) (by omega)
      exact ⟨x, y, z, Or.inr rfl⟩

omit [DecidableEq X] in
/-- A gene tree with four leaves has one of five shapes; its leaves are `x 0, x 1, x 2, x 3`, from
left to right. -/
private theorem p8abc_shapes {q : GeneTree X} (h : q.leaves.length = 4) :
    ∃ x : Fin 4 → X,
      q = node (leaf (x 0)) (node (leaf (x 1)) (node (leaf (x 2)) (leaf (x 3)))) ∨
      q = node (leaf (x 0)) (node (node (leaf (x 1)) (leaf (x 2))) (leaf (x 3))) ∨
      q = node (node (leaf (x 0)) (leaf (x 1))) (node (leaf (x 2)) (leaf (x 3))) ∨
      q = node (node (leaf (x 0)) (node (leaf (x 1)) (leaf (x 2)))) (leaf (x 3)) ∨
      q = node (node (node (leaf (x 0)) (leaf (x 1))) (leaf (x 2))) (leaf (x 3)) := by
  rcases q with x | ⟨l, r⟩
  · simp [leaves] at h
  · simp only [leaves, List.length_append] at h
    have := l.one_le_length_leaves
    have := r.one_le_length_leaves
    rcases (show l.leaves.length = 1 ∨ l.leaves.length = 2 ∨ l.leaves.length = 3 by omega) with
      h1 | h1 | h1
    · obtain ⟨x0, rfl⟩ := p8abc_len_one h1
      obtain ⟨x1, x2, x3, rfl | rfl⟩ := p8abc_len_three (s := r) (by omega)
      · exact ⟨![x0, x1, x2, x3], Or.inl rfl⟩
      · exact ⟨![x0, x1, x2, x3], Or.inr (Or.inl rfl)⟩
    · obtain ⟨x0, x1, rfl⟩ := p8abc_len_two h1
      obtain ⟨x2, x3, rfl⟩ := p8abc_len_two (s := r) (by omega)
      exact ⟨![x0, x1, x2, x3], Or.inr (Or.inr (Or.inl rfl))⟩
    · obtain ⟨x3, rfl⟩ := p8abc_len_one (s := r) (by omega)
      obtain ⟨x0, x1, x2, rfl | rfl⟩ := p8abc_len_three h1
      · exact ⟨![x0, x1, x2, x3], Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨![x0, x1, x2, x3], Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- The check of one shape: both sides only depend on the positions `ia, ib, ic, ie` of
`a, b, c, e` among the leaves, and each of the `24` placements is computed. -/
local macro "p8abc_shape_tac" : tactic => `(tactic| (
  intro x hx ia ib ic ie hab hac hae hbc hbe hce
  simp [p8abc_anch, internalNodes, clusters, leafSet, leaves, geneTreeDisplays, hx.eq_iff,
    List.countP_cons]
  fin_cases ia <;> fin_cases ib <;> (try exact absurd rfl hab) <;> fin_cases ic <;>
    (try exact absurd rfl hac) <;> (try exact absurd rfl hbc) <;> fin_cases ie <;>
    (try exact absurd rfl hae) <;> (try exact absurd rfl hbe) <;> (try exact absurd rfl hce) <;>
    simp))

open Classical in
/-- The anchor lemma for the caterpillar `(x₀, (x₁, (x₂, x₃)))`, with `a, b, c, e` at the leaves
`ia, ib, ic, ie`. -/
private theorem p8abc_shapeA : ∀ x : Fin 4 → X, Function.Injective x →
    ∀ ia ib ic ie : Fin 4, ia ≠ ib → ia ≠ ic → ia ≠ ie → ib ≠ ic → ib ≠ ie → ic ≠ ie →
    (node (leaf (x 0)) (node (leaf (x 1)) (node (leaf (x 2)) (leaf (x 3))))).internalNodes.countP
        (fun v => decide (p8abc_anch (x ia) (x ib) (x ic) (x ie) v)) =
      if geneTreeDisplays
          (node (leaf (x 0)) (node (leaf (x 1)) (node (leaf (x 2)) (leaf (x 3))))).clusters
          (x ia) (x ib) (x ic) (x ie) then 1 else 0 := by
  p8abc_shape_tac

open Classical in
/-- The anchor lemma for `(x₀, ((x₁, x₂), x₃))`, with `a, b, c, e` at the leaves
`ia, ib, ic, ie`. -/
private theorem p8abc_shapeB : ∀ x : Fin 4 → X, Function.Injective x →
    ∀ ia ib ic ie : Fin 4, ia ≠ ib → ia ≠ ic → ia ≠ ie → ib ≠ ic → ib ≠ ie → ic ≠ ie →
    (node (leaf (x 0)) (node (node (leaf (x 1)) (leaf (x 2))) (leaf (x 3)))).internalNodes.countP
        (fun v => decide (p8abc_anch (x ia) (x ib) (x ic) (x ie) v)) =
      if geneTreeDisplays
          (node (leaf (x 0)) (node (node (leaf (x 1)) (leaf (x 2))) (leaf (x 3)))).clusters
          (x ia) (x ib) (x ic) (x ie) then 1 else 0 := by
  p8abc_shape_tac

open Classical in
/-- The anchor lemma for the balanced tree `((x₀, x₁), (x₂, x₃))`, with `a, b, c, e` at the leaves
`ia, ib, ic, ie`. -/
private theorem p8abc_shapeC : ∀ x : Fin 4 → X, Function.Injective x →
    ∀ ia ib ic ie : Fin 4, ia ≠ ib → ia ≠ ic → ia ≠ ie → ib ≠ ic → ib ≠ ie → ic ≠ ie →
    (node (node (leaf (x 0)) (leaf (x 1))) (node (leaf (x 2)) (leaf (x 3)))).internalNodes.countP
        (fun v => decide (p8abc_anch (x ia) (x ib) (x ic) (x ie) v)) =
      if geneTreeDisplays
          (node (node (leaf (x 0)) (leaf (x 1))) (node (leaf (x 2)) (leaf (x 3)))).clusters
          (x ia) (x ib) (x ic) (x ie) then 1 else 0 := by
  p8abc_shape_tac

open Classical in
/-- The anchor lemma for `((x₀, (x₁, x₂)), x₃)`, with `a, b, c, e` at the leaves
`ia, ib, ic, ie`. -/
private theorem p8abc_shapeD : ∀ x : Fin 4 → X, Function.Injective x →
    ∀ ia ib ic ie : Fin 4, ia ≠ ib → ia ≠ ic → ia ≠ ie → ib ≠ ic → ib ≠ ie → ic ≠ ie →
    (node (node (leaf (x 0)) (node (leaf (x 1)) (leaf (x 2)))) (leaf (x 3))).internalNodes.countP
        (fun v => decide (p8abc_anch (x ia) (x ib) (x ic) (x ie) v)) =
      if geneTreeDisplays
          (node (node (leaf (x 0)) (node (leaf (x 1)) (leaf (x 2)))) (leaf (x 3))).clusters
          (x ia) (x ib) (x ic) (x ie) then 1 else 0 := by
  p8abc_shape_tac

open Classical in
/-- The anchor lemma for the caterpillar `(((x₀, x₁), x₂), x₃)`, with `a, b, c, e` at the leaves
`ia, ib, ic, ie`. -/
private theorem p8abc_shapeE : ∀ x : Fin 4 → X, Function.Injective x →
    ∀ ia ib ic ie : Fin 4, ia ≠ ib → ia ≠ ic → ia ≠ ie → ib ≠ ic → ib ≠ ie → ic ≠ ie →
    (node (node (node (leaf (x 0)) (leaf (x 1))) (leaf (x 2))) (leaf (x 3))).internalNodes.countP
        (fun v => decide (p8abc_anch (x ia) (x ib) (x ic) (x ie) v)) =
      if geneTreeDisplays
          (node (node (node (leaf (x 0)) (leaf (x 1))) (leaf (x 2))) (leaf (x 3))).clusters
          (x ia) (x ib) (x ic) (x ie) then 1 else 0 := by
  p8abc_shape_tac

open Classical in
/-- The anchor lemma for a gene tree whose taxa are exactly the four taxa of the quartet: it has
one of five shapes (`p8abc_shapes`), each checked by `p8abc_shapeA`, …, `p8abc_shapeE`. -/
private theorem p8abc_countP_anch_four {q : GeneTree X} (hq : q.leaves.Nodup) {a b c e : X}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (hS : q.leafSet = {a, b, c, e}) :
    q.internalNodes.countP (fun v => decide (p8abc_anch a b c e v)) =
      if geneTreeDisplays q.clusters a b c e then 1 else 0 := by
  have hlen : q.leaves.length = 4 := by
    rw [← List.toFinset_card_of_nodup hq]
    change #q.leafSet = 4
    rw [hS, Finset.card_insert_of_notMem (by simp [hab, hac, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbe]), Finset.card_pair hce]
  have hmem : ∀ y ∈ ({a, b, c, e} : Finset X), y ∈ q.leaves := fun y hy => by
    rw [← hS] at hy
    exact mem_leafSet.1 hy
  obtain ⟨x, hshape⟩ := p8abc_shapes hlen
  -- the leaves `x 0, …, x 3` are distinct, and `a, b, c, e` are among them
  have hleaves : q.leaves = [x 0, x 1, x 2, x 3] := by
    rcases hshape with rfl | rfl | rfl | rfl | rfl <;> simp [leaves]
  have hx : Function.Injective x := by
    have hnd := hq
    rw [hleaves] at hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnd
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hidx : ∀ y ∈ ({a, b, c, e} : Finset X), ∃ i, x i = y := fun y hy => by
    have := hmem y hy
    rw [hleaves] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  obtain ⟨ia, rfl⟩ := hidx a (by simp)
  obtain ⟨ib, rfl⟩ := hidx b (by simp)
  obtain ⟨ic, rfl⟩ := hidx c (by simp)
  obtain ⟨ie, rfl⟩ := hidx e (by simp)
  have hab' : ia ≠ ib := fun h => hab (by rw [h])
  have hac' : ia ≠ ic := fun h => hac (by rw [h])
  have hae' : ia ≠ ie := fun h => hae (by rw [h])
  have hbc' : ib ≠ ic := fun h => hbc (by rw [h])
  have hbe' : ib ≠ ie := fun h => hbe (by rw [h])
  have hce' : ic ≠ ie := fun h => hce (by rw [h])
  rcases hshape with rfl | rfl | rfl | rfl | rfl
  · exact p8abc_shapeA x hx _ _ _ _ hab' hac' hae' hbc' hbe' hce'
  · exact p8abc_shapeB x hx _ _ _ _ hab' hac' hae' hbc' hbe' hce'
  · exact p8abc_shapeC x hx _ _ _ _ hab' hac' hae' hbc' hbe' hce'
  · exact p8abc_shapeD x hx _ _ _ _ hab' hac' hae' hbc' hbe' hce'
  · exact p8abc_shapeE x hx _ _ _ _ hab' hac' hae' hbc' hbe' hce'

/-- **Each quartet is counted exactly once** (the anchor nodes of ASTRAL, Mirarab and Warnow): for
distinct taxa `a, b, c, e` and a gene tree with distinct leaf labels, exactly one internal node is
an anchor node of `ab|ce` if the gene tree displays `ab|ce`, and none is otherwise. The proof goes
through the restriction to `{a, b, c, e}` (`p8abc_countP_anch_restrict`,
`p8abc_countP_anch_four`). -/
theorem countP_isAnchor {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (hab : a ≠ b)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    t.internalNodes.countP (fun v => t.IsAnchor v a b c e) =
      if t.Displays a b c e then 1 else 0 := by
  classical
  by_cases hall : a ∈ t.leafSet ∧ b ∈ t.leafSet ∧ c ∈ t.leafSet ∧ e ∈ t.leafSet
  · obtain ⟨ha, hb, hc, he⟩ := hall
    have h1 : t.internalNodes.countP (fun v => t.IsAnchor v a b c e) =
        t.internalNodes.countP (fun v => decide (p8abc_anch a b c e v)) :=
      List.countP_congr fun v _ => by
        simp only [decide_eq_true_eq]
        exact p8abc_isAnchor_iff t v ha hb hc he
    -- the restriction `q` of `t` to the four taxa is a gene tree on exactly these taxa
    obtain ⟨q, hq⟩ : ∃ q, t.restrict {a, b, c, e} = some q := by
      cases h : t.restrict {a, b, c, e} with
      | none => exact absurd (restrict_eq_none_iff.1 h a (mem_leafSet.1 ha)) (by simp)
      | some q => exact ⟨q, rfl⟩
    have hqS : q.leafSet = {a, b, c, e} := by
      rw [leafSet_restrict hq, Finset.inter_eq_right]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hmem : ∀ y ∈ ({a, b, c, e} : Finset X), y ∈ q.leaves := fun y hy => by
      rw [← hqS] at hy
      exact mem_leafSet.1 hy
    -- `t` displays the quartet exactly when `q` does, that is, by the bridge, when
    -- `geneTreeDisplays` holds for the clusters of `q`
    have hq' : q.restrict {a, b, c, e} = some q :=
      restrict_eq_some_self fun x hx => by
        rw [← mem_leafSet, hqS] at hx
        exact hx
    have hdisp : t.Displays a b c e ↔ geneTreeDisplays q.clusters a b c e = true := by
      rw [← displays_iff_geneTreeDisplays hab hac hae hbc hbe hce (hmem a (by simp))
        (hmem b (by simp)) (hmem c (by simp)) (hmem e (by simp))]
      simp only [Displays, hq, hq']
    rw [h1, p8abc_countP_anch_restrict, hq]
    dsimp only
    rw [p8abc_countP_anch_four (nodup_restrict hq ht) hab hac hae hbc hbe hce hqS]
    by_cases hd : t.Displays a b c e
    · rw [ite_eq_left (hdisp.1 hd), ite_eq_left hd]
    · rw [ite_eq_right (mt hdisp.2 hd), ite_eq_right hd]
  · -- if one of the four taxa is not a leaf, no node is an anchor node and the quartet is not
    -- displayed
    have h0 : t.internalNodes.countP (fun v => t.IsAnchor v a b c e) = 0 := by
      rw [List.countP_eq_zero]
      intro v hv hanc
      simp only [decide_eq_true_eq] at hanc
      obtain ⟨σ, h1, h2, h3, h4⟩ := hanc
      -- the parts at an internal node are sets of taxa of `t`
      have hsub : ∀ i, t.parts v i ⊆ t.leafSet := by
        have hinf := leaves_infix_of_mem_internalNodes hv
        intro i x hx
        fin_cases i
        · exact mem_leafSet.2 (hinf.subset (List.mem_append_left _ (mem_leafSet.1 hx)))
        · exact mem_leafSet.2 (hinf.subset (List.mem_append_right _ (mem_leafSet.1 hx)))
        · exact (Finset.mem_sdiff.1 hx).1
      exact hall ⟨hsub _ h1, hsub _ h2, hsub _ h3, hsub _ h4⟩
    have hnd : ¬ t.Displays a b c e := by
      rintro ⟨q, hq, hqS, -⟩
      have hsub : ∀ y ∈ ({a, b, c, e} : Finset X), y ∈ t.leafSet := fun y hy => by
        rw [← hqS, leafSet_restrict hq] at hy
        exact (Finset.mem_inter.1 hy).1
      exact hall ⟨hsub a (by simp), hsub b (by simp), hsub c (by simp), hsub e (by simp)⟩
    rw [h0, ite_eq_right hnd]

/-- Each quartet `ab|ce` of distinct taxa that a gene tree with distinct leaf labels displays has
exactly one anchor node. -/
theorem existsUnique_isAnchor {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (hab : a ≠ b)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    (h : t.Displays a b c e) :
    ∃ v ∈ t.internalNodes, t.IsAnchor v a b c e ∧
      ∀ v' ∈ t.internalNodes, t.IsAnchor v' a b c e → v' = v := by
  have hc := countP_isAnchor ht hab hac hae hbc hbe hce
  rw [ite_eq_left h, List.countP_eq_length_filter, List.length_eq_one_iff] at hc
  obtain ⟨v, hv⟩ := hc
  have hvmem : v ∈ t.internalNodes.filter (fun v => t.IsAnchor v a b c e) := by
    rw [hv]
    exact List.mem_singleton_self v
  rw [List.mem_filter, decide_eq_true_eq] at hvmem
  refine ⟨v, hvmem.1, hvmem.2, fun v' hv' ha' => ?_⟩
  have h' : v' ∈ t.internalNodes.filter (fun v => t.IsAnchor v a b c e) :=
    List.mem_filter.2 ⟨hv', decide_eq_true ha'⟩
  rw [hv] at h'
  exact List.mem_singleton.1 h'

/-- A quartet of distinct taxa with an anchor node in a gene tree with distinct leaf labels is
displayed. -/
theorem displays_of_isAnchor {t : GeneTree X} (ht : t.leaves.Nodup) {a b c e : X} (hab : a ≠ b)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e)
    {v : GeneTree X × GeneTree X} (hv : v ∈ t.internalNodes) (h : t.IsAnchor v a b c e) :
    t.Displays a b c e := by
  by_contra hd
  have hc := countP_isAnchor ht hab hac hae hbc hbe hce
  rw [ite_eq_right hd] at hc
  have hpos : 0 < t.internalNodes.countP (fun v => t.IsAnchor v a b c e) :=
    List.countP_pos_iff.2 ⟨v, hv, decide_eq_true h⟩
  omega

end GeneTree

end Phylogenetics
