module

public import Phylogenetics.Tree.Metric
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Phylogenetics.Tree.Splits

/-!
# Neighbor joining is an exact tree builder

The algorithm of N. Saitou, M. Nei, *The neighbor-joining method: a new method for reconstructing
phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406-425, in the formulation of J. A. Studier, K. J. Keppler,
*A note on the neighbor-joining algorithm of Saitou and Nei*, Mol. Biol. Evol. 5 (1988), 729-731, whose
formulas (1) to (4) are `State.Q`, `State.rowSum`, `State.joinedDist` and `State.branch`.

On a current set of `n ≥ 3` active nodes with distances `d`, NJ picks a pair minimizing
`Q(i,j) = (n-2) d(i,j) - r_i - r_j`, with `r_i = ∑_k d(i,k)`, joins it into a new node `u` with
`d(u,k) = (d(i,k) + d(j,k) - d(i,j)) / 2`, and gives its members the branch lengths
`d(i,u) = d(i,j) / 2 + (r_i - r_j) / (2 (n-2))`. Here an active node is a cluster: a set of taxa
(`State.active`), and the node `u` is the union. At `n = 3`, `Q` is constant, and the join with the last edge is
the star (`State.Q_eq_star`, `State.branch_eq_star`, `State.joinedDist_eq_star`).

## What is proved

* `nj tb` is the method, for a rule `tb` breaking ties among the `Q`-minimizers, and `Run` the relation of
  all runs, which allows any way of breaking ties.
* `isExactBuilder_nj`, `nj_spec`, `Run.output_spec`: on the metric of a tree with positive weights, polytomies
  allowed, every run returns a tree refining the tree, with the same weights on the edges of the tree and weight
  zero on the others. `isBinaryTree_nj`, `Run.isBinaryTree`: that tree is binary, on any input.
* `Inv.nbr_of_isQMin`, the classical core: a `Q`-minimizing pair are neighbours. This is the theorem of
  Studier and Keppler 1988 (see also O. Gascuel, *Concerning the NJ algorithm and its unweighted version,
  UNJ*, in Mathematical Hierarchies and Biology, DIMACS Ser. 37 (1997), 149-170, and K. Atteson, *The
  performance of neighbor-joining methods of phylogenetic reconstruction*, Algorithmica 25 (1999), 251-278,
  whose Theorem 4 implies it), for trees with polytomies. `Nbr T A B` says that the only splits
  separating `A` and `B` are their pendant edges, which means that `A ∪ B` is compatible with `T` (`nbr_iff_compat`),
  that is, `A, B` are a cherry of a resolution of `T` (`Nbr.isResolutionOf`), and a cherry of `T` when `T` is binary
  (`cherry_of_isQMin`). A pair that are not neighbours is strictly beaten, so this holds for every minimizer, and no
  tie-break matters.
* `ops_run`, `njOps_le`, `ops_run_le`: the number of elementary operations of an instrumented run (`State.ops`,
  `State.joinCost`), an explicit function of the number `N` of taxa, at most `8 N³`. The `O(N³)` is Studier and
  Keppler's.

## The argument

The argument follows Studier and Keppler in comparing a pair that are not neighbours with a pair of
neighbours, by the difference of their criteria, but differs in how: see `exists_QC_lt_of_not_nbr`. The tree `T`
and its weights are fixed for the whole run; only the clusters change. The current distance is the distance in `T`
between clusters (`clusterDist`), and the pendant edge of a cluster `A` is the edge of `T` with side `A` if there is
one, and an edge of length zero otherwise (`pend`). Then `Q(A,B) = -∑_S w_S g_S(A,B)` over the sides `S` of `T` (`QC_eq`),
where `g_S(A,B)` is `1` if `S` separates `A` and `B`, and otherwise the number of clusters on the side of `S`
not containing them. If `S₀` separates `A, B` and has two clusters on each side, take the side with at most `n/2`
clusters, and in it a least side with at least two clusters; two of its clusters `K, L` are neighbours, and
`g_S(K,L) ≥ g_S(A,B)` for all `S`, strictly at `S₀` (`g_le`, `QC_lt_of_side`). The induction step of the
exactness is `Inv.join`: after joining neighbours, the distances are those of the same tree between the new
clusters (`clusterDist_union_eq`), and the branch lengths are the pendant edges (`branch_eq_pend`).
-/

@[expose] public noncomputable section

open Finset
open scoped Classical

namespace Phylogenetics.NJ

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### The algorithm -/

/-- The state of a run: the active nodes, as clusters of taxa, their current distances, the sides of the
splits recorded so far with their branch lengths, and the number of elementary operations so far (see
`State.joinCost`). -/
structure State (X : Type*) where
  /-- The active nodes. -/
  active : Finset (Finset X)
  /-- The current distances between active nodes. -/
  dist : Finset X → Finset X → ℝ
  /-- The sides of the splits recorded so far. -/
  edges : Finset (Finset X)
  /-- The branch lengths recorded so far. -/
  len : Finset X → ℝ
  /-- The number of elementary operations so far. -/
  ops : ℕ

namespace State

/-- `r_A = ∑_C d(A,C)` over the active nodes. -/
def rowSum (s : State X) (A : Finset X) : ℝ := ∑ C ∈ s.active, s.dist A C

/-- The selection criterion of Studier and Keppler, `Q(A,B) = (n-2) d(A,B) - r_A - r_B`. -/
def Q (s : State X) (A B : Finset X) : ℝ :=
  ((s.active.card : ℝ) - 2) * s.dist A B - s.rowSum A - s.rowSum B

/-- The pair `A, B` of distinct active nodes minimizes `Q`. -/
def IsQMin (s : State X) (A B : Finset X) : Prop :=
  A ∈ s.active ∧ B ∈ s.active ∧ A ≠ B ∧ ∀ C ∈ s.active, ∀ D ∈ s.active, C ≠ D → s.Q A B ≤ s.Q C D

/-- The pairs minimizing `Q`, which a tie-break chooses from. -/
def qMinimizers (s : State X) : Finset (Finset X × Finset X) :=
  s.active.offDiag.filter fun p => s.IsQMin p.1 p.2

/-- The branch length from `A` to the new node joining `A, B`:
`d(A,u) = d(A,B) / 2 + (r_A - r_B) / (2 (n-2))`. -/
def branch (s : State X) (A B : Finset X) : ℝ :=
  s.dist A B / 2 + (s.rowSum A - s.rowSum B) / (2 * ((s.active.card : ℝ) - 2))

/-- The distances after joining `A, B` into the new node `u = A ∪ B`:
`d(u,F) = (d(A,F) + d(B,F) - d(A,B)) / 2`, and `d(u,u) = 0`. -/
def joinedDist (D : Finset X → Finset X → ℝ) (A B E F : Finset X) : ℝ :=
  if E = A ∪ B then
    if F = A ∪ B then 0 else (D A F + D B F - D A B) / 2
  else if F = A ∪ B then (D E A + D E B - D A B) / 2 else D E F

/-- The number of elementary operations of a join of `A, B`. One operation is one real addition, subtraction,
multiplication or division with its operands read from the table of distances, one comparison of reals, one
write to the table, or one update of the set of active nodes or of the list of edges. (A node is a pointer in
an implementation, so that the union of clusters is one update.) These are, in the order of `State.join`:

* the row sums `r_E`: for each active node, one addition for each active node;
* `Q` on the ordered pairs of distinct active nodes, those that `IsQMin` ranges over: `3` arithmetic operations
  each, with `n - 2` counted once, under the branch lengths;
* the search for a minimum: one comparison for each such pair;
* the two branch lengths (`State.branch`): `6` arithmetic operations each;
* the new distances (`State.joinedDist`): for each active node `F` other than `A, B`, `3` arithmetic operations
  and `1` write for `d(u,F)`, and the same for `d(F,u)`; and `1` write for `d(u,u)`;
* the updates: `3` of the active nodes (remove `A, B`, add `u`) and `4` of the edges. -/
def joinCost (s : State X) (A B : Finset X) : ℕ :=
  ∑ _C ∈ s.active, s.active.card + 3 * s.active.offDiag.card + s.active.offDiag.card + 2 * 6 +
    (2 * (4 * ((s.active.erase A).erase B).card) + 1) + (3 + 4)

/-- The join of the active nodes `A, B`: `u = A ∪ B` replaces them, the distances are updated, the two
splits with sides `A` and `B` are recorded with their branch lengths, and the operations are counted. -/
def join (s : State X) (A B : Finset X) : State X where
  active := insert (A ∪ B) ((s.active.erase A).erase B)
  dist := joinedDist s.dist A B
  edges := {A, Aᶜ, B, Bᶜ} ∪ s.edges
  len S :=
    if S = A ∨ S = Aᶜ then s.branch A B else if S = B ∨ S = Bᶜ then s.branch B A else s.len S
  ops := s.ops + s.joinCost A B

/-- The result of a run ending with the active nodes `E, F`: the recorded splits with the last edge, of
length `d(E,F) = r_E = r_F`. With one taxon, the only active node is the set of all taxa, and there is no
edge. -/
def output (s : State X) : Finset (Finset X) × (Finset X → ℝ) :=
  (s.active.filter (· ≠ univ) ∪ s.edges, fun S => if S ∈ s.active then s.rowSum S else s.len S)

/-- The number of table reads of `State.output`. -/
def outputCost (s : State X) : ℕ := ∑ _C ∈ s.active, s.active.card

end State

/-- The initial state on a dissimilarity `d`: the singletons, with the distances `d`. The sum over the
clusters is `d` on singletons, and it spares choosing their elements. Reading `d` takes `N²` operations. -/
def init (d : X → X → ℝ) : State X where
  active := univ.image singleton
  dist A B := ∑ x ∈ A, ∑ y ∈ B, d x y
  edges := ∅
  len _ := 0
  ops := Fintype.card X * Fintype.card X

/-- All the runs of NJ, however ties are broken: as long as there are at least three active nodes, a pair minimizing `Q` is
joined. -/
inductive Run : State X → State X → Prop
  /-- A run may stop. -/
  | done (s : State X) : Run s s
  /-- Join a pair minimizing `Q`, and go on. -/
  | step {s s' : State X} {A B : Finset X} (h3 : 3 ≤ s.active.card) (hAB : s.IsQMin A B)
      (hrun : Run (s.join A B) s') : Run s s'

/-- A way of breaking ties: a choice from each nonempty set of pairs. -/
structure TieBreak (X : Type*) where
  /-- The choice. -/
  pick : Finset (Finset X × Finset X) → Finset X × Finset X
  /-- A choice from a nonempty set lies in it. -/
  pick_mem : ∀ c, c.Nonempty → pick c ∈ c

/-- Some way of breaking ties exists. -/
instance : Nonempty (TieBreak X) :=
  ⟨⟨fun c => if h : c.Nonempty then h.choose else (∅, ∅),
    fun c hc => by simpa only [dite_eq_left hc] using hc.choose_spec⟩⟩

/-- One step of the method: join the pair that the tie-break picks from the minimizers of `Q`. -/
def stepWith (tb : TieBreak X) (s : State X) : State X :=
  s.join (tb.pick s.qMinimizers).1 (tb.pick s.qMinimizers).2

/-- The run of the method: `N - 2` joins, the last of which, with three active nodes, is the star. -/
def run (tb : TieBreak X) (d : X → X → ℝ) : State X :=
  (stepWith tb)^[Fintype.card X - 2] (init d)

/-- **Neighbor joining** with the tie-break `tb`, as a tree builder. -/
def nj (tb : TieBreak X) : TreeBuilder X := fun d => (run tb d).output

omit [Fintype X] in
/-- With three active nodes, the branch lengths of the join are those of the star on them, with the formula
for the third coming from the distances after the join (`joinedDist_eq_star`). -/
theorem State.branch_eq_star {s : State X} {A B C : Finset X} (h : s.active = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hAA : s.dist A A = 0) (hBB : s.dist B B = 0)
    (hBA : s.dist B A = s.dist A B) :
    s.branch A B = (s.dist A B + s.dist A C - s.dist B C) / 2 := by
  have hc : s.active.card = 3 := by rw [h, card_eq_three.2 ⟨A, B, C, hAB, hAC, hBC, rfl⟩]
  have h1 : s.rowSum A = s.dist A B + s.dist A C := by
    rw [State.rowSum, h, sum_insert (by simp [hAB, hAC]), sum_insert (by simp [hBC]), sum_singleton, hAA,
      zero_add]
  have h2 : s.rowSum B = s.dist A B + s.dist B C := by
    rw [State.rowSum, h, sum_insert (by simp [hAB, hAC]), sum_insert (by simp [hBC]), sum_singleton, hBB,
      hBA, zero_add]
  rw [State.branch, h1, h2, hc]
  norm_num
  ring

omit [Fintype X] in
/-- With three active nodes, `Q` does not depend on the pair, so that any pair may be joined: this is the star of
Saitou and Nei. -/
theorem State.Q_eq_star {s : State X} {A B C : Finset X} (h : s.active = {A, B, C})
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hAA : s.dist A A = 0) (hBB : s.dist B B = 0)
    (hBA : s.dist B A = s.dist A B) :
    s.Q A B = -(s.dist A B + s.dist A C + s.dist B C) := by
  have hc : s.active.card = 3 := by rw [h, card_eq_three.2 ⟨A, B, C, hAB, hAC, hBC, rfl⟩]
  have h1 : s.rowSum A = s.dist A B + s.dist A C := by
    rw [State.rowSum, h, sum_insert (by simp [hAB, hAC]), sum_insert (by simp [hBC]), sum_singleton, hAA,
      zero_add]
  have h2 : s.rowSum B = s.dist A B + s.dist B C := by
    rw [State.rowSum, h, sum_insert (by simp [hAB, hAC]), sum_insert (by simp [hBC]), sum_singleton, hBB,
      hBA, zero_add]
  rw [State.Q, h1, h2, hc]
  norm_num
  ring

omit [Fintype X] in
/-- The third branch length of the star: the distance from the new node to the third node. -/
theorem State.joinedDist_eq_star (D : Finset X → Finset X → ℝ) {A B C : Finset X}
    (h : C ≠ A ∪ B) : State.joinedDist D A B (A ∪ B) C = (D A C + D B C - D A B) / 2 := by
  simp [State.joinedDist, h]

/-! ### Compatibility -/

/-- Two sets are compatible as sides of splits. -/
def Compat (A S : Finset X) : Prop := A ⊆ S ∨ S ⊆ A ∨ Disjoint A S ∨ A ∪ S = univ

theorem Compat.symm {A S : Finset X} (h : Compat A S) : Compat S A := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (by rwa [union_comm])))

theorem Compat.compl_right {A S : Finset X} (h : Compat A S) : Compat A Sᶜ := by
  rcases h with h | h | h | h
  · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (h hx))))
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    by_cases hx : x ∈ S
    · exact mem_union_left _ (h hx)
    · exact mem_union_right _ (mem_compl.2 hx)
  · exact Or.inl (subset_compl_iff_disjoint_right.2 h)
  · refine Or.inr (Or.inl fun x hx => ?_)
    have : x ∈ A ∪ S := h ▸ mem_univ x
    exact (mem_union.1 this).resolve_right (mem_compl.1 hx)

theorem Compat.compl_left {A S : Finset X} (h : Compat A S) : Compat Aᶜ S :=
  h.symm.compl_right.symm

/-! ### Clusters -/

/-- The active nodes partition the taxa into nonempty clusters. -/
structure IsClusters (P : Finset (Finset X)) : Prop where
  nonempty : ∀ C ∈ P, C.Nonempty
  disjoint : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D
  cover : ∀ x, ∃ C ∈ P, x ∈ C

namespace IsClusters

variable {P : Finset (Finset X)}

omit [Fintype X] in
theorem eq_of_mem (hd : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) {C D : Finset X} (hC : C ∈ P)
    (hD : D ∈ P) {x : X} (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  by_contra hne
  exact disjoint_left.1 (hd C hC D hD hne) hxC hxD

omit [Fintype X] in
/-- A cluster inside a cluster is that cluster. -/
theorem eq_of_subset (hP : IsClusters P) {C D : Finset X} (hC : C ∈ P) (hD : D ∈ P) (h : C ⊆ D) :
    C = D := by
  obtain ⟨x, hx⟩ := hP.nonempty C hC
  exact eq_of_mem hP.disjoint hC hD hx (h hx)

end IsClusters

/-- The side `S` has every cluster on one of its sides: no cluster has yet swallowed the edge. -/
def Relevant (P : Finset (Finset X)) (S : Finset X) : Prop := ∀ C ∈ P, C ⊆ S ∨ Disjoint C S

/-- The number of clusters inside `S`. -/
def kin (P : Finset (Finset X)) (S : Finset X) : ℕ := (P.filter (· ⊆ S)).card

variable {P : Finset (Finset X)} {T : Finset (Finset X)} {w : Finset X → ℝ}

theorem Relevant.compl {S : Finset X} (h : Relevant P S) : Relevant P Sᶜ := fun C hC => by
  rcases h C hC with h | h
  · exact Or.inr (disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (h hx))
  · exact Or.inl (subset_compl_iff_disjoint_right.2 h)

/-- A cluster is inside the complement of a side exactly when it is not inside the side. -/
theorem subset_compl_iff_not_subset (hP : IsClusters P) {S C : Finset X} (h : Relevant P S)
    (hC : C ∈ P) : C ⊆ Sᶜ ↔ ¬ C ⊆ S := by
  obtain ⟨x, hx⟩ := hP.nonempty C hC
  constructor
  · intro h1 h2
    exact mem_compl.1 (h1 hx) (h2 hx)
  · intro h1
    exact subset_compl_iff_disjoint_right.2 ((h C hC).resolve_left h1)

theorem disjoint_iff_not_subset (hP : IsClusters P) {S C : Finset X} (h : Relevant P S)
    (hC : C ∈ P) : Disjoint C S ↔ ¬ C ⊆ S := by
  rw [← subset_compl_iff_disjoint_right, subset_compl_iff_not_subset hP h hC]

theorem kin_add_kin_compl (hP : IsClusters P) {S : Finset X} (h : Relevant P S) :
    kin P S + kin P Sᶜ = P.card := by
  have : P.filter (· ⊆ Sᶜ) = P.filter (fun C => ¬ C ⊆ S) :=
    filter_congr fun C hC => subset_compl_iff_not_subset hP h hC
  rw [kin, kin, this, card_filter_add_card_filter_not]

/-- A side with one cluster on one side and one off it has every cluster on one of its sides. -/
theorem relevant_of_sep (hP : IsClusters P) {S K L : Finset X} (hc : ∀ C ∈ P, Compat C S)
    (hK : K ∈ P) (hL : L ∈ P) (hKS : K ⊆ S) (hLS : Disjoint L S) : Relevant P S := by
  intro C hC
  rcases hc C hC with h | h | h | h
  · exact Or.inl h
  · rw [hP.eq_of_subset hK hC (hKS.trans h)] at hKS
    exact Or.inl hKS
  · exact Or.inr h
  · have hLC : L ⊆ C := fun x hx => by
      have : x ∈ C ∪ S := h ▸ mem_univ x
      exact (mem_union.1 this).resolve_right (disjoint_left.1 hLS hx)
    rw [← hP.eq_of_subset hL hC hLC]
    exact Or.inr hLS

omit [Fintype X] in
/-- A relevant side other than a cluster `K` inside it has two clusters. -/
theorem two_le_kin (hP : IsClusters P) {S K : Finset X} (h : Relevant P S) (hK : K ∈ P)
    (hKS : K ⊆ S) (hne : S ≠ K) : 2 ≤ kin P S := by
  obtain ⟨x, hxS, hxK⟩ : ∃ x ∈ S, x ∉ K := by
    by_contra hn
    push Not at hn
    exact hne (Subset.antisymm hn hKS)
  obtain ⟨C, hC, hxC⟩ := hP.cover x
  have hCS : C ⊆ S := (h C hC).resolve_right fun hd => disjoint_left.1 hd hxC hxS
  have hCK : K ≠ C := fun e => hxK (e ▸ hxC)
  exact one_lt_card.2 ⟨K, mem_filter.2 ⟨hK, hKS⟩, C, mem_filter.2 ⟨hC, hCS⟩, hCK⟩

/-! ### The distance between clusters in a tree -/

/-- The distance in the tree between clusters: the total weight of the sides with `A` inside and `B` off.
A side `S` with both clusters on one of its sides does not count, and this is the distance between the
points where the clusters attach to the tree, with their pendant edges. -/
def clusterDist (T : Finset (Finset X)) (w : Finset X → ℝ) (A B : Finset X) : ℝ :=
  ∑ S ∈ T with A ⊆ S ∧ Disjoint B S, w S

/-- The length of the pendant edge of the cluster `A`: the weight of the edge of the tree with side `A`, and
`0` if `A` is not a side, when the new edge is a resolution of a polytomy. -/
def pend (T : Finset (Finset X)) (w : Finset X → ℝ) (A : Finset X) : ℝ := if A ∈ T then w A else 0

/-- The pair `A, B` are neighbours in the tree: the only sides with `A` inside and `B` off are the sides of their
pendant edges. -/
def Nbr (T : Finset (Finset X)) (A B : Finset X) : Prop :=
  ∀ S ∈ T, A ⊆ S → Disjoint B S → S = A ∨ Sᶜ = B

theorem pend_compl (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A) (A : Finset X) :
    pend T w Aᶜ = pend T w A := by
  by_cases h : A ∈ T
  · rw [pend, pend, ite_eq_left h, ite_eq_left (hT A h), hw A h]
  · have h' : Aᶜ ∉ T := fun h' => h (by simpa using hT _ h')
    rw [pend, pend, ite_eq_right h, ite_eq_right h']

theorem Nbr.symm (hT : ∀ A ∈ T, Aᶜ ∈ T) {A B : Finset X} (h : Nbr T A B) : Nbr T B A := by
  intro S hS hBS hAS
  rcases h Sᶜ (hT S hS) (subset_compl_iff_disjoint_right.2 hAS)
    (disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (hBS hx)) with h | h
  · exact Or.inr h
  · exact Or.inl (by simpa using h)

omit [Fintype X] in
theorem clusterDist_self {A : Finset X} (hA : A.Nonempty) : clusterDist T w A A = 0 := by
  refine sum_eq_zero fun S hS => ?_
  obtain ⟨x, hx⟩ := hA
  obtain ⟨-, h1, h2⟩ := mem_filter.1 hS
  exact absurd (h1 hx) (disjoint_left.1 h2 hx)

theorem clusterDist_comm (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A) (A B : Finset X) :
    clusterDist T w A B = clusterDist T w B A := by
  refine sum_nbij' compl compl ?_ ?_ (by simp) (by simp) ?_
  · intro S hS
    obtain ⟨hS, h1, h2⟩ := mem_filter.1 hS
    exact mem_filter.2 ⟨hT S hS, subset_compl_iff_disjoint_right.2 h2,
      disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (h1 hx)⟩
  · intro S hS
    obtain ⟨hS, h1, h2⟩ := mem_filter.1 hS
    exact mem_filter.2 ⟨hT S hS, subset_compl_iff_disjoint_right.2 h2,
      disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (h1 hx)⟩
  · intro S hS
    exact (hw S (mem_filter.1 hS).1).symm

omit [Fintype X] in
theorem treeMetric_eq_clusterDist (x y : X) :
    treeMetric T w x y = clusterDist T w {x} {y} := by
  rw [treeMetric, clusterDist]
  refine sum_congr ?_ fun _ _ => rfl
  ext S
  simp

/-- The pendant edge splits off a distance: `d(A,C) = d(A,u) + d(u,C)`. -/
theorem clusterDist_eq_pend_add (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S)
    {A B C : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hC : C ∈ P) (hAB : A ≠ B) (hAC : A ≠ C)
    (hBC : B ≠ C) (hn : Nbr T A B) :
    clusterDist T w A C = pend T w A + clusterDist T w (A ∪ B) C := by
  have hdAC := hP.disjoint A hA C hC hAC
  have hdBC := hP.disjoint B hB C hC hBC
  have hdAB := hP.disjoint A hA B hB hAB
  have hBne := hP.nonempty B hB
  have hCne := hP.nonempty C hC
  rw [clusterDist, clusterDist, sum_filter, sum_filter]
  have hpend : pend T w A = ∑ S ∈ T, if S = A then w S else 0 := by
    rw [sum_ite_eq' T A w, pend]
  rw [hpend, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  by_cases hSA : S = A
  · subst hSA
    have h1 : ¬ (S ∪ B ⊆ S ∧ Disjoint C S) := by
      rintro ⟨h, -⟩
      obtain ⟨x, hx⟩ := hBne
      exact disjoint_left.1 hdAB (h (mem_union_right _ hx)) hx
    rw [ite_eq_left ⟨Subset.refl _, hdAC.symm⟩, ite_eq_left rfl, ite_eq_right h1, add_zero]
  · rw [ite_eq_right hSA, zero_add]
    congr 1
    refine propext ⟨fun ⟨hAS, hCS⟩ => ⟨?_, hCS⟩, fun ⟨hu, hCS⟩ => ⟨subset_union_left.trans hu, hCS⟩⟩
    have hCc : C ⊆ Sᶜ := subset_compl_iff_disjoint_right.2 hCS
    obtain ⟨c, hcC⟩ := hCne
    refine union_subset hAS ?_
    rcases hc B hB S hS with h | h | h | h
    · exact h
    · have := hP.eq_of_subset hA hB (hAS.trans h)
      exact absurd this hAB
    · rcases hn S hS hAS h with h' | h'
      · exact absurd h' hSA
      · rw [h'] at hCc
        exact absurd (hCc hcC) (disjoint_left.1 hdBC.symm hcC)
    · have hcB : c ∈ B := by
        have : c ∈ B ∪ S := h ▸ mem_univ c
        exact (mem_union.1 this).resolve_right (mem_compl.1 (hCc hcC))
      exact absurd hcB (disjoint_left.1 hdBC.symm hcC)

/-- The distance between neighbours is the sum of their pendant edges, when there is a third cluster. -/
theorem clusterDist_nbr (hP : IsClusters P) (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A)
    {A B C : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hC : C ∈ P) (hAB : A ≠ B) (hAC : A ≠ C)
    (hBC : B ≠ C) (hn : Nbr T A B) :
    clusterDist T w A B = pend T w A + pend T w B := by
  have hdAB := hP.disjoint A hA B hB hAB
  have hABc : A ≠ Bᶜ := by
    intro e
    have : C ⊆ A := e ▸ subset_compl_iff_disjoint_right.2 (hP.disjoint C hC B hB hBC.symm)
    exact hAC (hP.eq_of_subset hC hA this).symm
  rw [clusterDist, sum_filter, ← pend_compl hT hw B]
  have h1 : pend T w A = ∑ S ∈ T, if S = A then w S else 0 := by
    rw [sum_ite_eq' T A w, pend]
  have h2 : pend T w Bᶜ = ∑ S ∈ T, if S = Bᶜ then w S else 0 := by
    rw [sum_ite_eq' T Bᶜ w, pend]
  rw [h1, h2, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  by_cases hSA : S = A
  · subst hSA
    rw [ite_eq_left ⟨Subset.refl _, hdAB.symm⟩, ite_eq_left rfl, ite_eq_right hABc, add_zero]
  · by_cases hSB : S = Bᶜ
    · subst hSB
      rw [ite_eq_left ⟨subset_compl_iff_disjoint_right.2 hdAB,
        disjoint_left.2 fun x hx hx' => mem_compl.1 hx' hx⟩, ite_eq_right hSA, ite_eq_left rfl, zero_add]
    · rw [ite_eq_right hSA, ite_eq_right hSB, ite_eq_right, add_zero]
      rintro ⟨h1, h2⟩
      rcases hn S hS h1 h2 with h | h
      · exact hSA h
      · exact hSB (by rw [← h, compl_compl])

/-- The union of neighbours is compatible with the tree: they are a cherry of a resolution. -/
theorem Nbr.compat_union (hT : ∀ A ∈ T, Aᶜ ∈ T) (hP : IsClusters P)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hn : Nbr T A B) {S : Finset X} (hS : S ∈ T) : Compat (A ∪ B) S := by
  have hn' := hn.symm hT
  rcases hc A hA S hS with h | h | h | h
  · rcases hc B hB S hS with h' | h' | h' | h'
    · exact Or.inl (union_subset h h')
    · exact absurd (hP.eq_of_subset hA hB (h.trans h')) hAB
    · rcases hn S hS h h' with e | e
      · rw [e]; exact Or.inr (Or.inl subset_union_left)
      · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
        by_cases hx : x ∈ S
        · exact mem_union_right _ hx
        · exact mem_union_left _ (mem_union_right _ (e ▸ mem_compl.2 hx))
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      have : x ∈ B ∪ S := h' ▸ mem_univ x
      rcases mem_union.1 this with hx | hx
      · exact mem_union_left _ (mem_union_right _ hx)
      · exact mem_union_right _ hx
  · exact Or.inr (Or.inl (h.trans subset_union_left))
  · rcases hc B hB S hS with h' | h' | h' | h'
    · rcases hn' S hS h' h with e | e
      · rw [e]; exact Or.inr (Or.inl subset_union_right)
      · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
        by_cases hx : x ∈ S
        · exact mem_union_right _ hx
        · exact mem_union_left _ (mem_union_left _ (e ▸ mem_compl.2 hx))
    · exact Or.inr (Or.inl (h'.trans subset_union_right))
    · exact Or.inr (Or.inr (Or.inl (disjoint_union_left.2 ⟨h, h'⟩)))
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      have : x ∈ B ∪ S := h' ▸ mem_univ x
      rcases mem_union.1 this with hx | hx
      · exact mem_union_left _ (mem_union_right _ hx)
      · exact mem_union_right _ hx
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    have : x ∈ A ∪ S := h ▸ mem_univ x
    rcases mem_union.1 this with hx | hx
    · exact mem_union_left _ (mem_union_left _ hx)
    · exact mem_union_right _ hx

/-! ### The criterion as a sum over the edges -/

/-- The row sum `r_A` in the tree. -/
def rowC (T : Finset (Finset X)) (w : Finset X → ℝ) (P : Finset (Finset X)) (A : Finset X) : ℝ :=
  ∑ C ∈ P, clusterDist T w A C

/-- The criterion `Q(A,B)` in the tree. -/
def QC (T : Finset (Finset X)) (w : Finset X → ℝ) (P : Finset (Finset X)) (A B : Finset X) : ℝ :=
  ((P.card : ℝ) - 2) * clusterDist T w A B - rowC T w P A - rowC T w P B

/-- The sides of the tree having each cluster on one side. -/
def relevantSides (T P : Finset (Finset X)) : Finset (Finset X) := T.filter (Relevant P)

/-- The number of clusters on the side of `S` not containing `A, B`, or `1` if `S` separates them. -/
def g (P : Finset (Finset X)) (S A B : Finset X) : ℝ :=
  if A ⊆ S then (if B ⊆ S then (P.card : ℝ) - kin P S else 1)
  else (if B ⊆ S then 1 else (kin P S : ℝ))

/-- The contribution of the side `S` to `Q(A,B)`, counting only the sides with `A` inside or `B` inside. -/
def phi (P : Finset (Finset X)) (S A B : Finset X) : ℝ :=
  ((P.card : ℝ) - 2) * (if A ⊆ S ∧ ¬ B ⊆ S then 1 else 0) -
    (if A ⊆ S then (P.card : ℝ) - kin P S else 0) - (if B ⊆ S then (P.card : ℝ) - kin P S else 0)

theorem clusterDist_eq_sum_relevant (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S)
    {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) :
    clusterDist T w A B = ∑ S ∈ relevantSides T P, if A ⊆ S ∧ ¬ B ⊆ S then w S else 0 := by
  rw [clusterDist, relevantSides, sum_filter, sum_filter]
  refine sum_congr rfl fun S hS => ?_
  by_cases hR : Relevant P S
  · rw [ite_eq_left hR]
    simp only [disjoint_iff_not_subset hP hR hB]
  · rw [ite_eq_right hR]
    exact ite_eq_right fun h => hR (relevant_of_sep hP (fun C hC => hc C hC S hS) hA hB h.1 h.2)

theorem rowC_eq (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A : Finset X} (hA : A ∈ P) :
    rowC T w P A =
      ∑ S ∈ relevantSides T P, if A ⊆ S then w S * ((P.card : ℝ) - kin P S) else 0 := by
  have h : ∀ C ∈ P, clusterDist T w A C =
      ∑ S ∈ relevantSides T P, if A ⊆ S ∧ ¬ C ⊆ S then w S else 0 :=
    fun C hC => clusterDist_eq_sum_relevant hP hc hA hC
  rw [rowC, sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun S _ => ?_
  by_cases hAS : A ⊆ S
  · have h1 : ∀ C ∈ P, (if A ⊆ S ∧ ¬ C ⊆ S then w S else 0) = if ¬ C ⊆ S then w S else 0 :=
      fun C _ => by simp only [hAS, true_and]
    have h2 := card_filter_add_card_filter_not (s := P) (fun C => C ⊆ S)
    have h3 : ((P.filter fun C => ¬ C ⊆ S).card : ℝ) = (P.card : ℝ) - kin P S := by
      rw [kin, ← h2]
      push_cast
      ring
    rw [sum_congr rfl h1, ← sum_filter, sum_const, nsmul_eq_mul, ite_eq_left hAS, h3, mul_comm]
  · simp [hAS]

theorem QC_eq_phi (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B : Finset X}
    (hA : A ∈ P) (hB : B ∈ P) :
    QC T w P A B = ∑ S ∈ relevantSides T P, w S * phi P S A B := by
  rw [QC, clusterDist_eq_sum_relevant hP hc hA hB, rowC_eq hP hc hA, rowC_eq hP hc hB, mul_sum,
    ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun S _ => ?_
  rw [phi]
  by_cases hAS : A ⊆ S <;> by_cases hBS : B ⊆ S <;> simp [hAS, hBS] <;> ring

/-- The two orientations of a split add up to `-2 g`. -/
theorem phi_add_phi_compl (hP : IsClusters P) {S A B : Finset X} (hR : Relevant P S) (hA : A ∈ P)
    (hB : B ∈ P) : phi P S A B + phi P Sᶜ A B = -2 * g P S A B := by
  have hk : (kin P Sᶜ : ℝ) = (P.card : ℝ) - kin P S := by
    rw [← kin_add_kin_compl hP hR]
    push_cast
    ring
  simp only [phi, g, hk, subset_compl_iff_not_subset hP hR hA, subset_compl_iff_not_subset hP hR hB]
  by_cases hAS : A ⊆ S <;> by_cases hBS : B ⊆ S <;> simp [hAS, hBS] <;> ring

/-- **The criterion as a sum over the edges**: `Q(A,B) = -∑_S w_S g_S(A,B)`. -/
theorem QC_eq (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A) (hP : IsClusters P)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) :
    QC T w P A B = -∑ S ∈ relevantSides T P, w S * g P S A B := by
  have hmem : ∀ S ∈ relevantSides T P, Sᶜ ∈ relevantSides T P := fun S hS => by
    obtain ⟨hS, hR⟩ := mem_filter.1 hS
    exact mem_filter.2 ⟨hT S hS, hR.compl⟩
  have hinv : ∑ S ∈ relevantSides T P, w S * phi P Sᶜ A B =
      ∑ S ∈ relevantSides T P, w S * phi P S A B := by
    refine sum_nbij' compl compl hmem hmem (by simp) (by simp) fun S hS => ?_
    rw [hw S (mem_filter.1 hS).1]
  have h2 : ∑ S ∈ relevantSides T P, w S * phi P S A B + ∑ S ∈ relevantSides T P, w S * phi P Sᶜ A B =
      -2 * ∑ S ∈ relevantSides T P, w S * g P S A B := by
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun S hS => ?_
    rw [← mul_add, phi_add_phi_compl hP (mem_filter.1 hS).2 hA hB]
    ring
  rw [QC_eq_phi hP hc hA hB]
  rw [hinv] at h2
  linarith

omit [Fintype X] in
theorem kin_mono {S S' : Finset X} (h : S ⊆ S') : kin P S ≤ kin P S' :=
  card_le_card fun _ hC => mem_filter.2 ⟨(mem_filter.1 hC).1, (mem_filter.1 hC).2.trans h⟩

omit [Fintype X] in
theorem one_le_kin {S C : Finset X} (hC : C ∈ P) (h : C ⊆ S) : 1 ≤ kin P S :=
  card_pos.2 ⟨C, mem_filter.2 ⟨hC, h⟩⟩

omit [Fintype X] in
theorem kin_self (hP : IsClusters P) {C : Finset X} (hC : C ∈ P) : kin P C = 1 := by
  rw [kin, card_eq_one]
  refine ⟨C, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hC, Subset.refl _⟩, fun D hD => ?_⟩⟩
  obtain ⟨hD, hsub⟩ := mem_filter.1 hD
  exact hP.eq_of_subset hD hC hsub

/-- **The comparison, side by side.** Let `S₀` be a side with `A` inside, `B` off and at most half the clusters.
Then neighbours `K, L` inside `S₀` have `g_S(K,L) ≥ g_S(A,B)` on each side `S`. -/
theorem g_le (hT : ∀ A ∈ T, Aᶜ ∈ T) (hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S') (hP : IsClusters P)
    {A B K L S₀ S : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hK : K ∈ P) (hL : L ∈ P) (hAB : A ≠ B)
    (hn : Nbr T K L) (hS₀ : S₀ ∈ T) (hAS₀ : A ⊆ S₀) (hBS₀ : Disjoint B S₀) (hKS₀ : K ⊆ S₀)
    (hhalf : 2 * kin P S₀ ≤ P.card) (hS : S ∈ T) (hR : Relevant P S) : g P S A B ≤ g P S K L := by
  have hk := kin_add_kin_compl hP hR
  have hk' : (P.card : ℝ) - kin P S = kin P Sᶜ := by
    rw [← hk]
    push_cast
    ring
  have hn' := hn.symm hT
  obtain ⟨a, ha⟩ := hP.nonempty A hA
  obtain ⟨b, hb⟩ := hP.nonempty B hB
  obtain ⟨c, hc⟩ := hP.nonempty K hK
  have hd : ∀ {C : Finset X}, C ∈ P → ¬ C ⊆ S → Disjoint C S := fun hC h =>
    (disjoint_iff_not_subset hP hR hC).2 h
  have hsc : ∀ {C : Finset X}, C ∈ P → ¬ C ⊆ S → C ⊆ Sᶜ := fun hC h =>
    (subset_compl_iff_not_subset hP hR hC).2 h
  -- `A, B` inside `S`, and `K, L` not: then `Sᶜ ⊆ S₀`
  have hcase1 : A ⊆ S → B ⊆ S → ¬ K ⊆ S → kin P Sᶜ ≤ kin P S := by
    intro hAS hBS hKS
    have hsub : Sᶜ ⊆ S₀ := by
      rcases (hcT S hS S₀ hS₀).compl_left with h | h | h | h
      · exact h
      · exact absurd (hAS ha) (mem_compl.1 (h (hAS₀ ha)))
      · exact absurd (hKS₀ hc) (disjoint_left.1 h (hsc hK hKS hc))
      · have : b ∈ Sᶜ ∪ S₀ := h ▸ mem_univ b
        rcases mem_union.1 this with h' | h'
        · exact absurd (hBS hb) (mem_compl.1 h')
        · exact absurd h' (disjoint_left.1 hBS₀ hb)
    have := kin_mono (P := P) hsub
    omega
  -- `K, L` inside `S`, and `A, B` not: then `S ⊆ S₀`
  have hcase2 : ¬ A ⊆ S → ¬ B ⊆ S → K ⊆ S → kin P S ≤ kin P Sᶜ := by
    intro hAS hBS hKS
    have hsub : S ⊆ S₀ := by
      rcases hcT S hS S₀ hS₀ with h | h | h | h
      · exact h
      · exact absurd (h (hAS₀ ha)) (disjoint_left.1 (hd hA hAS) ha)
      · exact absurd (hKS₀ hc) (disjoint_left.1 h (hKS hc))
      · have : b ∈ S ∪ S₀ := h ▸ mem_univ b
        rcases mem_union.1 this with h' | h'
        · exact absurd h' (disjoint_left.1 (hd hB hBS) hb)
        · exact absurd h' (disjoint_left.1 hBS₀ hb)
    have := kin_mono (P := P) hsub
    omega
  -- `S` separates the neighbours
  have hsep1 : A ⊆ S → B ⊆ S → ∀ {K' L' : Finset X}, K' ∈ P → L' ∈ P → Nbr T K' L' → K' ⊆ S → ¬ L' ⊆ S →
      kin P Sᶜ = 1 := by
    intro hAS hBS K' L' hK' hL' hn' hKS hLS
    rcases hn' S hS hKS (hd hL' hLS) with e | e
    · subst e
      exact absurd ((hP.eq_of_subset hA hK' hAS).trans (hP.eq_of_subset hB hK' hBS).symm) hAB
    · rw [e]
      exact kin_self hP hL'
  have hsep2 : ¬ A ⊆ S → ¬ B ⊆ S → ∀ {K' L' : Finset X}, K' ∈ P → L' ∈ P → Nbr T K' L' → K' ⊆ S →
      ¬ L' ⊆ S → kin P S = 1 := by
    intro hAS hBS K' L' hK' hL' hn' hKS hLS
    rcases hn' S hS hKS (hd hL' hLS) with e | e
    · rw [e]
      exact kin_self hP hK'
    · rw [compl_eq_comm] at e
      subst e
      have h1 : A ⊆ L' := by simpa using hsc hA hAS
      have h2 : B ⊆ L' := by simpa using hsc hB hBS
      exact absurd ((hP.eq_of_subset hA hL' h1).trans (hP.eq_of_subset hB hL' h2).symm) hAB
  have cast1 : ∀ {u v : ℕ}, u ≤ v → (u : ℝ) ≤ v := fun h => by exact_mod_cast h
  have cast2 : ∀ {u : ℕ}, 1 ≤ u → (1 : ℝ) ≤ u := fun h => by exact_mod_cast h
  simp only [g, hk']
  by_cases hAS : A ⊆ S <;> by_cases hBS : B ⊆ S <;> by_cases hKS : K ⊆ S <;> by_cases hLS : L ⊆ S <;>
    simp only [hAS, hBS, hKS, hLS, ite_true, ite_false, le_refl]
  · rw [hsep1 hAS hBS hK hL hn hKS hLS]
    norm_num
  · rw [hsep1 hAS hBS hL hK hn' hLS hKS]
    norm_num
  · exact cast1 (hcase1 hAS hBS hKS)
  · exact cast2 (one_le_kin hB (hsc hB hBS))
  · exact cast2 (one_le_kin hA hAS)
  · exact cast2 (one_le_kin hA (hsc hA hAS))
  · exact cast2 (one_le_kin hB hBS)
  · exact cast1 (hcase2 hAS hBS hKS)
  · rw [hsep2 hAS hBS hK hL hn hKS hLS]
    norm_num
  · rw [hsep2 hAS hBS hL hK hn' hLS hKS]
    norm_num

/-- **The comparison.** A side `S₀` with `A` inside, `B` off, and at least two clusters and at most half
of them; neighbours `K, L` inside it beat `A, B`. -/
theorem QC_lt_of_side (hT : ∀ A ∈ T, Aᶜ ∈ T) (hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S')
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S)
    {A B K L S₀ : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hK : K ∈ P) (hL : L ∈ P) (hAB : A ≠ B)
    (hn : Nbr T K L) (hS₀ : S₀ ∈ T) (hAS₀ : A ⊆ S₀) (hBS₀ : Disjoint B S₀) (hKS₀ : K ⊆ S₀)
    (hLS₀ : L ⊆ S₀) (h2 : 2 ≤ kin P S₀) (hhalf : 2 * kin P S₀ ≤ P.card) :
    QC T w P K L < QC T w P A B := by
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  rw [QC_eq hT hw' hP hc hK hL, QC_eq hT hw' hP hc hA hB, neg_lt_neg_iff]
  have hR₀ : Relevant P S₀ := relevant_of_sep hP (fun C hC => hc C hC S₀ hS₀) hA hB hAS₀ hBS₀
  refine sum_lt_sum (fun S hS => ?_) ⟨S₀, mem_filter.2 ⟨hS₀, hR₀⟩, ?_⟩
  · obtain ⟨hS, hR⟩ := mem_filter.1 hS
    exact mul_le_mul_of_nonneg_left
      (g_le hT hcT hP hA hB hK hL hAB hn hS₀ hAS₀ hBS₀ hKS₀ hhalf hS hR) (hw S hS).1.le
  · refine mul_lt_mul_of_pos_left ?_ (hw S₀ hS₀).1
    have hBn : ¬ B ⊆ S₀ := fun h => by
      obtain ⟨b, hb⟩ := hP.nonempty B hB
      exact disjoint_left.1 hBS₀ hb (h hb)
    have h1 : g P S₀ A B = 1 := by simp [g, hAS₀, hBn]
    have h3 : g P S₀ K L = (P.card : ℝ) - kin P S₀ := by simp [g, hKS₀, hLS₀]
    rw [h1, h3]
    have h4 : (2 : ℝ) * kin P S₀ ≤ P.card := by exact_mod_cast hhalf
    have h5 : (2 : ℝ) ≤ kin P S₀ := by exact_mod_cast h2
    linarith

/-- A least side with at least two clusters inside `S₀` has neighbours. -/
theorem exists_nbr_in_side (hT : ∀ A ∈ T, Aᶜ ∈ T) (hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S')
    (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {S₀ : Finset X} (hS₀ : S₀ ∈ T)
    (hR₀ : Relevant P S₀) (h2 : 2 ≤ kin P S₀) :
    ∃ K ∈ P, ∃ L ∈ P, K ≠ L ∧ K ⊆ S₀ ∧ L ⊆ S₀ ∧ Nbr T K L := by
  have hne : (T.filter fun S => S ⊆ S₀ ∧ Relevant P S ∧ 2 ≤ kin P S).Nonempty :=
    ⟨S₀, mem_filter.2 ⟨hS₀, Subset.refl _, hR₀, h2⟩⟩
  obtain ⟨S', hS', hmin⟩ := exists_min_image _ card hne
  obtain ⟨hS'T, hsub, -, h2'⟩ := mem_filter.1 hS'
  obtain ⟨K, hK, L, hL, hKL⟩ := one_lt_card.1 h2'
  obtain ⟨hKP, hKS⟩ := mem_filter.1 hK
  obtain ⟨hLP, hLS⟩ := mem_filter.1 hL
  refine ⟨K, hKP, L, hLP, hKL, hKS.trans hsub, hLS.trans hsub, fun S hS hKin hLoff => ?_⟩
  by_contra hcon
  push Not at hcon
  have hRS := relevant_of_sep hP (fun C hC => hc C hC S hS) hKP hLP hKin hLoff
  have h2S := two_le_kin hP hRS hKP hKin hcon.1
  have h2Sc := two_le_kin hP hRS.compl hLP (subset_compl_iff_disjoint_right.2 hLoff) hcon.2
  obtain ⟨c, hc'⟩ := hP.nonempty K hKP
  obtain ⟨l, hl⟩ := hP.nonempty L hLP
  rcases hcT S hS S' hS'T with h | h | h | h
  · have h3 := hmin S (mem_filter.2 ⟨hS, h.trans hsub, hRS, h2S⟩)
    have hlt : S ⊂ S' := ⟨h, fun h' => disjoint_left.1 hLoff hl (h' (hLS hl))⟩
    exact absurd (card_lt_card hlt) (not_lt.2 h3)
  · exact disjoint_left.1 hLoff hl (h (hLS hl))
  · exact disjoint_left.1 h (hKin hc') (hKS hc')
  · have hsc : Sᶜ ⊆ S' := fun x hx => by
      have : x ∈ S ∪ S' := h ▸ mem_univ x
      exact (mem_union.1 this).resolve_left (mem_compl.1 hx)
    have h3 := hmin Sᶜ (mem_filter.2 ⟨hT S hS, hsc.trans hsub, hRS.compl, h2Sc⟩)
    have hlt : Sᶜ ⊂ S' := ⟨hsc, fun h' => mem_compl.1 (h' (hKS hc')) (hKin hc')⟩
    exact absurd (card_lt_card hlt) (not_lt.2 h3)

theorem QC_comm (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A) (A B : Finset X) :
    QC T w P A B = QC T w P B A := by
  rw [QC, QC, clusterDist_comm hT hw A B]
  ring

/-- **Pairs that are not neighbours do not minimize the criterion** (the Theorem of Studier and Keppler 1988, p. 730,
for trees with polytomies).

`S_kl - S_ij` is a sum over the edges (`QC_eq`). Of the two sides of an edge separating the pair, one has at most half of
the clusters, and neighbours inside it have a strictly smaller criterion (`QC_lt_of_side`). -/
theorem exists_QC_lt_of_not_nbr (hT : ∀ A ∈ T, Aᶜ ∈ T) (hcT : ∀ S ∈ T, ∀ S' ∈ T, Compat S S')
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S)
    {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) (hn : ¬ Nbr T A B) :
    ∃ K ∈ P, ∃ L ∈ P, K ≠ L ∧ Nbr T K L ∧ QC T w P K L < QC T w P A B := by
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  simp only [Nbr] at hn
  push Not at hn
  obtain ⟨S₀, hS₀, hAS₀, hBS₀, hne, hne'⟩ := hn
  have hR₀ := relevant_of_sep hP (fun C hC => hc C hC S₀ hS₀) hA hB hAS₀ hBS₀
  have h2 := two_le_kin hP hR₀ hA hAS₀ hne
  have h2' := two_le_kin hP hR₀.compl hB (subset_compl_iff_disjoint_right.2 hBS₀) hne'
  have hk := kin_add_kin_compl hP hR₀
  by_cases hle : 2 * kin P S₀ ≤ P.card
  · obtain ⟨K, hK, L, hL, hKL, hKS, hLS, hnKL⟩ := exists_nbr_in_side hT hcT hP hc hS₀ hR₀ h2
    exact ⟨K, hK, L, hL, hKL, hnKL, QC_lt_of_side hT hcT hw hP hc hA hB hK hL hAB hnKL hS₀ hAS₀ hBS₀ hKS hLS
      h2 hle⟩
  · obtain ⟨K, hK, L, hL, hKL, hKS, hLS, hnKL⟩ :=
      exists_nbr_in_side hT hcT hP hc (hT S₀ hS₀) hR₀.compl h2'
    refine ⟨K, hK, L, hL, hKL, hnKL, ?_⟩
    rw [QC_comm hT hw' A B]
    exact QC_lt_of_side hT hcT hw hP hc hB hA hK hL hAB.symm hnKL (hT S₀ hS₀)
      (subset_compl_iff_disjoint_right.2 hBS₀)
      (disjoint_left.2 fun x hx hx' => mem_compl.1 hx' (hAS₀ hx)) hKS hLS h2' (by omega)

/-! ### The join in the tree -/

/-- The distance from the new node. -/
theorem clusterDist_union_eq (hP : IsClusters P) (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B C : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hn : Nbr T A B) :
    (clusterDist T w A C + clusterDist T w B C - clusterDist T w A B) / 2 =
      clusterDist T w (A ∪ B) C := by
  have h1 := clusterDist_eq_pend_add (w := w) hP hc hA hB hC hAB hAC hBC hn
  have h2 := clusterDist_eq_pend_add (w := w) hP hc hB hA hC hAB.symm hBC hAC (hn.symm hT)
  have h3 := clusterDist_nbr (w := w) hP hT hw hA hB hC hAB hAC hBC hn
  rw [union_comm B A] at h2
  rw [h1, h2, h3]
  ring

/-- `r_A - r_B = (n-2) (pend A - pend B)`. -/
theorem rowC_sub_rowC (hP : IsClusters P) (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P)
    (hAB : A ≠ B) (hn : Nbr T A B) :
    rowC T w P A - rowC T w P B = ((P.card : ℝ) - 2) * (pend T w A - pend T w B) := by
  have hB' : B ∈ P.erase A := mem_erase.2 ⟨hAB.symm, hB⟩
  have hsplit : ∀ E : Finset X, rowC T w P E = clusterDist T w E A + clusterDist T w E B +
      ∑ C ∈ (P.erase A).erase B, clusterDist T w E C := by
    intro E
    rw [rowC, ← add_sum_erase P _ hA, ← add_sum_erase (P.erase A) _ hB', add_assoc]
  have hcard : (((P.erase A).erase B).card : ℝ) = (P.card : ℝ) - 2 := by
    have h1 : 1 ≤ P.card := card_pos.2 ⟨A, hA⟩
    have h2 : 1 ≤ (P.erase A).card := card_pos.2 ⟨B, hB'⟩
    rw [card_erase_of_mem hB', card_erase_of_mem hA] at *
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    push_cast
    ring
  rw [hsplit A, hsplit B, clusterDist_self (hP.nonempty A hA), clusterDist_self (hP.nonempty B hB),
    clusterDist_comm hT hw B A, ← hcard]
  have hrest : ∑ C ∈ (P.erase A).erase B, clusterDist T w A C -
      ∑ C ∈ (P.erase A).erase B, clusterDist T w B C =
      (((P.erase A).erase B).card : ℝ) * (pend T w A - pend T w B) := by
    rw [← sum_sub_distrib, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun C hC => ?_
    obtain ⟨hCB, hCA, hCP⟩ : C ≠ B ∧ C ≠ A ∧ C ∈ P := by
      simpa only [mem_erase] using hC
    have h1 := clusterDist_eq_pend_add (w := w) hP hc hA hB hCP hAB hCA.symm hCB.symm hn
    have h2 := clusterDist_eq_pend_add (w := w) hP hc hB hA hCP hAB.symm hCB.symm hCA.symm (hn.symm hT)
    rw [union_comm B A] at h2
    rw [h1, h2]
    ring
  linarith

/-- **The branch length of Saitou and Nei is the pendant edge.** -/
theorem branch_eq_pend (hP : IsClusters P) (hT : ∀ A ∈ T, Aᶜ ∈ T) (hw : ∀ A ∈ T, w Aᶜ = w A)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P)
    (hAB : A ≠ B) (hn : Nbr T A B) (h3 : 3 ≤ P.card) :
    clusterDist T w A B / 2 + (rowC T w P A - rowC T w P B) / (2 * ((P.card : ℝ) - 2)) =
      pend T w A := by
  have hB' : B ∈ P.erase A := mem_erase.2 ⟨hAB.symm, hB⟩
  obtain ⟨C, hC⟩ : ((P.erase A).erase B).Nonempty := by
    rw [← card_pos, card_erase_of_mem hB', card_erase_of_mem hA]
    omega
  obtain ⟨hCB, hCA, hCP⟩ : C ≠ B ∧ C ≠ A ∧ C ∈ P := by
    simpa only [mem_erase] using hC
  have h3' : (3 : ℝ) ≤ P.card := by exact_mod_cast h3
  have hne : (P.card : ℝ) - 2 ≠ 0 := by
    have : (0 : ℝ) < (P.card : ℝ) - 2 := by linarith
    exact this.ne'
  rw [clusterDist_nbr hP hT hw hA hB hCP hAB hCA.symm hCB.symm hn, rowC_sub_rowC hP hT hw hc hA hB hAB hn]
  field_simp
  ring

/-- The distance across the last edge. -/
theorem clusterDist_compl (E : Finset X) : clusterDist T w E Eᶜ = pend T w E := by
  rw [clusterDist, sum_filter, pend, ← sum_ite_eq' T E w]
  refine sum_congr rfl fun S _ => ?_
  have hiff : (E ⊆ S ∧ Disjoint Eᶜ S) ↔ S = E := by
    constructor
    · rintro ⟨h1, h2⟩
      refine Subset.antisymm (fun x hx => ?_) h1
      by_contra hxE
      exact disjoint_left.1 h2 (mem_compl.2 hxE) hx
    · rintro rfl
      exact ⟨Subset.refl _, disjoint_left.2 fun x hx hx' => mem_compl.1 hx hx'⟩
  simp only [hiff]

/-! ### Clusters under a join -/

omit [Fintype X] in
theorem IsClusters.join (hP : IsClusters P) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) :
    IsClusters (insert (A ∪ B) ((P.erase A).erase B)) := by
  have hrest : ∀ {C : Finset X}, C ∈ (P.erase A).erase B → C ≠ B ∧ C ≠ A ∧ C ∈ P := fun hC => by
    simpa only [mem_erase] using hC
  refine ⟨fun C hC => ?_, fun C hC D hD hne => ?_, fun x => ?_⟩
  · rcases mem_insert.1 hC with rfl | hC
    · exact (hP.nonempty A hA).mono subset_union_left
    · exact hP.nonempty C (hrest hC).2.2
  · rcases mem_insert.1 hC with rfl | hC <;> rcases mem_insert.1 hD with rfl | hD
    · exact absurd rfl hne
    · obtain ⟨h1, h2, h3⟩ := hrest hD
      exact disjoint_union_left.2 ⟨hP.disjoint A hA D h3 h2.symm, hP.disjoint B hB D h3 h1.symm⟩
    · obtain ⟨h1, h2, h3⟩ := hrest hC
      exact disjoint_union_right.2 ⟨hP.disjoint C h3 A hA h2, hP.disjoint C h3 B hB h1⟩
    · exact hP.disjoint C (hrest hC).2.2 D (hrest hD).2.2 hne
  · obtain ⟨C, hC, hx⟩ := hP.cover x
    by_cases hCA : C = A
    · exact ⟨A ∪ B, mem_insert_self _ _, mem_union_left _ (hCA ▸ hx)⟩
    · by_cases hCB : C = B
      · exact ⟨A ∪ B, mem_insert_self _ _, mem_union_right _ (hCB ▸ hx)⟩
      · exact ⟨C, mem_insert_of_mem (mem_erase.2 ⟨hCB, mem_erase.2 ⟨hCA, hC⟩⟩), hx⟩

omit [Fintype X] in
theorem IsClusters.ne_union (hP : IsClusters P) {A B C : Finset X} (hA : A ∈ P)
    (hC : C ∈ (P.erase A).erase B) : C ≠ A ∪ B := by
  rintro rfl
  obtain ⟨h1, h2, h3⟩ : A ∪ B ≠ B ∧ A ∪ B ≠ A ∧ A ∪ B ∈ P := by
    simpa only [mem_erase] using hC
  exact h2 (hP.eq_of_subset hA h3 subset_union_left).symm

omit [Fintype X] in
theorem IsClusters.card_join (hP : IsClusters P) {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P)
    (hAB : A ≠ B) : (insert (A ∪ B) ((P.erase A).erase B)).card + 1 = P.card := by
  have hB' : B ∈ P.erase A := mem_erase.2 ⟨hAB.symm, hB⟩
  have hnot : A ∪ B ∉ (P.erase A).erase B := fun h => hP.ne_union hA h rfl
  have h1 : 0 < (P.erase A).card := card_pos.2 ⟨B, hB'⟩
  rw [card_insert_of_notMem hnot, card_erase_of_mem hB']
  have h2 := card_erase_of_mem hA
  have h3 := card_pos.2 ⟨A, hA⟩
  omega

/-- A recorded side is compatible with each active node. -/
theorem compat_of_inside (hP : IsClusters P) {C S : Finset X} (hC : C ∈ P)
    (h : ∃ D ∈ P, S ⊆ D ∨ Sᶜ ⊆ D) : Compat C S := by
  obtain ⟨D, hD, h⟩ := h
  by_cases hCD : C = D
  · subst hCD
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      by_cases hx : x ∈ S
      · exact mem_union_right _ hx
      · exact mem_union_left _ (h (mem_compl.2 hx))
  · have hd := hP.disjoint C hC D hD hCD
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl (hd.mono_right h)))
    · refine Or.inl fun x hx => ?_
      by_contra hxS
      exact disjoint_left.1 hd hx (h (mem_compl.2 hxS))

/-! ### The invariant of a run on a tree metric -/

/-- The invariant of a run on the metric of `T` and `w`. The active nodes are clusters compatible with `T`, at
their distances in `T`. The recorded edges have their pendant lengths. The edges of `T` are recorded or have
every cluster on one side. The recorded edges form a tree. -/
structure Inv (T : Finset (Finset X)) (w : Finset X → ℝ) (s : State X) : Prop where
  clusters : IsClusters s.active
  compat : ∀ C ∈ s.active, ∀ S ∈ T, Compat C S
  dist_eq : ∀ C ∈ s.active, ∀ D ∈ s.active, s.dist C D = clusterDist T w C D
  len_eq : ∀ S ∈ s.edges, s.len S = pend T w S
  covered : ∀ S ∈ T, S ∈ s.edges ∨ Relevant s.active S
  edges_inside : ∀ S ∈ s.edges, ∃ C ∈ s.active, S ⊆ C ∨ Sᶜ ⊆ C
  edges_compat : ∀ S ∈ s.edges, ∀ S' ∈ s.edges, Compat S S'
  edges_compl : ∀ S ∈ s.edges, Sᶜ ∈ s.edges
  edges_nonempty : ∀ S ∈ s.edges, S.Nonempty

namespace Inv

variable {s : State X}

theorem rowSum_eq (h : Inv T w s) {A : Finset X} (hA : A ∈ s.active) :
    s.rowSum A = rowC T w s.active A :=
  sum_congr rfl fun C hC => h.dist_eq A hA C hC

theorem Q_eq (h : Inv T w s) {A B : Finset X} (hA : A ∈ s.active) (hB : B ∈ s.active) :
    s.Q A B = QC T w s.active A B := by
  rw [State.Q, QC, h.dist_eq A hA B hB, h.rowSum_eq hA, h.rowSum_eq hB]

/-- **A pair minimizing `Q` are neighbours**, for a tree with polytomies and any active clusters: Studier and
Keppler's theorem. There is no assumption on how ties are broken, as a pair that is not a pair of neighbours
is strictly beaten. -/
theorem nbr_of_isQMin (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (h : Inv T w s)
    {A B : Finset X} (hq : s.IsQMin A B) : Nbr T A B := by
  obtain ⟨hA, hB, hAB, hmin⟩ := hq
  by_contra hn
  obtain ⟨K, hK, L, hL, hKL, -, hlt⟩ := exists_QC_lt_of_not_nbr hS.compl_mem
    (fun S hS' S' hS'' => hS.compatible S hS' S' hS'') hw h.clusters h.compat hA hB hAB hn
  have := hmin K hK L hL hKL
  rw [h.Q_eq hA hB, h.Q_eq hK hL] at this
  exact absurd hlt (not_lt.2 this)

/-- **The induction step.** After joining a pair minimizing `Q`, the current distance is the metric of the tree
with the two neighbours replaced by the new node, and the branch lengths recorded are correct. -/
theorem join (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (h : Inv T w s)
    (h3 : 3 ≤ s.active.card) {A B : Finset X} (hq : s.IsQMin A B) : Inv T w (s.join A B) := by
  have hn := h.nbr_of_isQMin hS hw hq
  obtain ⟨hA, hB, hAB, -⟩ := hq
  have hT := hS.compl_mem
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  have hP := h.clusters
  have hn' := hn.symm hT
  have hrest : ∀ {C : Finset X}, C ∈ (s.active.erase A).erase B → C ≠ B ∧ C ≠ A ∧ C ∈ s.active :=
    fun hC => by simpa only [mem_erase] using hC
  have hd := hP.disjoint A hA B hB hAB
  obtain ⟨a, ha⟩ := hP.nonempty A hA
  obtain ⟨b, hb⟩ := hP.nonempty B hB
  have hsub : ∀ S ∈ ({A, Aᶜ, B, Bᶜ} : Finset (Finset X)), (S = A ∨ S = Aᶜ) ∨ (S = B ∨ S = Bᶜ) := by
    intro S hS
    simp only [mem_insert, mem_singleton] at hS
    tauto
  -- the recorded sides against the old edges
  have hnew : ∀ S ∈ ({A, Aᶜ, B, Bᶜ} : Finset (Finset X)), ∀ S' ∈ s.edges, Compat S S' := by
    intro S hS S' hS'
    have hAc := compat_of_inside hP hA (h.edges_inside S' hS')
    have hBc := compat_of_inside hP hB (h.edges_inside S' hS')
    rcases hsub S hS with (rfl | rfl) | (rfl | rfl)
    · exact hAc
    · exact hAc.compl_left
    · exact hBc
    · exact hBc.compl_left
  have hAA : Compat A A := Or.inl (Subset.refl _)
  have hBB : Compat B B := Or.inl (Subset.refl _)
  have hABc : Compat A B := Or.inr (Or.inr (Or.inl hd))
  refine ⟨hP.join hA hB, fun C hC S hS' => ?_, fun E hE F hF => ?_, fun S hS' => ?_,
    fun S hS' => ?_, fun S hS' => ?_, fun S hS' S' hS'' => ?_, fun S hS' => ?_, fun S hS' => ?_⟩
  · -- compatibility
    rcases mem_insert.1 hC with rfl | hC
    · exact hn.compat_union hT hP h.compat hA hB hAB hS'
    · exact h.compat C (hrest hC).2.2 S hS'
  · -- the distances
    have hval : ∀ {F : Finset X}, F ∈ (s.active.erase A).erase B →
        (s.dist A F + s.dist B F - s.dist A B) / 2 = clusterDist T w (A ∪ B) F := by
      intro F hF
      obtain ⟨h1, h2, h3'⟩ := hrest hF
      rw [h.dist_eq A hA F h3', h.dist_eq B hB F h3', h.dist_eq A hA B hB]
      exact clusterDist_union_eq hP hT hw' h.compat hA hB h3' hAB h2.symm h1.symm hn
    change State.joinedDist s.dist A B E F = _
    rcases mem_insert.1 hE with rfl | hE' <;> rcases mem_insert.1 hF with rfl | hF'
    · simp only [State.joinedDist, ite_true]
      exact (clusterDist_self ((hP.nonempty A hA).mono subset_union_left)).symm
    · simp only [State.joinedDist, ite_true, hP.ne_union hA hF', ite_false]
      exact hval hF'
    · simp only [State.joinedDist, ite_true, hP.ne_union hA hE', ite_false]
      obtain ⟨h1, h2, h3'⟩ := hrest hE'
      rw [clusterDist_comm hT hw' E (A ∪ B), ← hval hE', h.dist_eq E h3' A hA, h.dist_eq E h3' B hB,
        h.dist_eq A hA E h3', h.dist_eq B hB E h3', clusterDist_comm hT hw' E A,
        clusterDist_comm hT hw' E B]
    · simp only [State.joinedDist, hP.ne_union hA hE', hP.ne_union hA hF', ite_false]
      exact h.dist_eq E (hrest hE').2.2 F (hrest hF').2.2
  · -- the branch lengths
    change (if S = A ∨ S = Aᶜ then s.branch A B else if S = B ∨ S = Bᶜ then s.branch B A else s.len S) = _
    have hbr : ∀ {A B : Finset X}, A ∈ s.active → B ∈ s.active → A ≠ B → Nbr T A B →
        s.branch A B = pend T w A := by
      intro A B hA hB hAB hn
      rw [State.branch, h.dist_eq A hA B hB, h.rowSum_eq hA, h.rowSum_eq hB]
      exact branch_eq_pend hP hT hw' h.compat hA hB hAB hn h3
    by_cases h1 : S = A ∨ S = Aᶜ
    · rw [ite_eq_left h1, hbr hA hB hAB hn]
      rcases h1 with rfl | rfl
      · rfl
      · exact (pend_compl hT hw' A).symm
    · rw [ite_eq_right h1]
      by_cases h2 : S = B ∨ S = Bᶜ
      · rw [ite_eq_left h2, hbr hB hA hAB.symm hn']
        rcases h2 with rfl | rfl
        · rfl
        · exact (pend_compl hT hw' B).symm
      · rw [ite_eq_right h2]
        rcases mem_union.1 hS' with hS' | hS'
        · rcases hsub S hS' with h' | h'
          · exact absurd h' h1
          · exact absurd h' h2
        · exact h.len_eq S hS'
  · -- the edges of the tree are recorded, or have every cluster on one side
    have hmem : ∀ {U : Finset X}, U ∈ ({A, Aᶜ, B, Bᶜ} : Finset (Finset X)) →
        U ∈ ({A, Aᶜ, B, Bᶜ} ∪ s.edges : Finset (Finset X)) := fun hU => mem_union_left _ hU
    rcases h.covered S hS' with hed | hR
    · exact Or.inl (mem_union_right _ hed)
    · have hAc : A ⊆ S ∧ B ⊆ S ∨ Disjoint A S ∧ Disjoint B S ∨ S ∈ ({A, Aᶜ, B, Bᶜ} : Finset (Finset X)) := by
        rcases hR A hA with h1 | h1 <;> rcases hR B hB with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · refine Or.inr (Or.inr ?_)
          rcases hn S hS' h1 h2 with e | e
          · simp [e]
          · rw [compl_eq_comm] at e
            simp [e]
        · refine Or.inr (Or.inr ?_)
          rcases hn' S hS' h2 h1 with e | e
          · simp [e]
          · rw [compl_eq_comm] at e
            simp [e]
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      rcases hAc with hAc | hAc | hAc
      · refine Or.inr fun C hC => ?_
        rcases mem_insert.1 hC with rfl | hC
        · exact Or.inl (union_subset hAc.1 hAc.2)
        · exact hR C (hrest hC).2.2
      · refine Or.inr fun C hC => ?_
        rcases mem_insert.1 hC with rfl | hC
        · exact Or.inr (disjoint_union_left.2 hAc)
        · exact hR C (hrest hC).2.2
      · exact Or.inl (hmem hAc)
  · -- recorded edges lie inside the clusters
    have hU : A ∪ B ∈ insert (A ∪ B) ((s.active.erase A).erase B) := mem_insert_self _ _
    rcases mem_union.1 hS' with hS' | hS'
    · refine ⟨A ∪ B, hU, ?_⟩
      rcases hsub S hS' with (rfl | rfl) | (rfl | rfl)
      · exact Or.inl subset_union_left
      · exact Or.inr (by simp)
      · exact Or.inl subset_union_right
      · exact Or.inr (by simp)
    · obtain ⟨C, hC, hin⟩ := h.edges_inside S hS'
      by_cases hCA : C = A
      · subst hCA
        exact ⟨_, hU, hin.imp (·.trans subset_union_left) (·.trans subset_union_left)⟩
      · by_cases hCB : C = B
        · subst hCB
          exact ⟨_, hU, hin.imp (·.trans subset_union_right) (·.trans subset_union_right)⟩
        · exact ⟨C, mem_insert_of_mem (mem_erase.2 ⟨hCB, mem_erase.2 ⟨hCA, hC⟩⟩), hin⟩
  · -- recorded edges are compatible
    rcases mem_union.1 hS' with hS' | hS' <;> rcases mem_union.1 hS'' with hS'' | hS''
    · rcases hsub S hS' with (rfl | rfl) | (rfl | rfl) <;>
        rcases hsub S' hS'' with (rfl | rfl) | (rfl | rfl)
      · exact hAA
      · exact hAA.compl_right
      · exact hABc
      · exact hABc.compl_right
      · exact hAA.compl_left
      · exact hAA.compl_left.compl_right
      · exact hABc.compl_left
      · exact hABc.compl_left.compl_right
      · exact hABc.symm
      · exact hABc.symm.compl_right
      · exact hBB
      · exact hBB.compl_right
      · exact hABc.symm.compl_left
      · exact hABc.symm.compl_left.compl_right
      · exact hBB.compl_left
      · exact hBB.compl_left.compl_right
    · exact hnew S hS' S' hS''
    · exact (hnew S' hS'' S hS').symm
    · exact h.edges_compat S hS' S' hS''
  · -- complements
    rcases mem_union.1 hS' with hS' | hS'
    · refine mem_union_left _ ?_
      rcases hsub S hS' with (rfl | rfl) | (rfl | rfl) <;> simp
    · exact mem_union_right _ (h.edges_compl S hS')
  · -- nonempty
    rcases mem_union.1 hS' with hS' | hS'
    · rcases hsub S hS' with (rfl | rfl) | (rfl | rfl)
      · exact ⟨a, ha⟩
      · exact ⟨b, mem_compl.2 (disjoint_right.1 hd hb)⟩
      · exact ⟨b, hb⟩
      · exact ⟨a, mem_compl.2 (disjoint_left.1 hd ha)⟩
    · exact h.edges_nonempty S hS'

/-- **The output at the end of a run**, with two active nodes left. -/
theorem output_spec (hS : IsSplitFamily T) (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (h : Inv T w s)
    (h2 : s.active.card = 2) :
    IsSplitFamily s.output.1 ∧ T ⊆ s.output.1 ∧ (∀ A ∈ T, s.output.2 A = w A) ∧
      ∀ A ∈ s.output.1, A ∉ T → s.output.2 A = 0 := by
  have hP := h.clusters
  have hT := hS.compl_mem
  have hw' : ∀ A ∈ T, w Aᶜ = w A := fun A hA => (hw A hA).2
  obtain ⟨E, F, hEF, hact⟩ := card_eq_two.1 h2
  have hE : E ∈ s.active := by simp [hact]
  have hF : F ∈ s.active := by simp [hact]
  have hd := hP.disjoint E hE F hF hEF
  have hFE : F = Eᶜ := by
    refine Subset.antisymm (subset_compl_iff_disjoint_left.2 hd) fun x hx => ?_
    obtain ⟨C, hC, hxC⟩ := hP.cover x
    rw [hact] at hC
    rcases mem_insert.1 hC with rfl | hC
    · exact absurd hxC (mem_compl.1 hx)
    · rw [mem_singleton] at hC
      exact hC ▸ hxC
  obtain ⟨e, he⟩ := hP.nonempty E hE
  obtain ⟨f, hf⟩ := hP.nonempty F hF
  have hEu : E ≠ univ := fun e' => disjoint_left.1 hd (e' ▸ mem_univ f) hf
  have hFu : F ≠ univ := fun e' => disjoint_left.1 hd he (e' ▸ mem_univ e)
  have hmemA : ∀ {S : Finset X}, S ∈ s.active ↔ S = E ∨ S = F := by
    intro S
    rw [hact, mem_insert, mem_singleton]
  have hrow : ∀ {S : Finset X}, S ∈ s.active → s.rowSum S = pend T w S := by
    intro S hSa
    have hsum : ∀ U ∈ s.active, s.rowSum U = clusterDist T w U E + clusterDist T w U F := by
      intro U hU
      rw [h.rowSum_eq hU, rowC, hact, sum_pair hEF]
    rw [hsum S hSa]
    rcases hmemA.1 hSa with rfl | rfl
    · rw [clusterDist_self (hP.nonempty S hE), zero_add, hFE, clusterDist_compl]
    · rw [clusterDist_self (hP.nonempty S hF), add_zero, hFE, clusterDist_comm hT hw' Eᶜ E,
        clusterDist_compl, ← pend_compl hT hw' E]
  have hval : ∀ S ∈ s.output.1, s.output.2 S = pend T w S := by
    intro S hS'
    change (if S ∈ s.active then s.rowSum S else s.len S) = _
    by_cases hSa : S ∈ s.active
    · rw [ite_eq_left hSa, hrow hSa]
    · rw [ite_eq_right hSa]
      rcases mem_union.1 hS' with hS' | hS'
      · exact absurd (mem_filter.1 hS').1 hSa
      · exact h.len_eq S hS'
  have hact_mem : ∀ {S : Finset X}, S ∈ s.active → S ≠ univ → S ∈ s.output.1 := fun hS1 hS2 =>
    mem_union_left _ (mem_filter.2 ⟨hS1, hS2⟩)
  have hsubT : T ⊆ s.output.1 := by
    intro S hS'
    rcases h.covered S hS' with hed | hR
    · exact mem_union_right _ hed
    · rcases hR E hE with h1 | h1 <;> rcases hR F hF with h2' | h2'
      · exfalso
        obtain ⟨x, hx⟩ := hS.compl_nonempty S hS'
        refine mem_compl.1 hx ?_
        by_cases hxE : x ∈ E
        · exact h1 hxE
        · exact h2' (hFE ▸ mem_compl.2 hxE)
      · have : S = E := by
          refine Subset.antisymm (fun x hx => ?_) h1
          by_contra hxE
          exact disjoint_left.1 h2' (hFE ▸ mem_compl.2 hxE) hx
        exact this ▸ hact_mem hE hEu
      · have : S = F := by
          refine Subset.antisymm (fun x hx => ?_) h2'
          rw [hFE]
          exact mem_compl.2 fun hxE => disjoint_left.1 h1 hxE hx
        exact this ▸ hact_mem hF hFu
      · exfalso
        obtain ⟨x, hx⟩ := hS.nonempty S hS'
        by_cases hxE : x ∈ E
        · exact disjoint_left.1 h1 hxE hx
        · exact disjoint_left.1 h2' (hFE ▸ mem_compl.2 hxE) hx
  have hmem : ∀ {S : Finset X}, S ∈ s.output.1 ↔ (S = E ∨ S = F) ∨ S ∈ s.edges := by
    intro S
    constructor
    · intro hS'
      rcases mem_union.1 hS' with hS' | hS'
      · exact Or.inl (hmemA.1 (mem_filter.1 hS').1)
      · exact Or.inr hS'
    · rintro (h' | h')
      · rcases h' with rfl | rfl
        · exact hact_mem hE hEu
        · exact hact_mem hF hFu
      · exact mem_union_right _ h'
  have hEFc : Compat E F := Or.inr (Or.inr (Or.inl hd))
  have hsplit : IsSplitFamily s.output.1 := by
    refine ⟨fun S hS' => ?_, fun S hS' => ?_, fun S hS' => ?_, fun x => hsubT (hS.singleton_mem x),
      fun S hS' S' hS'' => ?_⟩
    · rcases hmem.1 hS' with (rfl | rfl) | hS'
      · exact ⟨e, he⟩
      · exact ⟨f, hf⟩
      · exact h.edges_nonempty S hS'
    · rcases hmem.1 hS' with (rfl | rfl) | hS'
      · exact ⟨f, mem_compl.2 (disjoint_right.1 hd hf)⟩
      · exact ⟨e, mem_compl.2 (disjoint_left.1 hd he)⟩
      · exact h.edges_nonempty _ (h.edges_compl S hS')
    · rcases hmem.1 hS' with (rfl | rfl) | hS'
      · exact hmem.2 (Or.inl (Or.inr hFE.symm))
      · exact hmem.2 (Or.inl (Or.inl (by rw [hFE, compl_compl])))
      · exact hmem.2 (Or.inr (h.edges_compl S hS'))
    · change Compat S S'
      rcases hmem.1 hS' with (rfl | rfl) | hS' <;> rcases hmem.1 hS'' with (rfl | rfl) | hS''
      · exact Or.inl (Subset.refl _)
      · exact hEFc
      · exact compat_of_inside hP hE (h.edges_inside _ hS'')
      · exact hEFc.symm
      · exact Or.inl (Subset.refl _)
      · exact compat_of_inside hP hF (h.edges_inside _ hS'')
      · exact (compat_of_inside hP hE (h.edges_inside _ hS')).symm
      · exact (compat_of_inside hP hF (h.edges_inside _ hS')).symm
      · exact h.edges_compat S hS' S' hS''
  refine ⟨hsplit, hsubT, fun A hA => ?_, fun A hA hnA => ?_⟩
  · rw [hval A (hsubT hA), pend, ite_eq_left hA]
  · rw [hval A hA, pend, ite_eq_right hnA]

end Inv

/-! ### Runs -/

theorem isClusters_init (d : X → X → ℝ) : IsClusters (init d).active := by
  refine ⟨fun C hC => ?_, fun C hC D hD hne => ?_, fun x => ⟨{x}, mem_image_of_mem _ (mem_univ x), by simp⟩⟩
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    exact singleton_nonempty x
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    obtain ⟨y, -, rfl⟩ := mem_image.1 hD
    rw [disjoint_singleton]
    exact fun e => hne (by rw [e])

theorem card_init (d : X → X → ℝ) : (init d).active.card = Fintype.card X := by
  rw [init, card_image_of_injective _ singleton_injective, card_univ]

/-- The invariant holds at the start of the run on a tree metric. -/
theorem inv_init (T : Finset (Finset X)) (w : Finset X → ℝ) : Inv T w (init (treeMetric T w)) := by
  refine ⟨isClusters_init _, fun C hC S _ => ?_, fun C hC D hD => ?_, fun S hS => absurd hS (notMem_empty S),
    fun S _ => Or.inr fun C hC => ?_, fun S hS => absurd hS (notMem_empty S),
    fun S hS => absurd hS (notMem_empty S), fun S hS => absurd hS (notMem_empty S),
    fun S hS => absurd hS (notMem_empty S)⟩
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    by_cases hx : x ∈ S
    · exact Or.inl (singleton_subset_iff.2 hx)
    · exact Or.inr (Or.inr (Or.inl (disjoint_singleton_left.2 hx)))
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    obtain ⟨y, -, rfl⟩ := mem_image.1 hD
    simp only [init, sum_singleton]
    exact treeMetric_eq_clusterDist x y
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hC
    by_cases hx : x ∈ S
    · exact Or.inl (singleton_subset_iff.2 hx)
    · exact Or.inr (disjoint_singleton_left.2 hx)

/-- Along a run on a tree metric, the invariant holds, and at least two nodes stay active. -/
theorem Run.inv {T : Finset (Finset X)} {w : Finset X → ℝ} (hS : IsSplitFamily T)
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) {s s' : State X} (hrun : Run s s') (h : Inv T w s)
    (h2 : 2 ≤ s.active.card) : Inv T w s' ∧ 2 ≤ s'.active.card := by
  induction hrun with
  | done s => exact ⟨h, h2⟩
  | step h3 hq _ ih =>
    refine ih (h.join hS hw h3 hq) ?_
    have := h.clusters.card_join hq.1 hq.2.1 hq.2.2.1
    change 2 ≤ (insert _ _ : Finset _).card
    omega

/-- **Every run of neighbor joining on a tree metric is exact**, however ties are broken and with polytomies:
it returns a tree refining `T`, with the same weights on the edges of `T`, and weight zero on the others. -/
theorem Run.output_spec {T : Finset (Finset X)} {w : Finset X → ℝ} (hT : IsUnrootedTree T)
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) {s : State X} (hrun : Run (init (treeMetric T w)) s)
    (hend : s.active.card ≤ 2) :
    IsUnrootedTree s.output.1 ∧ T ⊆ s.output.1 ∧ (∀ A ∈ T, s.output.2 A = w A) ∧
      ∀ A ∈ s.output.1, A ∉ T → s.output.2 A = 0 := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hS := hT.isSplitFamily hX
    have h2 : 2 ≤ (init (treeMetric T w)).active.card := by rwa [card_init]
    obtain ⟨hI, hc⟩ := hrun.inv hS hw (inv_init T w) h2
    obtain ⟨h1, h3, h4, h5⟩ := hI.output_spec hS hw (le_antisymm hend hc)
    exact ⟨(isUnrootedTree_iff hX _).2 h1, h3, h4, h5⟩
  · have hc : (init (treeMetric T w)).active.card < 3 := by
      rw [card_init]
      omega
    have hs : s = init (treeMetric T w) := by
      cases hrun with
      | done _ => rfl
      | step h3 _ _ => omega
    subst hs
    have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    have hT0 : T = ∅ := by
      refine eq_empty_of_forall_notMem fun A hA => hX ?_
      exact hT.two_le_card_of_mem hA
    have hout : (init (treeMetric T w)).output.1 = ∅ := by
      refine eq_empty_of_forall_notMem fun S hS => ?_
      rcases mem_union.1 hS with hS | hS
      · obtain ⟨hS, hne⟩ := mem_filter.1 hS
        obtain ⟨x, -, rfl⟩ := mem_image.1 hS
        refine hne (eq_univ_iff_forall.2 fun y => ?_)
        simp [Subsingleton.elim y x]
      · exact notMem_empty S hS
    rw [hout]
    refine ⟨hT0 ▸ hT, by simp [hT0], fun A hA => by simp [hT0] at hA, fun A hA => by simp at hA⟩

/-! ### Neighbours in a resolution, and cherries -/

/-- Neighbours are exactly the clusters whose union is compatible with the tree. -/
theorem nbr_iff_compat (hT : ∀ A ∈ T, Aᶜ ∈ T) (hP : IsClusters P) (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S)
    {A B : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    Nbr T A B ↔ ∀ S ∈ T, Compat (A ∪ B) S := by
  refine ⟨fun hn S hS => hn.compat_union hT hP hc hA hB hAB hS, fun h S hS hAS hBS => ?_⟩
  obtain ⟨a, ha⟩ := hP.nonempty A hA
  obtain ⟨b, hb⟩ := hP.nonempty B hB
  rcases h S hS with h' | h' | h' | h'
  · exact absurd (h' (mem_union_right _ hb)) (disjoint_left.1 hBS hb)
  · refine Or.inl (Subset.antisymm (fun x hx => ?_) hAS)
    exact (mem_union.1 (h' hx)).resolve_right fun hxB => disjoint_left.1 hBS hxB hx
  · exact absurd (hAS ha) (disjoint_left.1 h' (mem_union_left _ ha))
  · refine Or.inr (Subset.antisymm (fun x hx => ?_) (subset_compl_iff_disjoint_right.2 hBS))
    have hx' : x ∈ A ∪ B ∪ S := h' ▸ mem_univ x
    rcases mem_union.1 hx' with hx' | hx'
    · rcases mem_union.1 hx' with hx' | hx'
      · exact absurd (hAS hx') (mem_compl.1 hx)
      · exact hx'
    · exact absurd hx' (mem_compl.1 hx)

/-- **Neighbours are a cherry of a resolution of the tree**, when there is a third cluster: with the split of
`A ∪ B` added, the family of sides is a tree. -/
theorem Nbr.isResolutionOf (hX : 2 ≤ Fintype.card X) (hS : IsSplitFamily T) (hP : IsClusters P)
    (hc : ∀ C ∈ P, ∀ S ∈ T, Compat C S) {A B C : Finset X} (hA : A ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hn : Nbr T A B) :
    IsResolutionOf (insert (A ∪ B) (insert (A ∪ B)ᶜ T)) T := by
  have hU : ∀ S ∈ T, Compat (A ∪ B) S := fun S hS' => hn.compat_union hS.compl_mem hP hc hA hB hAB hS'
  obtain ⟨a, ha⟩ := hP.nonempty A hA
  obtain ⟨c, hc'⟩ := hP.nonempty C hC
  have hcU : c ∉ A ∪ B := fun h => by
    rcases mem_union.1 h with h | h
    · exact disjoint_left.1 (hP.disjoint A hA C hC hAC) h hc'
    · exact disjoint_left.1 (hP.disjoint B hB C hC hBC) h hc'
  have hUU : Compat (A ∪ B) (A ∪ B) := Or.inl (Subset.refl _)
  refine ⟨(isUnrootedTree_iff hX _).2 ⟨fun S hS' => ?_, fun S hS' => ?_, fun S hS' => ?_, fun x => ?_,
    fun S hS' S' hS'' => ?_⟩, fun S hS' => mem_insert_of_mem (mem_insert_of_mem hS')⟩
  · simp only [mem_insert] at hS'
    rcases hS' with rfl | rfl | hS'
    · exact ⟨a, mem_union_left _ ha⟩
    · exact ⟨c, mem_compl.2 hcU⟩
    · exact hS.nonempty S hS'
  · simp only [mem_insert] at hS'
    rcases hS' with rfl | rfl | hS'
    · exact ⟨c, mem_compl.2 hcU⟩
    · exact ⟨a, by simpa using mem_union_left _ ha⟩
    · exact hS.compl_nonempty S hS'
  · simp only [mem_insert] at hS' ⊢
    rcases hS' with rfl | rfl | hS'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (compl_compl _)
    · exact Or.inr (Or.inr (hS.compl_mem S hS'))
  · exact mem_insert_of_mem (mem_insert_of_mem (hS.singleton_mem x))
  · change Compat S S'
    simp only [mem_insert] at hS' hS''
    rcases hS' with rfl | rfl | hS' <;> rcases hS'' with rfl | rfl | hS''
    · exact hUU
    · exact hUU.compl_right
    · exact hU S' hS''
    · exact hUU.compl_left
    · exact hUU.compl_left.compl_right
    · exact (hU S' hS'').compl_left
    · exact (hU S hS').symm
    · exact (hU S hS').compl_left.symm
    · exact hS.compatible S hS' S' hS''

/-- A binary rooting at the edge of the taxon `b`, that is, with the cluster `{b}ᶜ`: if the only sides separating `a`
from `b` are their pendant edges, then `a, b` are a cherry. -/
theorem mem_of_compl_singleton_mem {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hbin : ∀ A ∈ H, 2 ≤ A.card → (childClusters H A).card = 2) (hX : 3 ≤ Fintype.card X)
    (hS : IsSplitFamily T) (hT : unroot H = T) {a b : X} (hab : a ≠ b) (hb : ({b} : Finset X)ᶜ ∈ H)
    (hsep : ∀ S ∈ T, a ∈ S → b ∉ S → S = {a} ∨ Sᶜ = {b}) : ({a, b} : Finset X) ∈ T := by
  have hmemT : ∀ {D : Finset X}, D ∈ H → D ≠ univ → D ∈ T := fun hD hne =>
    hT ▸ mem_unroot.2 (Or.inl ⟨hD, hne⟩)
  have hK2 : 2 ≤ (({b} : Finset X)ᶜ).card := by
    rw [card_compl, card_singleton]
    omega
  have hch := hbin _ hb hK2
  have haK : a ∈ ({b} : Finset X)ᶜ := by simpa using hab
  obtain ⟨D, hD, haD⟩ := hH.exists_mem_childClusters hK2 haK
  obtain ⟨D', hD', hne⟩ := exists_mem_ne (by omega : 1 < (childClusters H ({b} : Finset X)ᶜ).card) D
  obtain ⟨hDH, hDlt, -⟩ := mem_childClusters.1 hD
  obtain ⟨hD'H, hD'lt, -⟩ := mem_childClusters.1 hD'
  have hbD : b ∉ D := fun h => by simpa using hDlt.1 h
  have hbD' : b ∉ D' := fun h => by simpa using hD'lt.1 h
  have hDu : D ≠ univ := fun e => hbD (e ▸ mem_univ b)
  have hD'u : D' ≠ univ := fun e => hbD' (e ▸ mem_univ b)
  have hDa : D = {a} := by
    rcases hsep D (hmemT hDH hDu) haD hbD with h | h
    · exact h
    · exact absurd (by rw [← h, compl_compl]) (ne_of_ssubset hDlt)
  have hdis := hH.disjoint_of_mem_childClusters hD hD' hne.symm
  have heq : ({a, b} : Finset X) = D'ᶜ := by
    ext x
    simp only [mem_insert, mem_singleton, mem_compl]
    constructor
    · rintro (rfl | rfl)
      · exact disjoint_left.1 hdis haD
      · exact hbD'
    · intro hx
      by_contra hxn
      push Not at hxn
      have hxK : x ∈ ({b} : Finset X)ᶜ := by simpa using hxn.2
      obtain ⟨C, hC, hxC⟩ := hH.exists_mem_childClusters hK2 hxK
      obtain ⟨E, F, hEF, hEFe⟩ := card_eq_two.1 hch
      rw [hEFe, mem_insert, mem_singleton] at hC hD hD'
      have hCD : C = D ∨ C = D' := by
        rcases hC with rfl | rfl <;> rcases hD with rfl | rfl <;> rcases hD' with rfl | rfl <;> simp_all
      rcases hCD with rfl | rfl
      · rw [hDa, mem_singleton] at hxC
        exact hxn.1 hxC
      · exact hx hxC
  rw [heq]
  exact hS.compl_mem _ (hmemT hD'H hD'u)

/-- In a binary tree, neighbouring taxa are a cherry. -/
theorem mem_of_nbr_of_isBinaryTree (hT : IsBinaryTree T) (hX : 3 ≤ Fintype.card X) {a b : X} (hab : a ≠ b)
    (hn : Nbr T {a} {b}) : ({a, b} : Finset X) ∈ T := by
  obtain ⟨H, hH, hun, hbin⟩ := hT
  have hTu : IsUnrootedTree T := ⟨H, hH, hun⟩
  have hS : IsSplitFamily T := hTu.isSplitFamily (by omega)
  have hsep : ∀ S ∈ T, a ∈ S → b ∉ S → S = {a} ∨ Sᶜ = {b} := fun S hS' ha hb =>
    hn S hS' (singleton_subset_iff.2 ha) (disjoint_singleton_left.2 hb)
  have hsep' : ∀ S ∈ T, b ∈ S → a ∉ S → S = {b} ∨ Sᶜ = {a} := fun S hS' hb ha =>
    hn.symm hS.compl_mem S hS' (singleton_subset_iff.2 hb) (disjoint_singleton_left.2 ha)
  have hmemT : ∀ {D : Finset X}, D ∈ H → D ≠ univ → D ∈ T := fun hD hne =>
    hun ▸ mem_unroot.2 (Or.inl ⟨hD, hne⟩)
  obtain ⟨K, hK, hsub, hleast⟩ := hH.exists_least (A := {a, b}) ⟨a, by simp⟩
  have haK : a ∈ K := hsub (by simp)
  have hbK : b ∈ K := hsub (by simp)
  have hK2 : 2 ≤ K.card := one_lt_card.2 ⟨a, haK, b, hbK, hab⟩
  obtain ⟨Ba, hBa, haB⟩ := hH.exists_mem_childClusters hK2 haK
  obtain ⟨Bb, hBb, hbB⟩ := hH.exists_mem_childClusters hK2 hbK
  obtain ⟨hBaH, hBalt, -⟩ := mem_childClusters.1 hBa
  obtain ⟨hBbH, hBblt, -⟩ := mem_childClusters.1 hBb
  have hne : Ba ≠ Bb := by
    rintro rfl
    refine not_subset_of_ssubset hBalt (hleast Ba hBaH fun x hx => ?_)
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haB
    · exact hbB
  have hdis := hH.disjoint_of_mem_childClusters hBa hBb hne
  have hbBa : b ∉ Ba := disjoint_right.1 hdis hbB
  have haBb : a ∉ Bb := disjoint_left.1 hdis haB
  have hBau : Ba ≠ univ := fun e => hbBa (e ▸ mem_univ b)
  have hBbu : Bb ≠ univ := fun e => haBb (e ▸ mem_univ a)
  rcases hsep Ba (hmemT hBaH hBau) haB hbBa with h1 | h1
  · rcases hsep' Bb (hmemT hBbH hBbu) hbB haBb with h2 | h2
    · -- both are single taxa: `K = {a, b}`
      have hKeq : K = {a, b} := by
        refine Subset.antisymm (fun x hx => ?_) hsub
        obtain ⟨C, hC, hxC⟩ := hH.exists_mem_childClusters hK2 hx
        obtain ⟨E, F, hEF, hEFe⟩ := card_eq_two.1 (hbin K hK hK2)
        have hBa' := hBa
        have hBb' := hBb
        rw [hEFe, mem_insert, mem_singleton] at hC hBa' hBb'
        have hCD : C = Ba ∨ C = Bb := by
          rcases hC with rfl | rfl <;> rcases hBa' with rfl | rfl <;> rcases hBb' with rfl | rfl <;> simp_all
        rcases hCD with rfl | rfl
        · rw [h1, mem_singleton] at hxC
          simp [hxC]
        · rw [h2, mem_singleton] at hxC
          simp [hxC]
      have hKu : K ≠ univ := by
        rintro rfl
        have : Fintype.card X = 2 := by
          rw [← card_univ, hKeq, card_pair hab]
        omega
      rw [← hKeq]
      exact hmemT hK hKu
    · have hb' : ({a} : Finset X)ᶜ ∈ H := by
        rw [← h2, compl_compl]
        exact hBbH
      rw [pair_comm]
      exact mem_of_compl_singleton_mem hH hbin hX hS hun hab.symm hb' hsep'
  · have hb' : ({b} : Finset X)ᶜ ∈ H := by
      rw [← h1, compl_compl]
      exact hBaH
    exact mem_of_compl_singleton_mem hH hbin hX hS hun hab hb' hsep

/-- **Studier and Keppler's theorem at the start of a run on a binary tree**: a pair of taxa minimizing `Q` is a
cherry. -/
theorem cherry_of_isQMin {T : Finset (Finset X)} {w : Finset X → ℝ} (hT : IsBinaryTree T)
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) (hX : 3 ≤ Fintype.card X) {a b : X}
    (hq : (init (treeMetric T w)).IsQMin {a} {b}) : ({a, b} : Finset X) ∈ T := by
  obtain ⟨H, hH, hun, hbin⟩ := id hT
  have hS : IsSplitFamily T := IsUnrootedTree.isSplitFamily ⟨H, hH, hun⟩ (by omega)
  have hab : a ≠ b := fun e => hq.2.2.1 (by rw [e])
  exact mem_of_nbr_of_isBinaryTree hT hX hab ((inv_init T w).nbr_of_isQMin hS hw hq)

/-! ### The output is a binary tree -/

/-- A cluster that is the union of two disjoint members of a hierarchy has these as its children. -/
theorem childClusters_eq_pair {H : Finset (Finset X)} (hH : ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    {B C : Finset X} (hB : B ∈ H) (hC : C ∈ H) (hBC : Disjoint B C) (hBne : B.Nonempty)
    (hCne : C.Nonempty) : childClusters H (B ∪ C) = {B, C} := by
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨c, hc⟩ := hCne
  have hBlt : B ⊂ B ∪ C := ⟨subset_union_left, fun h => disjoint_left.1 hBC (h (mem_union_right _ hc)) hc⟩
  have hClt : C ⊂ B ∪ C := ⟨subset_union_right, fun h => disjoint_left.1 hBC hb (h (mem_union_left _ hb))⟩
  -- nothing in the hierarchy lies strictly between a child and the union
  have hbetween : ∀ {U V : Finset X}, U ∈ H → V ∈ H → U ∪ V = B ∪ C → Disjoint U V → U.Nonempty →
      ∀ E ∈ H, U ⊂ E → ¬ E ⊂ B ∪ C := by
    intro U V hU hV hUV hd hne E hE hlt hltu
    obtain ⟨x, hxE, hxU⟩ := exists_of_ssubset hlt
    have hxV : x ∈ V := by
      have : x ∈ U ∪ V := hUV ▸ hltu.1 hxE
      exact (mem_union.1 this).resolve_left hxU
    rcases hH E hE V hV with h | h | h
    · obtain ⟨u, hu⟩ := hne
      exact disjoint_left.1 hd hu (h (hlt.1 hu))
    · refine not_subset_of_ssubset hltu ?_
      rw [← hUV]
      exact union_subset hlt.1 h
    · exact disjoint_left.1 h hxE hxV
  ext D
  simp only [mem_childClusters, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hD, hlt, hmax⟩
    rcases hH D hD B hB with h | h | h
    · left
      by_contra hne
      exact hmax B hB (h.ssubset_of_ne hne) hBlt
    · left
      by_contra hne
      exact hbetween hB hC rfl hBC ⟨b, hb⟩ D hD (h.ssubset_of_ne (Ne.symm hne)) hlt
    · right
      have hDC : D ⊆ C := fun x hx =>
        (mem_union.1 (hlt.1 hx)).resolve_left (disjoint_left.1 h hx)
      by_contra hne
      exact hmax C hC (hDC.ssubset_of_ne hne) hClt
  · rintro (rfl | rfl)
    · exact ⟨hB, hBlt, hbetween hB hC rfl hBC ⟨b, hb⟩⟩
    · exact ⟨hC, hClt, hbetween hC hB (union_comm _ _) hBC.symm ⟨c, hc⟩⟩

/-- The structure of a run on any input: the clusters `R` recorded so far form, with the active nodes, a binary
forest. -/
structure BinInv (R : Finset (Finset X)) (s : State X) : Prop where
  clusters : IsClusters s.active
  edges_eq : s.edges = R ∪ R.image compl
  inside : ∀ A ∈ R, ∃ C ∈ s.active, A ⊂ C
  laminar : ∀ A ∈ R, ∀ B ∈ R, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B
  nonempty : ∀ A ∈ R, A.Nonempty
  singleton : ∀ x, {x} ∈ R ∪ s.active
  children : ∀ A ∈ R ∪ s.active, 2 ≤ A.card → ∃ B ∈ R, ∃ C ∈ R, Disjoint B C ∧ A = B ∪ C

theorem BinInv.join {R : Finset (Finset X)} {s : State X} (h : BinInv R s) {A B : Finset X}
    (hA : A ∈ s.active) (hB : B ∈ s.active) (hAB : A ≠ B) :
    BinInv (insert A (insert B R)) (s.join A B) := by
  have hP := h.clusters
  have hd := hP.disjoint A hA B hB hAB
  have hAne := hP.nonempty A hA
  have hBne := hP.nonempty B hB
  have hmem : ∀ {C : Finset X}, C ∈ s.active → C ≠ A → C ≠ B →
      C ∈ insert (A ∪ B) ((s.active.erase A).erase B) := fun hC h1 h2 =>
    mem_insert_of_mem (mem_erase.2 ⟨h2, mem_erase.2 ⟨h1, hC⟩⟩)
  have hrest : ∀ {C : Finset X}, C ∈ (s.active.erase A).erase B → C ≠ B ∧ C ≠ A ∧ C ∈ s.active :=
    fun hC => by simpa only [mem_erase] using hC
  have hR : ∀ {D : Finset X}, D ∈ R → D ∈ insert A (insert B R) := fun hD =>
    mem_insert_of_mem (mem_insert_of_mem hD)
  -- old clusters against the two joined
  have hold : ∀ {E D : Finset X}, E ∈ s.active → D ∈ R → D ⊆ E ∨ Disjoint D E := by
    intro E D hE hD
    obtain ⟨C, hC, hlt⟩ := h.inside D hD
    by_cases hCE : C = E
    · exact Or.inl (hCE ▸ hlt.1)
    · exact Or.inr ((hP.disjoint C hC E hE hCE).mono_left hlt.1)
  refine ⟨hP.join hA hB, ?_, fun D hD => ?_, fun D hD E hE => ?_, fun D hD => ?_, fun x => ?_,
    fun D hD hD2 => ?_⟩
  · change {A, Aᶜ, B, Bᶜ} ∪ s.edges = _
    rw [h.edges_eq]
    ext S
    simp only [mem_union, mem_insert, mem_singleton, mem_image]
    constructor
    · rintro ((rfl | rfl | rfl | rfl) | (h' | ⟨D, hD, rfl⟩))
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨_, Or.inl rfl, rfl⟩
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr ⟨_, Or.inr (Or.inl rfl), rfl⟩
      · exact Or.inl (Or.inr (Or.inr h'))
      · exact Or.inr ⟨_, Or.inr (Or.inr hD), rfl⟩
    · rintro ((rfl | rfl | h') | ⟨D, (rfl | rfl | hD), rfl⟩)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inl h')
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inr ⟨D, hD, rfl⟩)
  · have hU : A ∪ B ∈ insert (A ∪ B) ((s.active.erase A).erase B) := mem_insert_self _ _
    have hAlt : A ⊂ A ∪ B := ⟨subset_union_left, fun h' => by
      obtain ⟨b, hb⟩ := hBne
      exact disjoint_left.1 hd (h' (mem_union_right _ hb)) hb⟩
    have hBlt : B ⊂ A ∪ B := ⟨subset_union_right, fun h' => by
      obtain ⟨a, ha⟩ := hAne
      exact disjoint_left.1 hd ha (h' (mem_union_left _ ha))⟩
    rcases mem_insert.1 hD with rfl | hD
    · exact ⟨_, hU, hAlt⟩
    · rcases mem_insert.1 hD with rfl | hD
      · exact ⟨_, hU, hBlt⟩
      · obtain ⟨C, hC, hlt⟩ := h.inside D hD
        by_cases hCA : C = A
        · exact ⟨_, hU, hlt.trans_subset (hCA ▸ subset_union_left)⟩
        · by_cases hCB : C = B
          · exact ⟨_, hU, hlt.trans_subset (hCB ▸ subset_union_right)⟩
          · exact ⟨C, hmem hC hCA hCB, hlt⟩
  · simp only [mem_insert] at hD hE
    have hup : ∀ {U V : Finset X}, V ⊆ U ∨ Disjoint V U → U ⊆ V ∨ V ⊆ U ∨ Disjoint U V := by
      rintro U V (h' | h')
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h'.symm)
    have hdown : ∀ {U V : Finset X}, V ⊆ U ∨ Disjoint V U → V ⊆ U ∨ U ⊆ V ∨ Disjoint V U := by
      rintro U V (h' | h')
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    rcases hD with rfl | rfl | hD <;> rcases hE with rfl | rfl | hE
    · exact Or.inl (Subset.refl _)
    · exact Or.inr (Or.inr hd)
    · exact hup (hold hA hE)
    · exact Or.inr (Or.inr hd.symm)
    · exact Or.inl (Subset.refl _)
    · exact hup (hold hB hE)
    · exact hdown (hold hA hD)
    · exact hdown (hold hB hD)
    · exact h.laminar D hD E hE
  · rcases mem_insert.1 hD with rfl | hD
    · exact hAne
    · rcases mem_insert.1 hD with rfl | hD
      · exact hBne
      · exact h.nonempty D hD
  · rcases mem_union.1 (h.singleton x) with hx | hx
    · exact mem_union_left _ (hR hx)
    · by_cases h1 : ({x} : Finset X) = A
      · exact mem_union_left _ (h1 ▸ mem_insert_self _ _)
      · by_cases h2 : ({x} : Finset X) = B
        · exact mem_union_left _ (mem_insert_of_mem (h2 ▸ mem_insert_self _ _))
        · exact mem_union_right _ (hmem hx h1 h2)
  · have hold' : ∀ {E : Finset X}, E ∈ R ∪ s.active → 2 ≤ E.card →
        ∃ B' ∈ insert A (insert B R), ∃ C ∈ insert A (insert B R), Disjoint B' C ∧ E = B' ∪ C := by
      intro E hE hE2
      obtain ⟨B', hB', C, hC, hdis, e⟩ := h.children E hE hE2
      exact ⟨B', hR hB', C, hR hC, hdis, e⟩
    rcases mem_union.1 hD with hD | hD
    · rcases mem_insert.1 hD with rfl | hD
      · exact hold' (mem_union_right _ hA) hD2
      · rcases mem_insert.1 hD with rfl | hD
        · exact hold' (mem_union_right _ hB) hD2
        · exact hold' (mem_union_left _ hD) hD2
    · rcases mem_insert.1 hD with rfl | hD
      · exact ⟨A, mem_insert_self _ _, B, mem_insert_of_mem (mem_insert_self _ _), hd, rfl⟩
      · exact hold' (mem_union_right _ (hrest hD).2.2) hD2

theorem binInv_init (d : X → X → ℝ) : BinInv ∅ (init d) := by
  refine ⟨isClusters_init d, by simp [init], fun A hA => absurd hA (notMem_empty A),
    fun A hA => absurd hA (notMem_empty A), fun A hA => absurd hA (notMem_empty A),
    fun x => mem_union_right _ (mem_image_of_mem _ (mem_univ x)), fun A hA h2 => ?_⟩
  rw [empty_union] at hA
  obtain ⟨x, -, rfl⟩ := mem_image.1 hA
  simp at h2

theorem Run.binInv {R : Finset (Finset X)} {s s' : State X} (hrun : Run s s') (h : BinInv R s)
    (h2 : 2 ≤ s.active.card) :
    ∃ R', BinInv R' s' ∧ 2 ≤ s'.active.card := by
  induction hrun generalizing R with
  | done s => exact ⟨R, h, h2⟩
  | step h3 hq _ ih =>
    refine ih (h.join hq.1 hq.2.1 hq.2.2.1) ?_
    have := h.clusters.card_join hq.1 hq.2.1 hq.2.2.1
    change 2 ≤ (insert _ _ : Finset _).card
    omega

/-- The output of a run ending with two active nodes is a binary tree. -/
theorem BinInv.isBinaryTree {R : Finset (Finset X)} {s : State X} (h : BinInv R s)
    (h2 : s.active.card = 2) : IsBinaryTree s.output.1 := by
  have hP := h.clusters
  obtain ⟨E, F, hEF, hact⟩ := card_eq_two.1 h2
  have hE : E ∈ s.active := by simp [hact]
  have hF : F ∈ s.active := by simp [hact]
  have hd := hP.disjoint E hE F hF hEF
  obtain ⟨e, he⟩ := hP.nonempty E hE
  obtain ⟨f, hf⟩ := hP.nonempty F hF
  have hun : E ∪ F = univ := eq_univ_iff_forall.2 fun x => by
    obtain ⟨C, hC, hx⟩ := hP.cover x
    rw [hact, mem_insert, mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact mem_union_left _ hx
    · exact mem_union_right _ hx
  have hEu : E ≠ univ := fun e' => disjoint_left.1 hd (e' ▸ mem_univ f) hf
  have hFu : F ≠ univ := fun e' => disjoint_left.1 hd he (e' ▸ mem_univ e)
  have hRu : ∀ A ∈ R, A ≠ univ := by
    rintro A hA rfl
    obtain ⟨C, -, hlt⟩ := h.inside _ hA
    exact not_subset_of_ssubset hlt (subset_univ C)
  have hne : ∀ A ∈ R ∪ s.active, A.Nonempty := fun A hA => by
    rcases mem_union.1 hA with hA | hA
    · exact h.nonempty A hA
    · exact hP.nonempty A hA
  -- the hierarchy
  have hlam : ∀ A ∈ insert univ (R ∪ s.active), ∀ B ∈ insert univ (R ∪ s.active),
      A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    have hold : ∀ {C D : Finset X}, C ∈ s.active → D ∈ R → D ⊆ C ∨ Disjoint D C := by
      intro C D hC hD
      obtain ⟨C', hC', hlt⟩ := h.inside D hD
      by_cases hCE : C' = C
      · exact Or.inl (hCE ▸ hlt.1)
      · exact Or.inr ((hP.disjoint C' hC' C hC hCE).mono_left hlt.1)
    intro A hA B hB
    rcases mem_insert.1 hA with rfl | hA
    · exact Or.inr (Or.inl (subset_univ B))
    rcases mem_insert.1 hB with rfl | hB
    · exact Or.inl (subset_univ A)
    rcases mem_union.1 hA with hA | hA <;> rcases mem_union.1 hB with hB | hB
    · exact h.laminar A hA B hB
    · rcases hold hB hA with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases hold hA hB with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h'.symm)
    · by_cases hAB : A = B
      · exact Or.inl (hAB ▸ Subset.refl _)
      · exact Or.inr (Or.inr (hP.disjoint A hA B hB hAB))
  have hnotu : univ ∉ R ∪ s.active := fun hu => by
    rcases mem_union.1 hu with hu | hu
    · exact hRu _ hu rfl
    · rw [hact, mem_insert, mem_singleton] at hu
      rcases hu with hu | hu
      · exact hEu hu.symm
      · exact hFu hu.symm
  refine ⟨insert univ (R ∪ s.active), ⟨mem_insert_self _ _, fun x => mem_insert_of_mem (h.singleton x),
    fun A hA => ?_, hlam⟩, ?_, fun A hA hA2 => ?_⟩
  · rcases mem_insert.1 hA with rfl | hA
    · exact ⟨e, mem_univ e⟩
    · exact hne A hA
  · ext S
    rw [mem_unroot]
    simp only [mem_insert, ne_eq, State.output, mem_union, mem_filter]
    rw [h.edges_eq, mem_union, mem_image]
    have hact' : ∀ {U : Finset X}, U ∈ s.active ↔ U = E ∨ U = F := by
      intro U
      rw [hact, mem_insert, mem_singleton]
    have hcE : Eᶜ = F := by
      refine Subset.antisymm (fun x hx => ?_) (subset_compl_iff_disjoint_left.2 hd)
      have : x ∈ E ∪ F := hun ▸ mem_univ x
      exact (mem_union.1 this).resolve_left (mem_compl.1 hx)
    have hcF : Fᶜ = E := by rw [← hcE, compl_compl]
    constructor
    · rintro (⟨(hu | hS | hS), hne'⟩ | ⟨(hu | hS | hS), hne'⟩)
      · exact absurd hu hne'
      · exact Or.inr (Or.inl hS)
      · exact Or.inl ⟨hS, fun e' => hnotu (e' ▸ mem_union_right _ hS)⟩
      · exact absurd hu hne'
      · exact Or.inr (Or.inr ⟨_, hS, by simp⟩)
      · refine Or.inl ⟨?_, ?_⟩
        · rcases hact'.1 hS with hS' | hS'
          · rw [← hcF, compl_inj_iff] at hS'
            exact hact'.2 (Or.inr hS')
          · rw [← hcE, compl_inj_iff] at hS'
            exact hact'.2 (Or.inl hS')
        · rintro rfl
          rcases hact'.1 hS with hS' | hS'
          · exact (hP.nonempty E hE).ne_empty (by rw [← hS']; simp)
          · exact (hP.nonempty F hF).ne_empty (by rw [← hS']; simp)
    · rintro (⟨hS, hne'⟩ | hS | ⟨D, hD, rfl⟩)
      · exact Or.inl ⟨Or.inr (Or.inr hS), hne'⟩
      · exact Or.inl ⟨Or.inr (Or.inl hS), hRu S hS⟩
      · exact Or.inr ⟨by simpa using Or.inr (Or.inl hD), by simpa using hRu D hD⟩
  · have hdec : ∃ B ∈ insert univ (R ∪ s.active), ∃ C ∈ insert univ (R ∪ s.active),
        Disjoint B C ∧ B.Nonempty ∧ C.Nonempty ∧ A = B ∪ C ∧ B ≠ C := by
      rcases mem_insert.1 hA with rfl | hA'
      · refine ⟨E, mem_insert_of_mem (mem_union_right _ hE), F, mem_insert_of_mem (mem_union_right _ hF),
          hd, ⟨e, he⟩, ⟨f, hf⟩, hun.symm, hEF⟩
      · obtain ⟨B, hB, C, hC, hdis, rfl⟩ := h.children A hA' hA2
        have hBne := h.nonempty B hB
        refine ⟨B, mem_insert_of_mem (mem_union_left _ hB), C, mem_insert_of_mem (mem_union_left _ hC),
          hdis, hBne, h.nonempty C hC, rfl, ?_⟩
        rintro rfl
        obtain ⟨b, hb⟩ := hBne
        exact disjoint_left.1 hdis hb hb
    obtain ⟨B, hB, C, hC, hdis, hBne, hCne, rfl, hBC⟩ := hdec
    rw [childClusters_eq_pair hlam hB hC hdis hBne hCne, card_pair hBC]

/-- **The output of a run of neighbor joining is a binary tree**, on any input: this needs no property of the
distances. -/
theorem Run.isBinaryTree [Nonempty X] {d : X → X → ℝ} {s : State X} (hrun : Run (init d) s)
    (hend : s.active.card ≤ 2) : IsBinaryTree s.output.1 := by
  by_cases hX : 2 ≤ Fintype.card X
  · have h2 : 2 ≤ (init d).active.card := by rwa [card_init]
    obtain ⟨R', hR', hc⟩ := hrun.binInv (binInv_init d) h2
    exact hR'.isBinaryTree (le_antisymm hend hc)
  · have hc : (init d).active.card < 3 := by
      rw [card_init]
      omega
    have hs : s = init d := by
      cases hrun with
      | done _ => rfl
      | step h3 _ _ => omega
    subst hs
    have hsub : Subsingleton X := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    obtain ⟨x⟩ := ‹Nonempty X›
    have huniv : ∀ y : X, ({y} : Finset X) = univ := fun y => eq_univ_iff_forall.2 fun z => by
      simp [Subsingleton.elim z y]
    have hout : (init d).output.1 = ∅ := by
      refine eq_empty_of_forall_notMem fun S hS => ?_
      rcases mem_union.1 hS with hS | hS
      · obtain ⟨hS, hne⟩ := mem_filter.1 hS
        obtain ⟨y, -, rfl⟩ := mem_image.1 hS
        exact hne (huniv y)
      · exact notMem_empty S hS
    rw [hout]
    refine ⟨{univ}, ⟨mem_singleton_self _, fun y => by simp [huniv y], fun A hA => ?_, fun A hA B hB => ?_⟩,
      by simp [unroot], fun A hA hA2 => ?_⟩
    · rw [mem_singleton.1 hA]
      exact ⟨x, mem_univ x⟩
    · rw [mem_singleton.1 hA, mem_singleton.1 hB]
      exact Or.inl (Subset.refl _)
    · rw [mem_singleton.1 hA, ← huniv x] at hA2
      simp at hA2

/-! ### The method -/

omit [Fintype X] [DecidableEq X] in
theorem exists_isQMin (s : State X) (h2 : 2 ≤ s.active.card) : s.qMinimizers.Nonempty := by
  have hne : s.active.offDiag.Nonempty := by
    obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.1 h2
    exact ⟨(A, B), mem_offDiag.2 ⟨hA, hB, hAB⟩⟩
  obtain ⟨p, hp, hmin⟩ := exists_min_image s.active.offDiag (fun p => s.Q p.1 p.2) hne
  obtain ⟨hA, hB, hAB⟩ := mem_offDiag.1 hp
  exact ⟨p, mem_filter.2 ⟨hp, hA, hB, hAB, fun C hC D hD hCD =>
    hmin (C, D) (mem_offDiag.2 ⟨hC, hD, hCD⟩)⟩⟩

omit [Fintype X] [DecidableEq X] in
theorem isQMin_pick (tb : TieBreak X) (s : State X) (h2 : 2 ≤ s.active.card) :
    s.IsQMin (tb.pick s.qMinimizers).1 (tb.pick s.qMinimizers).2 :=
  (mem_filter.1 (tb.pick_mem _ (exists_isQMin s h2))).2

/-- The closed form of `State.joinCost` with `n` active nodes: `5 n² + 4 n + 4` for `n ≥ 2`. -/
def joinOps (n : ℕ) : ℕ :=
  n * n + 3 * (n * n - n) + (n * n - n) + 2 * 6 + (2 * (4 * (n - 2)) + 1) + (3 + 4)

omit [Fintype X] in
theorem joinCost_eq {s : State X} (hs : s.active = P) {A B : Finset X} (hA : A ∈ P)
    (hB : B ∈ P) (hAB : A ≠ B) : s.joinCost A B = joinOps P.card := by
  have hB' : B ∈ P.erase A := mem_erase.2 ⟨hAB.symm, hB⟩
  rw [State.joinCost, hs, joinOps, offDiag_card, sum_const, smul_eq_mul, card_erase_of_mem hB',
    card_erase_of_mem hA]
  rfl

/-- The run of the method, step by step: each is a join of a `Q`-minimizer, there are `m` joins from `m + 2` nodes,
and the operations add up. -/
theorem iterate_stepWith (tb : TieBreak X) (m : ℕ) (s : State X) (hP : IsClusters s.active)
    (hc : s.active.card = m + 2) :
    Run s ((stepWith tb)^[m] s) ∧ ((stepWith tb)^[m] s).active.card = 2 ∧
      ((stepWith tb)^[m] s).ops = s.ops + ∑ i ∈ range m, joinOps (i + 3) := by
  induction m generalizing s with
  | zero => exact ⟨Run.done s, hc, by simp⟩
  | succ m ih =>
    have h2 : 2 ≤ s.active.card := by omega
    have hq := isQMin_pick tb s h2
    have hA := hq.1
    have hB := hq.2.1
    have hAB := hq.2.2.1
    have hP' : IsClusters (stepWith tb s).active := hP.join hA hB
    have hc' : (stepWith tb s).active.card = m + 2 := by
      have := hP.card_join hA hB hAB
      change (insert _ _ : Finset _).card = _
      omega
    obtain ⟨h1, h3, h4⟩ := ih (stepWith tb s) hP' hc'
    rw [Function.iterate_succ_apply]
    refine ⟨Run.step (by omega) hq h1, h3, ?_⟩
    rw [h4, sum_range_succ]
    have h5 : (stepWith tb s).ops = s.ops + joinOps (m + 3) := by
      change s.ops + s.joinCost _ _ = _
      rw [joinCost_eq rfl hA hB hAB, hc]
    rw [h5]
    ring

/-- The run of the method is a run. -/
theorem run_spec (tb : TieBreak X) (d : X → X → ℝ) :
    Run (init d) (run tb d) ∧ (run tb d).active.card ≤ 2 := by
  by_cases hX : 2 ≤ Fintype.card X
  · obtain ⟨h1, h2, -⟩ := iterate_stepWith tb (Fintype.card X - 2) (init d) (isClusters_init d)
      (by rw [card_init]; omega)
    exact ⟨h1, h2.le⟩
  · have h0 : Fintype.card X - 2 = 0 := by omega
    simp only [run, h0, Function.iterate_zero, id]
    exact ⟨Run.done _, by rw [card_init]; omega⟩

/-- **Neighbor joining is exact**, whichever way ties are broken: on the metric of a tree `T` with positive
weights, with polytomies or not, it returns a tree refining `T`, with the same weights on the edges of `T` and
weight zero on the others. -/
theorem nj_spec (tb : TieBreak X) {T : Finset (Finset X)} {w : Finset X → ℝ} (hT : IsUnrootedTree T)
    (hw : ∀ A ∈ T, 0 < w A ∧ w Aᶜ = w A) :
    IsUnrootedTree (nj tb (treeMetric T w)).1 ∧ T ⊆ (nj tb (treeMetric T w)).1 ∧
      (∀ A ∈ T, (nj tb (treeMetric T w)).2 A = w A) ∧
      ∀ A ∈ (nj tb (treeMetric T w)).1, A ∉ T → (nj tb (treeMetric T w)).2 A = 0 :=
  (run_spec tb _).1.output_spec hT hw (run_spec tb _).2

/-- **The output of neighbor joining is a binary tree**, on any input, whichever way ties are broken. -/
theorem isBinaryTree_nj [Nonempty X] (tb : TieBreak X) (d : X → X → ℝ) : IsBinaryTree (nj tb d).1 :=
  (run_spec tb d).1.isBinaryTree (run_spec tb d).2

/-- **Neighbor joining is an exact tree builder**, whichever way ties are broken. -/
theorem isExactBuilder_nj (tb : TieBreak X) : IsExactBuilder (nj tb) := fun _ _ hT hw =>
  let ⟨h1, h2, h3, h4⟩ := nj_spec tb hT hw
  ⟨h1, h2, h3, fun A hA hnA => (h4 A hA hnA).le⟩

/-! ### The number of operations -/

/-- The number of elementary operations of neighbor joining on `N` taxa: reading the input, the joins from
`n = N` down to `n = 3` active nodes (`joinOps`, `State.joinCost`), and the row sums for the last edge. -/
def njOps (N : ℕ) : ℕ :=
  N * N + ∑ i ∈ range (N - 2), joinOps (i + 3) + min N 2 * min N 2

/-- The operations counted along the run of the method, on any input. -/
theorem ops_run (tb : TieBreak X) (d : X → X → ℝ) :
    (run tb d).ops + (run tb d).outputCost = njOps (Fintype.card X) := by
  by_cases hX : 2 ≤ Fintype.card X
  · obtain ⟨-, h2, h3⟩ := iterate_stepWith tb (Fintype.card X - 2) (init d) (isClusters_init d)
      (by rw [card_init]; omega)
    have hmin : min (Fintype.card X) 2 = 2 := min_eq_right hX
    rw [State.outputCost, sum_const, smul_eq_mul, run, h2, h3, njOps, hmin]
    rfl
  · have h0 : Fintype.card X - 2 = 0 := by omega
    have hmin : min (Fintype.card X) 2 = Fintype.card X := min_eq_left (by omega)
    simp only [run, h0, Function.iterate_zero, id, State.outputCost, sum_const, smul_eq_mul, njOps, hmin,
      card_init, range_zero, sum_empty, add_zero]
    rfl

/-- A join with `n` active nodes takes at most `7 n²` operations. -/
theorem joinOps_le {n : ℕ} (hn : 3 ≤ n) : joinOps n ≤ 7 * (n * n) := by
  have h1 : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
  rw [joinOps]
  generalize n * n = q at *
  omega

/-- **The `O(N³)` of neighbor joining** (Studier and Keppler 1988): the number of
operations is at most `8 N³`. -/
theorem njOps_le (N : ℕ) : njOps N ≤ 8 * N ^ 3 := by
  have hsum : ∑ i ∈ range (N - 2), joinOps (i + 3) ≤ (N - 2) * (7 * (N * N)) := by
    calc ∑ i ∈ range (N - 2), joinOps (i + 3)
        ≤ ∑ _i ∈ range (N - 2), 7 * (N * N) := by
          refine sum_le_sum fun i hi => ?_
          have hi' : i + 3 ≤ N := by
            have := mem_range.1 hi
            omega
          exact (joinOps_le (by omega)).trans
            (Nat.mul_le_mul_left 7 (Nat.mul_le_mul hi' hi'))
      _ = (N - 2) * (7 * (N * N)) := by simp
  have hle : (N - 2) * (7 * (N * N)) ≤ 7 * N ^ 3 := by
    calc (N - 2) * (7 * (N * N)) ≤ N * (7 * (N * N)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 7 * N ^ 3 := by ring
  rw [njOps]
  rcases N with _ | _ | N
  · simp
  · simp
  · have hmin : min (N + 1 + 1) 2 = 2 := by omega
    have h4 : (N + 1 + 1) * (N + 1 + 1) + 2 * 2 ≤ (N + 1 + 1) ^ 3 := by nlinarith [sq_nonneg N, Nat.zero_le N]
    rw [hmin]
    omega

/-- **The `O(N³)` of neighbor joining**, on the instrumented run: at most `8 N³` operations, on any input and with any
tie-break. -/
theorem ops_run_le (tb : TieBreak X) (d : X → X → ℝ) :
    (run tb d).ops + (run tb d).outputCost ≤ 8 * Fintype.card X ^ 3 := by
  rw [ops_run]
  exact njOps_le _

end Phylogenetics.NJ
