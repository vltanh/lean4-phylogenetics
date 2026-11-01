module

public import Phylogenetics.NMSC.Level1.Symmetry
public import Mathlib.Data.Fin.Tuple.Sort
/-!
# The quartet CFs of a displayed tree of a cycle

Once the lineage of the hybrid component has chosen a side, the cycle acts as a tree: a path
`0 — 1 — ⋯ — d` with the components hanging from its nodes, rooted at its top node, which lies at
the node `p + 1` (if the root of the network is not the top node of the cycle; the component of
the root hangs there) or inside the edge between `p` and `p + 1`. The two *arms* of the path are
`0, …, p` (going up from `0`) and `d, d - 1, …, d - q` (going up from `d`). Each of the lineages
`0, 1, 2, 3` sits at a position `pos l`; the lineages at the positions of an arm enter it there.

`Phylogenetics.displayed_score` computes the expected score `Phylogenetics.quartetScore` of the
forest at the top node: it is the quartet CF `Phylogenetics.pathCF` of the quartet tree that the
four positions induce on the path. The proof locates the node where the third lineage joins,
applies `Phylogenetics.NiceKernel.score` there, and computes the coalescence of the pairs before
it.

The arm processes: `Phylogenetics.armDist μ₀ nodes`, where `μ₀` is the distribution of the forest
entering the lowest node from below and `nodes`, listed from the bottom, gives for each node the
distribution of the forest that joins there and the length of the edge above the node.

## Proof

Each arm is rewritten as a recursion over the heights of its nodes (the right arm with the
heights `d - pos l`), and its part above a node as a product of kernels. With the lineages sorted
by position (`Tuple.sort`), at positions `a₁ < a₂ < a₃ < a₄`: where no lineage enters, an arm is
Kingman's coalescent for the total length of its edges; a single lineage does not change; two
lineages reach the node of the upper one as two roots, which merge with probability `1 - e^{-T}`.
If three lineages enter one arm, the process after the node of the third one is a nice kernel;
otherwise each arm carries at most two lineages to the top node. Either way the expected score is
`e^{-t}/3 + (1 - e^{-t}) s`, where `t = pathLen W a₂ a₃` and `s` is `1` if the two lowest lineages
form `{0, 1}` or `{2, 3}` and `0` otherwise; this is `pathCF`.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

/-- The forest at the top of an arm. The forest with distribution `μ₀` arrives at the lowest node;
at each node (listed from the bottom) an independent forest with distribution `n.1` joins, and the
lineages then travel along the edge above the node, of length `n.2`. -/
def armDist (μ₀ : Finset (Finset (Fin 4)) → ℝ)
    (nodes : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)) : Finset (Finset (Fin 4)) → ℝ :=
  nodes.foldl (fun μ n => forestUnion μ n.1 ᵥ* kingmanTransition n.2) μ₀

/-- The forest of the singletons of the lineages at position `j`. -/
def posForest (pos : Fin 4 → ℕ) (j : ℕ) : Finset (Finset (Fin 4)) :=
  (univ.filter fun l => pos l = j).image fun l => {l}

/-- The left arm `0, 1, …, p` of the path: the lineages at position `0` enter at the bottom and
travel along the edge above position `0`; the node at position `h` (`1 ≤ h ≤ p`) receives the
lineages at position `h`. The edge above position `h` has length `W h` for `h < p`; the edge above
position `p`, to the top node, has length `tL`. -/
def leftArm (p : ℕ) (W : ℕ → ℝ) (tL : ℝ) (pos : Fin 4 → ℕ) : Finset (Finset (Fin 4)) → ℝ :=
  armDist (Pi.single (posForest pos 0) 1 ᵥ* kingmanTransition (if p = 0 then tL else W 0))
    ((List.range p).map fun i =>
      (Pi.single (posForest pos (i + 1)) 1, if i + 1 = p then tL else W (i + 1)))

/-- The right arm `d, d - 1, …, d - q` of the path: the lineages at position `d` enter at the
bottom and travel along the edge above position `d`; the node at height `h` (`1 ≤ h ≤ q`), at
position `d - h`, receives the lineages at that position. The edge above position `d - h` (towards
position `d - h - 1`) has length `W (d - h - 1)` for `h < q`; the edge above position `d - q`, to
the top node, has length `tR`. -/
def rightArm (d q : ℕ) (W : ℕ → ℝ) (tR : ℝ) (pos : Fin 4 → ℕ) : Finset (Finset (Fin 4)) → ℝ :=
  armDist (Pi.single (posForest pos d) 1 ᵥ* kingmanTransition (if q = 0 then tR else W (d - 1)))
    ((List.range q).map fun i =>
      (Pi.single (posForest pos (d - (i + 1))) 1, if i + 1 = q then tR else W (d - (i + 1) - 1)))

/-! ### Arms, node by node -/

/-- An arm whose node at height `h` receives the lineages `l` with `f l = h`, and whose edge above
height `h` has length `e h`: the distribution of the forest at the top of the edge above height
`n - 1` (the empty forest for `n = 0`). -/
private def na_arm (f : Fin 4 → ℕ) (e : ℕ → ℝ) : ℕ → Finset (Finset (Fin 4)) → ℝ
  | 0 => Pi.single ∅ 1
  | n + 1 => forestUnion (na_arm f e n) (Pi.single (posForest f n) 1) ᵥ* kingmanTransition (e n)

/-- The kernel of the node at height `h` and of the edge above it. -/
private def na_step (f : Fin 4 → ℕ) (e : ℕ → ℝ) (h : ℕ) :
    Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ :=
  unionKernel (Pi.single (posForest f h) 1) * kingmanTransition (e h)

/-- The kernel of the nodes at heights `m, …, m + k - 1` and of the edges above them. -/
private def na_seg (f : Fin 4 → ℕ) (e : ℕ → ℝ) (m : ℕ) :
    ℕ → Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ
  | 0 => 1
  | k + 1 => na_seg f e m k * na_step f e (m + k)

/-- The edge lengths of the left arm, by height. -/
private def na_eL (p : ℕ) (W : ℕ → ℝ) (tL : ℝ) (h : ℕ) : ℝ := if h = p then tL else W h

/-- The edge lengths of the right arm, by height (the node at height `h` is at position
`d - h`). -/
private def na_eR (d q : ℕ) (W : ℕ → ℝ) (tR : ℝ) (h : ℕ) : ℝ :=
  if h = q then tR else W (d - h - 1)

private theorem na_armDist_append (μ₀ : Finset (Finset (Fin 4)) → ℝ)
    (l : List ((Finset (Finset (Fin 4)) → ℝ) × ℝ)) (x : (Finset (Finset (Fin 4)) → ℝ) × ℝ) :
    armDist μ₀ (l ++ [x]) = forestUnion (armDist μ₀ l) x.1 ᵥ* kingmanTransition x.2 := by
  simp only [armDist, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem na_arm_one_step (f : Fin 4 → ℕ) (e : ℕ → ℝ) :
    na_arm f e 1 = Pi.single (posForest f 0) 1 ᵥ* kingmanTransition (e 0) := by
  show forestUnion (Pi.single ∅ 1) _ ᵥ* _ = _
  rw [forestUnion_single_single, empty_union]

/-- The left arm, node by node. -/
private theorem na_leftArm_eq (p : ℕ) (W : ℕ → ℝ) (tL : ℝ) (pos : Fin 4 → ℕ) :
    leftArm p W tL pos = na_arm pos (na_eL p W tL) (p + 1) := by
  have key : ∀ k, armDist (Pi.single (posForest pos 0) 1 ᵥ*
      kingmanTransition (if p = 0 then tL else W 0)) ((List.range k).map fun i =>
        (Pi.single (posForest pos (i + 1)) 1, if i + 1 = p then tL else W (i + 1))) =
      na_arm pos (na_eL p W tL) (k + 1) := by
    intro k
    induction k with
    | zero =>
      rw [na_arm_one_step, na_eL]
      simp only [List.range_zero, List.map_nil, armDist, List.foldl_nil]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp
      · simp [hp.ne', hp.ne]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, na_armDist_append, ih]
      rfl
  exact key p

/-- The right arm, node by node, by height: the node at height `h` is at position `d - h`. -/
private theorem na_rightArm_eq {d q : ℕ} (W : ℕ → ℝ) (tR : ℝ) {pos : Fin 4 → ℕ}
    (hle : ∀ l, pos l ≤ d) (hqd : q < d) :
    rightArm d q W tR pos = na_arm (fun l => d - pos l) (na_eR d q W tR) (q + 1) := by
  have hpf : ∀ h ≤ d, posForest pos (d - h) = posForest (fun l => d - pos l) h := by
    intro h hh
    unfold posForest
    congr 1
    ext l
    simp only [mem_filter, mem_univ, true_and]
    have := hle l
    omega
  have key : ∀ k ≤ q, armDist (Pi.single (posForest pos d) 1 ᵥ*
      kingmanTransition (if q = 0 then tR else W (d - 1))) ((List.range k).map fun i =>
        (Pi.single (posForest pos (d - (i + 1))) 1,
          if i + 1 = q then tR else W (d - (i + 1) - 1))) =
      na_arm (fun l => d - pos l) (na_eR d q W tR) (k + 1) := by
    intro k hk
    induction k with
    | zero =>
      rw [na_arm_one_step, na_eR, ← hpf 0 (Nat.zero_le _), Nat.sub_zero]
      simp only [List.range_zero, List.map_nil, armDist, List.foldl_nil]
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · simp [hq.ne', hq.ne]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, na_armDist_append,
        ih (by omega), hpf (k + 1) (by omega)]
      rfl
  exact key q le_rfl

/-! ### Small facts about forests and kernels -/

private theorem na_single_vecMul_apply (F : Finset (Finset (Fin 4)))
    (Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (G : Finset (Finset (Fin 4))) :
    (Pi.single F 1 ᵥ* Φ) G = Φ F G := by
  rw [single_one_vecMul]
  rfl

private theorem na_kingmanTransition_zero :
    (kingmanTransition 0 : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ) = 1 := by
  rw [kingmanTransition_zero]

/-- The forest of the singletons of a set of lineages. -/
private abbrev na_sing (T : Finset (Fin 4)) : Finset (Finset (Fin 4)) := T.image fun l => {l}

private theorem na_roots_sing (T : Finset (Fin 4)) : roots (na_sing T) = na_sing T := by
  refine subset_antisymm (roots_subset _) fun A hA =>
    mem_roots.2 ⟨hA, fun B hB hAB => ?_⟩
  obtain ⟨l, -, rfl⟩ := mem_image.1 hA
  obtain ⟨m, -, rfl⟩ := mem_image.1 hB
  rw [singleton_subset_singleton.1 hAB]

private theorem na_sing_union (T T' : Finset (Fin 4)) :
    na_sing T ∪ na_sing T' = na_sing (T ∪ T') :=
  (image_union _ _).symm

private theorem na_sing_pair (i j : Fin 4) : na_sing {i, j} = {{i}, {j}} := by
  simp only [na_sing, image_insert, image_singleton]

private theorem na_card_mem_sing {T : Finset (Fin 4)} {D : Finset (Fin 4)} (hD : D ∈ na_sing T) :
    #D = 1 := by
  obtain ⟨l, -, rfl⟩ := mem_image.1 hD
  exact card_singleton l

/-- A good forest with at most one root does not change. -/
private theorem na_vecMul_K_sing {T : Finset (Fin 4)} (hT : #T ≤ 1) (t : ℝ) :
    Pi.single (na_sing T) 1 ᵥ* kingmanTransition t = Pi.single (na_sing T) 1 := by
  refine single_vecMul_kingmanTransition (isGoodForest_singletons T).1 ?_ t
  rw [na_roots_sing]
  exact card_image_le.trans hT

private theorem na_posForest_eq_sing (f : Fin 4 → ℕ) (h : ℕ) :
    posForest f h = na_sing (univ.filter fun l => f l = h) := rfl

private theorem na_posForest_eq_empty {f : Fin 4 → ℕ} {h : ℕ} (hf : ∀ l, f l ≠ h) :
    posForest f h = ∅ := by
  unfold posForest
  rw [image_eq_empty, filter_eq_empty_iff]
  exact fun l _ => hf l

private theorem na_posForest_eq_single {f : Fin 4 → ℕ} {i : Fin 4} (hf : ∀ l, f l = f i → l = i) :
    posForest f (f i) = na_sing {i} := by
  rw [na_posForest_eq_sing]
  congr 1
  ext l
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨hf l, fun h => h ▸ rfl⟩

/-- Merging the two roots of a good forest gives a good forest on the same lineages. -/
private theorem na_isGood_merge {F : Finset (Finset (Fin 4))} (hF : IsGoodForest F) {A B : Finset (Fin 4)}
    (hA : A ∈ roots F) (hB : B ∈ roots F) (hAB : A ≠ B) :
    IsGoodForest (insert (A ∪ B) F) ∧ lineages (insert (A ∪ B) F) = lineages F :=
  ⟨⟨hF.1.isForest_merge hA hB, isBinaryForest_merge hF.1 hF.2
    (mem_merges.2 ⟨A, hA, B, hB, hAB, rfl⟩)⟩, lineages_merge hA hB⟩

/-! ### Arms, node by node: the recursions -/

private theorem na_arm_succ (f : Fin 4 → ℕ) (e : ℕ → ℝ) (n : ℕ) :
    na_arm f e (n + 1) = na_arm f e n ᵥ* na_step f e n := by
  rw [na_step, ← vecMul_vecMul, ← forestUnion_eq_vecMul]
  rfl

private theorem na_arm_add (f : Fin 4 → ℕ) (e : ℕ → ℝ) (m k : ℕ) :
    na_arm f e (m + k) = na_arm f e m ᵥ* na_seg f e m k := by
  induction k with
  | zero => rw [Nat.add_zero, na_seg, vecMul_one]
  | succ k ih => rw [← Nat.add_assoc, na_arm_succ, ih, na_seg, vecMul_vecMul]

/-- Where no lineage enters, the arm is one edge (Kingman's coalescent for the total length). -/
private theorem na_arm_noentry (f : Fin 4 → ℕ) (e : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n)
    (hf : ∀ l, f l < n → f l < m) :
    na_arm f e n = na_arm f e m ᵥ* kingmanTransition (∑ h ∈ Ico m n, e h) := by
  induction n, hmn using Nat.le_induction with
  | base => rw [Ico_self, sum_empty, na_kingmanTransition_zero, vecMul_one]
  | succ n hmn ih =>
    have hn : posForest f n = ∅ := na_posForest_eq_empty fun l hl => by
      have := hf l (by omega)
      omega
    rw [sum_Ico_succ_top hmn, ← kingmanTransition_add_vecMul, ← ih fun l hl => hf l (by omega)]
    show forestUnion (na_arm f e n) (Pi.single (posForest f n) 1) ᵥ* _ = _
    rw [hn, forestUnion_single_empty]

/-- An arm that no lineage has entered carries the empty forest. -/
private theorem na_arm_empty (f : Fin 4 → ℕ) (e : ℕ → ℝ) {n : ℕ} (hf : ∀ l, n ≤ f l) :
    na_arm f e n = Pi.single ∅ 1 := by
  rw [na_arm_noentry f e (Nat.zero_le n) fun l hl => absurd (hf l) (by omega)]
  exact na_vecMul_K_sing (T := ∅) (by simp) _

/-- An arm carrying one lineage carries it unchanged. -/
private theorem na_arm_one (f : Fin 4 → ℕ) (e : ℕ → ℝ) {n : ℕ} {i : Fin 4} (hin : f i < n)
    (hf : ∀ l, f l < n → l = i) :
    na_arm f e n = Pi.single (na_sing {i}) 1 := by
  have h0 : na_arm f e (f i) = Pi.single ∅ 1 := na_arm_empty f e fun l => by
    by_contra h
    exact absurd (hf l (by omega)) (by rintro rfl; omega)
  have h1 : na_arm f e (f i + 1) = Pi.single (na_sing {i}) 1 := by
    show forestUnion (na_arm f e (f i)) (Pi.single (posForest f (f i)) 1) ᵥ* _ = _
    rw [h0, na_posForest_eq_single fun l hl => hf l (by omega), forestUnion_single_single,
      empty_union]
    exact na_vecMul_K_sing (by simp) _
  rw [na_arm_noentry f e (show f i + 1 ≤ n by omega) fun l hl => by
      rw [hf l hl]; omega, h1]
  exact na_vecMul_K_sing (by simp) _

/-- An arm carrying two lineages: they arrive at the node of the upper one as two roots, which
then travel together to the top. -/
private theorem na_arm_two (f : Fin 4 → ℕ) (e : ℕ → ℝ) {n : ℕ} {i j : Fin 4} (hij : f i < f j)
    (hjn : f j < n) (hf : ∀ l, f l < n → l = i ∨ l = j) :
    na_arm f e n = Pi.single (na_sing {i, j}) 1 ᵥ* kingmanTransition (∑ h ∈ Ico (f j) n, e h) := by
  have h0 : na_arm f e (f j) = Pi.single (na_sing {i}) 1 := na_arm_one f e hij fun l hl => by
    rcases hf l (by omega) with rfl | rfl
    · rfl
    · omega
  have h1 : na_arm f e (f j + 1) =
      Pi.single (na_sing {i, j}) 1 ᵥ* kingmanTransition (e (f j)) := by
    show forestUnion (na_arm f e (f j)) (Pi.single (posForest f (f j)) 1) ᵥ* _ = _
    rw [h0, na_posForest_eq_single fun l hl => ?_, forestUnion_single_single, na_sing_union]
    · rfl
    · rcases hf l (by omega) with rfl | rfl
      · omega
      · rfl
  rw [na_arm_noentry f e (show f j + 1 ≤ n by omega) fun l hl => by
      rcases hf l hl with rfl | rfl <;> omega, h1, kingmanTransition_add_vecMul,
    ← sum_eq_sum_Ico_succ_bot hjn]

/-- The two-lineage arm as a mixture: the two lineages have not coalesced with probability
`e^{-T}`. -/
private theorem na_arm_two_mix (f : Fin 4 → ℕ) (e : ℕ → ℝ) {n : ℕ} {i j : Fin 4}
    (hij : f i < f j) (hjn : f j < n) (hf : ∀ l, f l < n → l = i ∨ l = j) :
    na_arm f e n = Real.exp (-∑ h ∈ Ico (f j) n, e h) • Pi.single (na_sing {i, j}) 1 +
      (1 - Real.exp (-∑ h ∈ Ico (f j) n, e h)) •
        Pi.single (insert {i, j} (na_sing {i, j})) 1 := by
  have hne : i ≠ j := by rintro rfl; omega
  rw [na_arm_two f e hij hjn hf, single_vecMul_kingmanTransition_two (isGoodForest_singletons _).1
    (A := {i}) (B := {j}) (by simpa using hne) (by rw [na_roots_sing, na_sing_pair]),
    ← insert_eq]

/-! ### The arms are nice kernels -/

private theorem na_nice_single (X : Finset (Fin 4)) :
    NiceKernel X (unionKernel (Pi.single (na_sing X) 1)) := by
  refine niceKernel_unionKernel ?_ fun E hE => ?_
  · rw [sum_pi_single']
    exact ite_eq_left (mem_univ _)
  · obtain rfl : E = na_sing X := by
      by_contra h
      exact hE (Pi.single_eq_of_ne h 1)
    exact ⟨isGoodForest_singletons X, lineages_image_singleton X⟩

private theorem na_nice_step (f : Fin 4 → ℕ) (e : ℕ → ℝ) (h : ℕ) :
    NiceKernel (univ.filter fun l => f l = h) (na_step f e h) := by
  have := (na_nice_single (univ.filter fun l => f l = h)).mul
    (niceKernel_kingmanTransition (e h)) (disjoint_empty_right _)
  rw [union_empty] at this
  exact this

private theorem na_nice_seg (f : Fin 4 → ℕ) (e : ℕ → ℝ) (m k : ℕ) :
    NiceKernel (univ.filter fun l => m ≤ f l ∧ f l < m + k) (na_seg f e m k) := by
  induction k with
  | zero =>
    have h : (univ.filter fun l => m ≤ f l ∧ f l < m + 0) = ∅ :=
      filter_eq_empty_iff.2 fun l _ => by omega
    rw [h]
    exact niceKernel_one
  | succ k ih =>
    have h := ih.mul (na_nice_step f e (m + k)) (disjoint_left.2 fun l hl hl' => by
      simp only [mem_filter, mem_univ, true_and] at hl hl'
      omega)
    have hS : ((univ.filter fun l => m ≤ f l ∧ f l < m + k) ∪
        univ.filter fun l => f l = m + k) = univ.filter fun l => m ≤ f l ∧ f l < m + (k + 1) := by
      ext l
      simp only [mem_union, mem_filter, mem_univ, true_and]
      omega
    rw [hS] at h
    exact h

/-- The forest at the top of an arm is a random good forest of the lineages of the arm. -/
private theorem na_arm_dist (f : Fin 4 → ℕ) (e : ℕ → ℝ) (n : ℕ) :
    ∑ G, na_arm f e n G = 1 ∧ ∀ G, na_arm f e n G ≠ 0 →
      IsGoodForest G ∧ lineages G = univ.filter fun l => f l < n := by
  have hN := na_nice_seg f e 0 n
  have hS : (univ.filter fun l => 0 ≤ f l ∧ f l < 0 + n) = univ.filter fun l => f l < n := by
    ext l
    simp
  rw [hS] at hN
  have h0 : Disjoint (lineages (∅ : Finset (Finset (Fin 4))))
      (univ.filter fun l => f l < n) := by
    rw [lineages_empty]
    exact disjoint_empty_left _
  have harm : na_arm f e n = Pi.single ∅ 1 ᵥ* na_seg f e 0 n := by
    have := na_arm_add f e 0 n
    rwa [Nat.zero_add] at this
  simp only [harm, na_single_vecMul_apply]
  refine ⟨hN.sum_eq_one ∅ isGoodForest_empty h0, fun G hG => ?_⟩
  obtain ⟨hGg, -, hGl⟩ := hN.support ∅ isGoodForest_empty h0 G hG
  rw [lineages_empty, empty_union] at hGl
  exact ⟨hGg, hGl⟩

/-! ### Expected scores -/

/-- The expected score of a random forest. -/
private def na_ES (μ : Finset (Finset (Fin 4)) → ℝ) : ℝ := ∑ G, μ G * quartetScore G

private theorem na_ES_add (μ ν : Finset (Finset (Fin 4)) → ℝ) :
    na_ES (μ + ν) = na_ES μ + na_ES ν := by
  simp only [na_ES, Pi.add_apply, add_mul, sum_add_distrib]

private theorem na_ES_smul (c : ℝ) (μ : Finset (Finset (Fin 4)) → ℝ) :
    na_ES (c • μ) = c * na_ES μ := by
  simp only [na_ES, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

private theorem na_ES_single (F : Finset (Finset (Fin 4))) :
    na_ES (Pi.single F 1) = quartetScore F := by
  simp [na_ES, Pi.single_apply]

/-- After a nice kernel, the expected score of a good forest of at least three lineages is its
score. -/
private theorem na_ES_nice {S : Finset (Fin 4)}
    {Φ : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ} (hΦ : NiceKernel S Φ)
    {F : Finset (Finset (Fin 4))} (hF : IsGoodForest F) (hFS : Disjoint (lineages F) S)
    (h3 : 3 ≤ #(lineages F)) : na_ES (Pi.single F 1 ᵥ* Φ) = quartetScore F := by
  simp only [na_ES, na_single_vecMul_apply]
  exact hΦ.score hF hFS h3

/-- The score of a forest whose only cluster of two lineages is `C` or its complement. -/
private def na_pairScore (C : Finset (Fin 4)) : ℝ := if C = {0, 1} ∨ C = {2, 3} then 1 else 0

private theorem na_compl01 : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide

private theorem na_compl23 : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide

private theorem na_pairScore_compl (C : Finset (Fin 4)) : na_pairScore Cᶜ = na_pairScore C := by
  have e1 : Cᶜ = {0, 1} ↔ C = {2, 3} := by rw [compl_eq_comm, na_compl01, eq_comm]
  have e2 : Cᶜ = {2, 3} ↔ C = {0, 1} := by rw [compl_eq_comm, na_compl23, eq_comm]
  unfold na_pairScore
  by_cases h : C = {0, 1} ∨ C = {2, 3}
  · rw [ite_eq_left h, ite_eq_left (by rw [e1, e2]; tauto)]
  · rw [ite_eq_right h, ite_eq_right (by rw [e1, e2]; tauto)]

/-- A forest of singletons has score `1/3`. -/
private theorem na_score_sing {F : Finset (Finset (Fin 4))} (hF : ∀ D ∈ F, #D = 1) :
    quartetScore F = 1 / 3 := by
  have h2 : ¬ ∃ C ∈ F, #C = 2 := by
    rintro ⟨C, hC, h2⟩
    have := hF C hC
    omega
  have h1 : ¬ (({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F) := by
    rintro (h | h)
    · exact absurd (hF _ h) (by decide)
    · exact absurd (hF _ h) (by decide)
  unfold quartetScore
  rw [ite_eq_right h1, ite_eq_right h2]

/-- A forest whose clusters are singletons, `C` and `Cᶜ`, with `C` or `Cᶜ` present. -/
private theorem na_score_pair {F : Finset (Finset (Fin 4))} {C : Finset (Fin 4)} (hC : #C = 2)
    (hF : ∀ D ∈ F, #D = 1 ∨ D = C ∨ D = Cᶜ) (hmem : C ∈ F ∨ Cᶜ ∈ F) :
    quartetScore F = na_pairScore C := by
  unfold quartetScore na_pairScore
  by_cases h : C = {0, 1} ∨ C = {2, 3}
  · rw [ite_eq_left h]
    refine ite_eq_left ?_
    rcases h with rfl | rfl <;> rcases hmem with hm | hm
    · exact Or.inl hm
    · exact Or.inr (na_compl01 ▸ hm)
    · exact Or.inr hm
    · exact Or.inl (na_compl23 ▸ hm)
  · rw [ite_eq_right h]
    have hn : ¬ (({0, 1} : Finset (Fin 4)) ∈ F ∨ ({2, 3} : Finset (Fin 4)) ∈ F) := by
      rintro (hm | hm)
      · rcases hF _ hm with h1 | h1 | h1
        · exact absurd h1 (by decide)
        · exact h (Or.inl h1.symm)
        · exact h (Or.inr (by rw [← compl_compl C, ← h1, na_compl01]))
      · rcases hF _ hm with h1 | h1 | h1
        · exact absurd h1 (by decide)
        · exact h (Or.inr h1.symm)
        · exact h (Or.inl (by rw [← compl_compl C, ← h1, na_compl23]))
    rw [ite_eq_right hn]
    refine ite_eq_left ?_
    rcases hmem with hm | hm
    · exact ⟨C, hm, hC⟩
    · exact ⟨Cᶜ, hm, by rw [card_compl, hC]; rfl⟩

/-! ### The forests where two lineages may have coalesced -/

private theorem na_single_vecMul_unionKernel (F E : Finset (Finset (Fin 4))) :
    Pi.single F 1 ᵥ* unionKernel (Pi.single E 1) = Pi.single (F ∪ E) 1 := by
  rw [← forestUnion_eq_vecMul, forestUnion_single_single]

/-- The forest of the singletons of `i ≠ j` with their cluster `{i, j}` is good. -/
private theorem na_merged_good {i j : Fin 4} (hij : i ≠ j) :
    IsGoodForest (insert {i, j} (na_sing {i, j})) ∧
      lineages (insert {i, j} (na_sing {i, j})) = {i, j} := by
  have hr : roots (na_sing {i, j}) = {{i}, {j}} := by rw [na_roots_sing, na_sing_pair]
  have h := na_isGood_merge (isGoodForest_singletons {i, j}) (A := {i}) (B := {j})
    (by rw [hr]; exact mem_insert_self _ _)
    (by rw [hr]; exact mem_insert_of_mem (mem_singleton_self _))
    (by simpa using hij)
  rw [← insert_eq, lineages_image_singleton] at h
  exact h

/-- The score of the forest of singletons with the cluster `{i, j}`. -/
private theorem na_score_merged {i j : Fin 4} (hij : i ≠ j) (T : Finset (Fin 4)) :
    quartetScore (insert {i, j} (na_sing {i, j}) ∪ na_sing T) = na_pairScore {i, j} := by
  refine na_score_pair (card_pair hij) (fun D hD => ?_) (Or.inl (mem_union_left _
    (mem_insert_self _ _)))
  rcases mem_union.1 hD with hD | hD
  · rcases mem_insert.1 hD with rfl | hD
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (na_card_mem_sing hD)
  · exact Or.inl (na_card_mem_sing hD)

/-- The two-lineage mixture, after adding the singleton of a third lineage. -/
private theorem na_mix_union {T : ℝ} {i j k : Fin 4} :
    (Real.exp (-T) • Pi.single (na_sing {i, j}) 1 +
      (1 - Real.exp (-T)) • Pi.single (insert {i, j} (na_sing {i, j})) 1) ᵥ*
        unionKernel (Pi.single (na_sing {k}) 1) =
      Real.exp (-T) • Pi.single (na_sing ({i, j} ∪ {k})) 1 +
        (1 - Real.exp (-T)) • Pi.single (insert {i, j} (na_sing {i, j}) ∪ na_sing {k}) 1 := by
  rw [add_vecMul, smul_vecMul, smul_vecMul, na_single_vecMul_unionKernel,
    na_single_vecMul_unionKernel, na_sing_union]

/-- Three distinct lineages. -/
private theorem na_card_three {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    #(({i, j} ∪ {k}) : Finset (Fin 4)) = 3 := by
  rw [card_union_of_disjoint (disjoint_singleton_right.2 (by simp [hik.symm, hjk.symm])),
    card_pair hij, card_singleton]

/-- **The third lineage joins an arm.** If the lineages `i, j, k` enter an arm in this order, below
all the other lineages (of the arm, and those `S'` of the other arm, whose forest has distribution
`ν`), then the expected score at the top is that of the forest just after `k` enters: `i` and `j`
have coalesced or not, and then the process is a nice kernel. -/
private theorem na_score_P (f : Fin 4 → ℕ) (e : ℕ → ℝ) {n : ℕ} {ν : Finset (Finset (Fin 4)) → ℝ}
    {S' : Finset (Fin 4)} (hν1 : ∑ E, ν E = 1)
    (hν2 : ∀ E, ν E ≠ 0 → IsGoodForest E ∧ lineages E = S') (hS' : ∀ l ∈ S', n ≤ f l)
    {i j k : Fin 4} (hij : f i < f j) (hjk : f j < f k) (hkn : f k < n)
    (hf : ∀ l, f l ≤ f k → l = i ∨ l = j ∨ l = k) :
    na_ES (forestUnion (na_arm f e n) ν) =
      Real.exp (-∑ h ∈ Ico (f j) (f k), e h) * (1 / 3) +
        (1 - Real.exp (-∑ h ∈ Ico (f j) (f k), e h)) * na_pairScore {i, j} := by
  have hij' : i ≠ j := by rintro rfl; omega
  have hik' : i ≠ k := by rintro rfl; omega
  have hjk' : j ≠ k := by rintro rfl; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = f k + 1 + m := ⟨n - (f k + 1), by omega⟩
  -- the process after `k` has entered is a nice kernel
  set S := (∅ ∪ univ.filter fun l => f k + 1 ≤ f l ∧ f l < f k + 1 + m) ∪ S'
  have hΦ : NiceKernel S (kingmanTransition (e (f k)) * na_seg f e (f k + 1) m * unionKernel ν) :=
    ((niceKernel_kingmanTransition _).mul (na_nice_seg f e _ _) (disjoint_empty_left _)).mul
      (niceKernel_unionKernel hν1 hν2) (disjoint_left.2 fun l hl hl' => by
        simp only [empty_union, mem_filter, mem_univ, true_and] at hl
        have := hS' l hl'
        omega)
  have hlow : Disjoint (({i, j} ∪ {k}) : Finset (Fin 4)) S := disjoint_left.2 fun l hl hl' => by
    have hl1 : f l ≤ f k := by
      simp only [mem_union, mem_insert, mem_singleton] at hl
      rcases hl with (rfl | rfl) | rfl <;> omega
    rcases mem_union.1 hl' with hl' | hl'
    · simp only [empty_union, mem_filter, mem_univ, true_and] at hl'
      omega
    · have := hS' l hl'
      omega
  -- the forest just after `k` has entered
  have hP : forestUnion (na_arm f e (f k + 1 + m)) ν =
      (na_arm f e (f k) ᵥ* unionKernel (Pi.single (posForest f (f k)) 1)) ᵥ*
        (kingmanTransition (e (f k)) * na_seg f e (f k + 1) m * unionKernel ν) := by
    rw [forestUnion_eq_vecMul, na_arm_add, na_arm_succ, na_step]
    simp only [vecMul_vecMul, Matrix.mul_assoc]
  rw [hP, na_arm_two_mix f e hij hjk fun l hl => by
      rcases hf l hl.le with h | h | rfl
      · exact Or.inl h
      · exact Or.inr h
      · omega,
    na_posForest_eq_single fun l hl => by
      rcases hf l hl.le with rfl | rfl | h
      · omega
      · omega
      · exact h,
    na_mix_union, add_vecMul, smul_vecMul, smul_vecMul, na_ES_add, na_ES_smul, na_ES_smul,
    na_ES_nice hΦ (isGoodForest_singletons _) (by rw [lineages_image_singleton]; exact hlow)
      (by rw [lineages_image_singleton, na_card_three hij' hik' hjk']),
    na_ES_nice hΦ ((na_merged_good hij').1.union (isGoodForest_singletons _)
      (by rw [(na_merged_good hij').2, lineages_image_singleton]
          exact disjoint_singleton_right.2 (by simp [hik'.symm, hjk'.symm])))
      (by rw [lineages_union, (na_merged_good hij').2, lineages_image_singleton]; exact hlow)
      (by rw [lineages_union, (na_merged_good hij').2, lineages_image_singleton,
        na_card_three hij' hik' hjk']),
    na_score_sing fun D hD => na_card_mem_sing hD, na_score_merged hij']

/-- **One arm carries two lineages, the other one.** -/
private theorem na_score_two_one {T : ℝ} {i j k : Fin 4} (hij : i ≠ j) :
    na_ES (forestUnion (Real.exp (-T) • Pi.single (na_sing {i, j}) 1 +
      (1 - Real.exp (-T)) • Pi.single (insert {i, j} (na_sing {i, j})) 1)
        (Pi.single (na_sing {k}) 1)) =
      Real.exp (-T) * (1 / 3) + (1 - Real.exp (-T)) * na_pairScore {i, j} := by
  rw [forestUnion_eq_vecMul, na_mix_union, na_ES_add, na_ES_smul, na_ES_smul, na_ES_single,
    na_ES_single, na_score_sing fun D hD => na_card_mem_sing hD, na_score_merged hij]

/-- **Each arm carries two lineages.** -/
private theorem na_score_two_two {T T' : ℝ} {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hc : ({i, j} : Finset (Fin 4))ᶜ = {k, l}) :
    na_ES (forestUnion (Real.exp (-T) • Pi.single (na_sing {i, j}) 1 +
      (1 - Real.exp (-T)) • Pi.single (insert {i, j} (na_sing {i, j})) 1)
        (Real.exp (-T') • Pi.single (na_sing {k, l}) 1 +
          (1 - Real.exp (-T')) • Pi.single (insert {k, l} (na_sing {k, l})) 1)) =
      Real.exp (-(T + T')) * (1 / 3) + (1 - Real.exp (-(T + T'))) * na_pairScore {i, j} := by
  have hkl' : na_pairScore {k, l} = na_pairScore {i, j} := by rw [← hc, na_pairScore_compl]
  have hboth : quartetScore (insert {i, j} (na_sing {i, j}) ∪ insert {k, l} (na_sing {k, l})) =
      na_pairScore {i, j} := by
    refine na_score_pair (card_pair hij) (fun D hD => ?_)
      (Or.inl (mem_union_left _ (mem_insert_self _ _)))
    rcases mem_union.1 hD with hD | hD
    · rcases mem_insert.1 hD with rfl | hD
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (na_card_mem_sing hD)
    · rcases mem_insert.1 hD with rfl | hD
      · exact Or.inr (Or.inr hc.symm)
      · exact Or.inl (na_card_mem_sing hD)
  simp only [forestUnion_add_left, forestUnion_smul_left]
  rw [forestUnion_comm (Pi.single (na_sing {i, j}) 1),
    forestUnion_comm (Pi.single (insert {i, j} (na_sing {i, j})) 1)]
  simp only [forestUnion_add_left, forestUnion_smul_left, forestUnion_single_single, na_ES_add,
    na_ES_smul, na_ES_single]
  rw [na_sing_union, na_score_sing fun D hD => na_card_mem_sing hD, na_score_merged hkl,
    union_comm, na_score_merged hij, union_comm, hboth, hkl', Real.exp_neg, Real.exp_neg,
    Real.exp_neg, Real.exp_add]
  field_simp
  ring

/-! ### Edge lengths along the arms -/

private theorem na_sum_eL {p a b : ℕ} (W : ℕ → ℝ) (tL : ℝ) (hb : b ≤ p) :
    ∑ h ∈ Ico a b, na_eL p W tL h = pathLen W a b :=
  sum_congr rfl fun h hh => by
    rw [mem_Ico] at hh
    exact ite_eq_right (by omega)

private theorem na_sum_eL_top {p a : ℕ} (W : ℕ → ℝ) (tL : ℝ) (ha : a ≤ p) :
    ∑ h ∈ Ico a (p + 1), na_eL p W tL h = pathLen W a p + tL := by
  rw [sum_Ico_succ_top ha, na_sum_eL W tL le_rfl]
  exact congrArg _ (ite_eq_left rfl)

private theorem na_sum_eR {d q a b : ℕ} (W : ℕ → ℝ) (tR : ℝ) (hq : q < d) (ha : d - q ≤ a)
    (hab : a ≤ b) (hb : b ≤ d) :
    ∑ h ∈ Ico (d - b) (d - a), na_eR d q W tR h = pathLen W a b := by
  have h1 : ∑ h ∈ Ico (d - b) (d - a), na_eR d q W tR h =
      ∑ h ∈ Ico (d - b) (d - a), W (d - 1 - h) :=
    sum_congr rfl fun h hh => by
      rw [mem_Ico] at hh
      rw [na_eR, ite_eq_right (by omega)]
      congr 1
      omega
  rw [h1, sum_Ico_reflect W _ (by omega : d - a ≤ d - 1 + 1),
    show d - 1 + 1 - (d - a) = a by omega, show d - 1 + 1 - (d - b) = b by omega]
  rfl

private theorem na_sum_eR_top {d q b : ℕ} (W : ℕ → ℝ) (tR : ℝ) (hq : q < d) (hb : d - q ≤ b)
    (hbd : b ≤ d) :
    ∑ h ∈ Ico (d - b) (q + 1), na_eR d q W tR h = pathLen W (d - q) b + tR := by
  rw [sum_Ico_succ_top (by omega), ← na_sum_eR W tR hq le_rfl hb hbd,
    show d - (d - q) = q by omega]
  exact congrArg _ (ite_eq_left rfl)

/-- The two arms together: from position `a` on the left arm up to the top node and down to
position `b` on the right arm. -/
private theorem na_pathLen_top {d p q : ℕ} {rv : Bool} (hd : d = p + q + 1 + (if rv then 1 else 0))
    {W : ℕ → ℝ} {tL tR : ℝ} (ht : if rv then tL = W p ∧ tR = W (p + 1) else tL + tR = W p)
    {a b : ℕ} (ha : a ≤ p) (hb : d - q ≤ b) :
    pathLen W a p + tL + (pathLen W (d - q) b + tR) = pathLen W a b := by
  unfold pathLen
  cases rv
  · simp only [Bool.false_eq_true, ite_false] at hd ht
    rw [← sum_Ico_consecutive W ha (show p ≤ b by omega),
      ← sum_Ico_consecutive W (Nat.le_succ p) (show p + 1 ≤ b by omega), sum_Ico_succ_top le_rfl,
      Ico_self, sum_empty, show d - q = p + 1 by omega, ← ht]
    ring
  · simp only [ite_true] at hd ht
    rw [← sum_Ico_consecutive W ha (show p ≤ b by omega),
      ← sum_Ico_consecutive W (show p ≤ p + 2 by omega) (show p + 2 ≤ b by omega),
      show p + 2 = p + 1 + 1 by rfl, sum_Ico_succ_top (Nat.le_succ p), sum_Ico_succ_top le_rfl,
      Ico_self, sum_empty, show d - q = p + 1 + 1 by omega, ht.1, ht.2]
    ring

/-! ### The quartet CF of the path, through the sorted lineages -/

/-- The four lineages in the order of their positions: `σ.symm l` is the rank of lineage `l`. -/
private theorem na_rank_facts : ∀ σ : Equiv.Perm (Fin 4),
    min (max (min (σ.symm 0) (σ.symm 1)) (min (σ.symm 2) (σ.symm 3)))
        (min (max (σ.symm 0) (σ.symm 1)) (max (σ.symm 2) (σ.symm 3))) = 1 ∧
    max (max (min (σ.symm 0) (σ.symm 1)) (min (σ.symm 2) (σ.symm 3)))
        (min (max (σ.symm 0) (σ.symm 1)) (max (σ.symm 2) (σ.symm 3))) = 2 ∧
    ((max (σ.symm 0) (σ.symm 1) < min (σ.symm 2) (σ.symm 3) ∨
        max (σ.symm 2) (σ.symm 3) < min (σ.symm 0) (σ.symm 1)) ↔
      (({σ 0, σ 1} : Finset (Fin 4)) = {0, 1} ∨ ({σ 0, σ 1} : Finset (Fin 4)) = {2, 3})) ∧
    ({σ 0, σ 1} : Finset (Fin 4))ᶜ = ({σ 2, σ 3} : Finset (Fin 4)) := by
  decide

/-- `pathCF` in terms of the lineages sorted by position (`pos ∘ σ` increasing): the internal path
joins the second and third positions, and the split is that of the two lowest lineages. -/
private theorem na_pathCF_eq (W : ℕ → ℝ) (pos : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4))
    (hσ : StrictMono (pos ∘ σ)) :
    pathCF W (pos 0) (pos 1) (pos 2) (pos 3) =
      Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2))) * (1 / 3) +
        (1 - Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2)))) * na_pairScore {σ 0, σ 1} := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 4 → ℕ, x = pos ∘ σ := ⟨_, rfl⟩
  have hpos : ∀ l, pos l = x (σ.symm l) := fun l => by rw [hx, Function.comp_apply,
    Equiv.apply_symm_apply]
  have hx1 : pos (σ 1) = x 1 := by rw [hx, Function.comp_apply]
  have hx2 : pos (σ 2) = x 2 := by rw [hx, Function.comp_apply]
  rw [← hx] at hσ
  obtain ⟨hlo, hhi, hcond, -⟩ := na_rank_facts σ
  have hm := hσ.monotone
  rw [hx1, hx2, hpos 0, hpos 1, hpos 2, hpos 3]
  simp only [pathCF, ← hm.map_min, ← hm.map_max, hσ.lt_iff_lt, hlo, hhi, hcond]
  unfold na_pairScore
  split_ifs <;> ring

/-- The complementary pair of the two lowest lineages. -/
private theorem na_compl_pair (σ : Equiv.Perm (Fin 4)) :
    ({σ 0, σ 1} : Finset (Fin 4))ᶜ = ({σ 3, σ 2} : Finset (Fin 4)) := by
  rw [(na_rank_facts σ).2.2.2, pair_comm]

private theorem na_cover : ∀ (σ : Equiv.Perm (Fin 4)) (l : Fin 4),
    l = σ 0 ∨ l = σ 1 ∨ l = σ 2 ∨ l = σ 3 := by
  decide

private theorem na_sorted {pos : Fin 4 → ℕ} {σ : Equiv.Perm (Fin 4)} (hσ : StrictMono (pos ∘ σ)) :
    pos (σ 0) < pos (σ 1) ∧ pos (σ 1) < pos (σ 2) ∧ pos (σ 2) < pos (σ 3) :=
  ⟨hσ (show (0 : Fin 4) < 1 by decide), hσ (show (1 : Fin 4) < 2 by decide),
    hσ (show (2 : Fin 4) < 3 by decide)⟩

/-! ### The three cases -/

/-- **Three lineages on the left arm.** -/
private theorem na_caseA {d p q : ℕ} (hd1 : p + q + 1 ≤ d) (W : ℕ → ℝ) (tL tR : ℝ)
    {pos : Fin 4 → ℕ} (hle : ∀ l, pos l ≤ d) {σ : Equiv.Perm (Fin 4)}
    (hσ : StrictMono (pos ∘ σ)) (hA : pos (σ 2) ≤ p) :
    na_ES (forestUnion (na_arm pos (na_eL p W tL) (p + 1))
      (na_arm (fun l => d - pos l) (na_eR d q W tR) (q + 1))) =
      Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2))) * (1 / 3) +
        (1 - Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2)))) * na_pairScore {σ 0, σ 1} := by
  obtain ⟨h01, h12, h23⟩ := na_sorted hσ
  obtain ⟨hν1, hν2⟩ := na_arm_dist (fun l => d - pos l) (na_eR d q W tR) (q + 1)
  rw [na_score_P pos (na_eL p W tL) hν1 hν2 (fun l hl => ?_) h01 h12 (by omega) (fun l hl => ?_),
    na_sum_eL W tL hA]
  · simp only [mem_filter, mem_univ, true_and] at hl
    have := hle l
    omega
  · rcases na_cover σ l with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · omega

/-- **Three lineages on the right arm.** -/
private theorem na_caseB {d p q : ℕ} (hd1 : p + q + 1 ≤ d) (W : ℕ → ℝ) (tL tR : ℝ)
    {pos : Fin 4 → ℕ} (hle : ∀ l, pos l ≤ d) {σ : Equiv.Perm (Fin 4)}
    (hσ : StrictMono (pos ∘ σ)) (hB : d - q ≤ pos (σ 1)) :
    na_ES (forestUnion (na_arm pos (na_eL p W tL) (p + 1))
      (na_arm (fun l => d - pos l) (na_eR d q W tR) (q + 1))) =
      Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2))) * (1 / 3) +
        (1 - Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2)))) * na_pairScore {σ 0, σ 1} := by
  obtain ⟨h01, h12, h23⟩ := na_sorted hσ
  have h3 := hle (σ 3)
  obtain ⟨hν1, hν2⟩ := na_arm_dist pos (na_eL p W tL) (p + 1)
  rw [forestUnion_comm, na_score_P (fun l => d - pos l) (na_eR d q W tR) (i := σ 3) (j := σ 2)
    (k := σ 1) hν1 hν2 (fun l hl => ?_) (by omega) (by omega)
    (by omega) (fun l hl => ?_)]
  · rw [na_sum_eR W tR (by omega) hB h12.le (hle _), ← na_compl_pair, na_pairScore_compl]
  · simp only [mem_filter, mem_univ, true_and] at hl
    omega
  · rcases na_cover σ l with rfl | rfl | rfl | rfl
    · omega
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

/-- **At most two lineages on each arm**: the pairs travel to the top node, where they meet. -/
private theorem na_caseC {d p q : ℕ} {rv : Bool} (hd : d = p + q + 1 + (if rv then 1 else 0))
    {W : ℕ → ℝ} {tL tR : ℝ} (ht : if rv then tL = W p ∧ tR = W (p + 1) else tL + tR = W p)
    {pos : Fin 4 → ℕ} (hle : ∀ l, pos l ≤ d) {σ : Equiv.Perm (Fin 4)}
    (hσ : StrictMono (pos ∘ σ)) (hA : p < pos (σ 2)) (hB : pos (σ 1) < d - q) :
    na_ES (forestUnion (na_arm pos (na_eL p W tL) (p + 1))
      (na_arm (fun l => d - pos l) (na_eR d q W tR) (q + 1))) =
      Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2))) * (1 / 3) +
        (1 - Real.exp (-pathLen W (pos (σ 1)) (pos (σ 2)))) * na_pairScore {σ 0, σ 1} := by
  obtain ⟨h01, h12, h23⟩ := na_sorted hσ
  have h3 := hle (σ 3)
  have hd1 : p + q + 1 ≤ d := by split_ifs at hd <;> omega
  have hd2 : d ≤ p + q + 2 := by split_ifs at hd <;> omega
  have hij : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hlk : σ 3 ≠ σ 2 := σ.injective.ne (by decide)
  -- the left arm with the two lowest lineages
  have hL2 : pos (σ 1) ≤ p → na_arm pos (na_eL p W tL) (p + 1) =
      Real.exp (-(pathLen W (pos (σ 1)) p + tL)) • Pi.single (na_sing {σ 0, σ 1}) 1 +
        (1 - Real.exp (-(pathLen W (pos (σ 1)) p + tL))) •
          Pi.single (insert {σ 0, σ 1} (na_sing {σ 0, σ 1})) 1 := fun h1 => by
    rw [na_arm_two_mix pos (na_eL p W tL) h01 (by omega) fun l hl => ?_, na_sum_eL_top W tL h1]
    rcases na_cover σ l with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
    · omega
  -- the right arm with the two highest lineages
  have hR2 : d - q ≤ pos (σ 2) → na_arm (fun l => d - pos l) (na_eR d q W tR) (q + 1) =
      Real.exp (-(pathLen W (d - q) (pos (σ 2)) + tR)) • Pi.single (na_sing {σ 3, σ 2}) 1 +
        (1 - Real.exp (-(pathLen W (d - q) (pos (σ 2)) + tR))) •
          Pi.single (insert {σ 3, σ 2} (na_sing {σ 3, σ 2})) 1 := fun h2 => by
    rw [na_arm_two_mix (fun l => d - pos l) (na_eR d q W tR) (i := σ 3) (j := σ 2)
      (by omega) (by omega) fun l hl => ?_]
    · rw [na_sum_eR_top W tR (by omega) h2 (hle _)]
    · rcases na_cover σ l with rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact Or.inr rfl
      · exact Or.inl rfl
  by_cases h1 : pos (σ 1) ≤ p <;> by_cases h2 : d - q ≤ pos (σ 2)
  · -- two lineages on each arm
    rw [hL2 h1, hR2 h2, na_score_two_two hij hlk (na_compl_pair σ), na_pathLen_top hd ht h1 h2]
  · -- the third lineage is in the component of the root
    have hrv : rv = true := by
      cases rv
      · simp only [Bool.false_eq_true, ite_false] at hd
        omega
      · rfl
    subst hrv
    simp only [ite_true] at hd ht
    rw [hL2 h1, na_arm_one (fun l => d - pos l) (na_eR d q W tR) (i := σ 3) (by omega)
      fun l hl => ?_, na_score_two_one hij, ht.1, show pos (σ 2) = p + 1 by omega]
    · rw [pathLen, pathLen, sum_Ico_succ_top h1]
    · rcases na_cover σ l with rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · rfl
  · -- the second lineage is in the component of the root
    have hrv : rv = true := by
      cases rv
      · simp only [Bool.false_eq_true, ite_false] at hd
        omega
      · rfl
    subst hrv
    simp only [ite_true] at hd ht
    rw [hR2 h2, na_arm_one pos (na_eL p W tL) (i := σ 0) (by omega) fun l hl => ?_,
      forestUnion_comm, na_score_two_one hlk, ← na_compl_pair, na_pairScore_compl, ht.2,
      show pos (σ 1) = p + 1 by omega, show d - q = p + 1 + 1 by omega]
    · rw [pathLen, pathLen, sum_eq_sum_Ico_succ_bot (show p + 1 < pos (σ 2) by omega),
        add_comm (W (p + 1))]
    · rcases na_cover σ l with rfl | rfl | rfl | rfl
      · rfl
      · omega
      · omega
      · omega
  · omega

/-- **The displayed tree.** The path `0 — 1 — ⋯ — d` has edge lengths `W m` (between `m` and
`m + 1`); its top node is the node `p + 1` (`rv = true`: then the two edges at the top node are
`W p` and `W (p + 1)`, and a lineage at position `p + 1` belongs to the component of the root,
outside the arms) or lies inside the edge between `p` and `p + 1` (`rv = false`: the two parts of
the edge, of lengths `tL` and `tR`, add up to `W p`). The lineages `0, 1, 2, 3` are at distinct
positions `pos l ≤ d`. Then the expected score of the forest at the top node is the CF of the split
`{0, 1} | {2, 3}` in the quartet tree that the positions induce on the path. -/
theorem displayed_score (d p q : ℕ) (rv : Bool) (hd : d = p + q + 1 + (if rv then 1 else 0))
    (W : ℕ → ℝ) (tL tR : ℝ) (ht : if rv then tL = W p ∧ tR = W (p + 1) else tL + tR = W p)
    (pos : Fin 4 → ℕ) (hinj : Function.Injective pos) (hle : ∀ l, pos l ≤ d) :
    ∑ F, forestUnion (leftArm p W tL pos) (rightArm d q W tR pos) F * quartetScore F =
      pathCF W (pos 0) (pos 1) (pos 2) (pos 3) := by
  have hd1 : p + q + 1 ≤ d := by split_ifs at hd <;> omega
  rw [na_leftArm_eq, na_rightArm_eq W tR hle (by omega)]
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 4), StrictMono (pos ∘ σ) :=
    ⟨Tuple.sort pos, (Tuple.monotone_sort pos).strictMono_of_injective
      (hinj.comp (Tuple.sort pos).injective)⟩
  rw [na_pathCF_eq W pos σ hσ]
  change na_ES _ = _
  by_cases hA : pos (σ 2) ≤ p
  · exact na_caseA hd1 W tL tR hle hσ hA
  by_cases hB : d - q ≤ pos (σ 1)
  · exact na_caseB hd1 W tL tR hle hσ hB
  exact na_caseC hd ht hle hσ (by omega) (by omega)

end Phylogenetics
