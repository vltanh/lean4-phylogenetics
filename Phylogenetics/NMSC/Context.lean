module

public import Phylogenetics.NMSC.Process
public import Phylogenetics.NMSC.Symmetry
/-!
# From the network to the top of a cycle

Let `Ω` be a cycle of the network `N`, and sample one lineage from each of four taxa of `N`, at
least three of which lie below the top node of `Ω`. The rest of `N` (the component of `Ω` that
contains the root of `N`, with at most one sampled lineage, and the population above the root) acts
on the forest arriving at the top node of `Ω` by a nice kernel (`Phylogenetics.NiceKernel`). Hence
the quartet CF of the four taxa is the expected score `Phylogenetics.quartetScore` of that forest
(`Phylogenetics.quartetCF_eq_sum_top`): `1` if the forest has the cluster `{0, 1}` or `{2, 3}`, `0`
if it has another cluster of two lineages, `1/3` otherwise.

The rest of `N` is a network `K : Net (Option X)` with one leaf labelled `none`, where the top of
`Ω` is substituted (`Phylogenetics.Net.bind`). The network coalescent on `K` is linear in the forest
at `none`; its kernel, followed by the population above the root, is nice, and the gene trees it
produces are complete binary trees on the four lineages, whose score is the indicator of the split
`{0, 1} | {2, 3}`. -/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset Matrix

universe u

/-! ### The inputs at the leaves -/

section Inputs

variable {α : Type*} {L : Type*} [Fintype L] [DecidableEq L]

mutual
/-- The network coalescent reads the inputs at the leaves of the network only. -/
private theorem ns_net_congr {ι ι' : α → Finset (Finset L) → ℝ} :
    ∀ K : Net α, (∀ a ∈ K.leaves, ι a = ι' a) → K.forestDistOf ι = K.forestDistOf ι'
  | .leaf a, h => by
      simp only [Net.forestDistOf]
      exact h a (by simp [Net.leaves])
  | .tree ℓ₁ K₁ ℓ₂ K₂, h => by
      have h₁ := ns_net_congr K₁ fun a ha => h a (by simp [Net.leaves, ha])
      have h₂ := ns_net_congr K₂ fun a ha => h a (by simp [Net.leaves, ha])
      simp only [Net.forestDistOf, h₁, h₂]
  | .cycle γ S₁ S₂ ℓ K, h => by
      have h₁ := ns_side_congr S₁ fun a ha => h a (by simp [Net.leaves, ha])
      have h₂ := ns_side_congr S₂ fun a ha => h a (by simp [Net.leaves, ha])
      have h₀ := ns_net_congr K fun a ha => h a (by simp [Net.leaves, ha])
      simp only [Net.forestDistOf, h₁, h₂, h₀]

/-- The same for sides. -/
private theorem ns_side_congr {ι ι' : α → Finset (Finset L) → ℝ} :
    ∀ S : Side α, (∀ a ∈ S.leaves, ι a = ι' a) → S.forestDistOf ι = S.forestDistOf ι'
  | .hyb _, _ => by simp only [Side.forestDistOf]
  | .node ℓ b K S, h => by
      have h₀ := ns_net_congr K fun a ha => h a (by simp [Side.leaves, ha])
      have h₁ := ns_side_congr S fun a ha => h a (by simp [Side.leaves, ha])
      simp only [Side.forestDistOf, h₀, h₁]
end

end Inputs

/-! ### Linearity in the input at the leaf `none` -/

section Linear

variable {X : Type u} [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

private theorem ns_net_indep (ι : X → Finset (Finset L) → ℝ) {K : Net (Option X)}
    (h : K.leaves.count none = 0) (μ μ' : Finset (Finset L) → ℝ) :
    K.forestDistOf (fun o => o.elim μ ι) = K.forestDistOf (fun o => o.elim μ' ι) :=
  ns_net_congr K fun a ha => by
    cases a with
    | none => exact absurd ha (List.count_eq_zero.1 h)
    | some x => rfl

private theorem ns_side_indep (ι : X → Finset (Finset L) → ℝ) {S : Side (Option X)}
    (h : S.leaves.count none = 0) (μ μ' : Finset (Finset L) → ℝ) :
    S.forestDistOf (fun o => o.elim μ ι) = S.forestDistOf (fun o => o.elim μ' ι) :=
  ns_side_congr S fun a ha => by
    cases a with
    | none => exact absurd ha (List.count_eq_zero.1 h)
    | some x => rfl

private theorem ns_forestUnion_vecMul_left (μ ν : Finset (Finset L) → ℝ)
    (M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) :
    forestUnion (μ ᵥ* M) ν = μ ᵥ* (M * unionKernel ν) := by
  rw [forestUnion_eq_vecMul, vecMul_vecMul]

private theorem ns_forestUnion_vecMul_right (μ ν : Finset (Finset L) → ℝ)
    (M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) :
    forestUnion ν (μ ᵥ* M) = μ ᵥ* (M * unionKernel ν) := by
  rw [forestUnion_comm, ns_forestUnion_vecMul_left]

/-- The hybrid node and the two sides of a cycle, when the forests at the top of the sides are
linear in `μ`. -/
private theorem ns_cycle_linear (γ : ℝ) (v μ : Finset (Finset L) → ℝ)
    (Y : Finset (Finset L) → Finset (Finset L) →
      Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ) :
    (fun G => ∑ F, v F * ∑ A ∈ (roots F).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F \ A) * (μ ᵥ* Y F A) G) =
      μ ᵥ* ∑ F, ∑ A ∈ (roots F).powerset, (v F * (γ ^ #A * (1 - γ) ^ #(roots F \ A))) • Y F A := by
  simp only [vecMul_sum, vecMul_smul]
  ext G
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

mutual
/-- If the leaf `none` occurs once in `K`, the network coalescent on `K` is linear in the input at
`none`. -/
private theorem ns_net_linear (ι : X → Finset (Finset L) → ℝ) :
    ∀ K : Net (Option X), K.leaves.count none = 1 →
      ∃ M : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ,
        ∀ μ, K.forestDistOf (fun o => o.elim μ ι) = μ ᵥ* M
  | .leaf none, _ => ⟨1, fun μ => by simp [Net.forestDistOf]⟩
  | .leaf (some x), h => by simp [Net.leaves] at h
  | .tree ℓ₁ K₁ ℓ₂ K₂, h => by
      simp only [Net.leaves, List.count_append] at h
      rcases (by omega : (K₁.leaves.count none = 1 ∧ K₂.leaves.count none = 0) ∨
          (K₁.leaves.count none = 0 ∧ K₂.leaves.count none = 1)) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · obtain ⟨M, hM⟩ := ns_net_linear ι K₁ h₁
        refine ⟨M * kingmanTransition ℓ₁ * unionKernel
          (K₂.forestDistOf (fun o => o.elim 0 ι) ᵥ* kingmanTransition ℓ₂), fun μ => ?_⟩
        simp only [Net.forestDistOf]
        rw [hM, ns_net_indep ι h₂ μ 0, vecMul_vecMul, ns_forestUnion_vecMul_left]
      · obtain ⟨M, hM⟩ := ns_net_linear ι K₂ h₂
        refine ⟨M * kingmanTransition ℓ₂ * unionKernel
          (K₁.forestDistOf (fun o => o.elim 0 ι) ᵥ* kingmanTransition ℓ₁), fun μ => ?_⟩
        simp only [Net.forestDistOf]
        rw [hM, ns_net_indep ι h₁ μ 0, vecMul_vecMul, ns_forestUnion_vecMul_right]
  | .cycle γ S₁ S₂ ℓ K, h => by
      simp only [Net.leaves, List.count_append] at h
      rcases (by omega : (S₁.leaves.count none = 1 ∧ S₂.leaves.count none = 0 ∧
          K.leaves.count none = 0) ∨ (S₁.leaves.count none = 0 ∧ S₂.leaves.count none = 1 ∧
          K.leaves.count none = 0) ∨ (S₁.leaves.count none = 0 ∧ S₂.leaves.count none = 0 ∧
          K.leaves.count none = 1)) with ⟨h₁, h₂, h₀⟩ | ⟨h₁, h₂, h₀⟩ | ⟨h₁, h₂, h₀⟩
      · -- `none` hangs from the side `S₁`
        obtain ⟨M, hM⟩ := ns_side_linear ι S₁ h₁
        refine ⟨∑ F, ∑ A ∈ (roots F).powerset,
          ((K.forestDistOf (fun o => o.elim 0 ι) ᵥ* kingmanTransition ℓ) F *
            (γ ^ #A * (1 - γ) ^ #(roots F \ A))) • (M (forestBelow F A) *
              unionKernel (S₂.forestDistOf (fun o => o.elim 0 ι) (forestBelow F (roots F \ A)))),
          fun μ => ?_⟩
        simp only [Net.forestDistOf]
        rw [ns_net_indep ι h₀ μ 0, ns_side_indep ι h₂ μ 0]
        simp only [hM, ns_forestUnion_vecMul_left]
        exact ns_cycle_linear γ _ μ _
      · -- `none` hangs from the side `S₂`
        obtain ⟨M, hM⟩ := ns_side_linear ι S₂ h₂
        refine ⟨∑ F, ∑ A ∈ (roots F).powerset,
          ((K.forestDistOf (fun o => o.elim 0 ι) ᵥ* kingmanTransition ℓ) F *
            (γ ^ #A * (1 - γ) ^ #(roots F \ A))) • (M (forestBelow F (roots F \ A)) *
              unionKernel (S₁.forestDistOf (fun o => o.elim 0 ι) (forestBelow F A))),
          fun μ => ?_⟩
        simp only [Net.forestDistOf]
        rw [ns_net_indep ι h₀ μ 0, ns_side_indep ι h₁ μ 0]
        simp only [hM, ns_forestUnion_vecMul_right]
        exact ns_cycle_linear γ _ μ _
      · -- `none` is below the hybrid node
        obtain ⟨M, hM⟩ := ns_net_linear ι K h₀
        refine ⟨M * kingmanTransition ℓ * Matrix.of fun F G => ∑ A ∈ (roots F).powerset,
          γ ^ #A * (1 - γ) ^ #(roots F \ A) *
            forestUnion (S₁.forestDistOf (fun o => o.elim 0 ι) (forestBelow F A))
              (S₂.forestDistOf (fun o => o.elim 0 ι) (forestBelow F (roots F \ A))) G,
          fun μ => ?_⟩
        simp only [Net.forestDistOf]
        rw [ns_side_indep ι h₁ μ 0, ns_side_indep ι h₂ μ 0, hM, vecMul_vecMul,
          ← vecMul_vecMul μ (M * kingmanTransition ℓ)]
        ext G
        simp only [vecMul, dotProduct, Matrix.of_apply]

/-- The same for sides, for each forest entering the bottom of the side. -/
private theorem ns_side_linear (ι : X → Finset (Finset L) → ℝ) :
    ∀ S : Side (Option X), S.leaves.count none = 1 →
      ∃ M : Finset (Finset L) → Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ,
        ∀ μ F, S.forestDistOf (fun o => o.elim μ ι) F = μ ᵥ* M F
  | .hyb _, h => by simp [Side.leaves] at h
  | .node ℓ b K S, h => by
      simp only [Side.leaves, List.count_append] at h
      rcases (by omega : (K.leaves.count none = 1 ∧ S.leaves.count none = 0) ∨
          (K.leaves.count none = 0 ∧ S.leaves.count none = 1)) with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · obtain ⟨M, hM⟩ := ns_net_linear ι K h₀
        refine ⟨fun F => M * kingmanTransition b *
          unionKernel (S.forestDistOf (fun o => o.elim 0 ι) F) * kingmanTransition ℓ,
          fun μ F => ?_⟩
        simp only [Side.forestDistOf]
        rw [hM, ns_side_indep ι h₁ μ 0, vecMul_vecMul, ns_forestUnion_vecMul_right,
          vecMul_vecMul]
      · obtain ⟨M, hM⟩ := ns_side_linear ι S h₁
        refine ⟨fun F => M F * unionKernel
          (K.forestDistOf (fun o => o.elim 0 ι) ᵥ* kingmanTransition b) * kingmanTransition ℓ,
          fun μ F => ?_⟩
        simp only [Side.forestDistOf]
        rw [hM, ns_net_indep ι h₀ μ 0, ns_forestUnion_vecMul_left, vecMul_vecMul]
end

end Linear

/-! ### The context of a subnetwork -/

section Context

variable {X : Type u}

mutual
private theorem ns_net_bind_some (f : Option X → Net X) (hf : ∀ x, f (some x) = .leaf x) :
    ∀ N : Net X, (N.bind fun x => .leaf (some x)).bind f = N
  | .leaf x => by
      simp only [Net.bind]
      exact hf x
  | .tree ℓ₁ N₁ ℓ₂ N₂ => by
      simp only [Net.bind, ns_net_bind_some f hf N₁, ns_net_bind_some f hf N₂]
  | .cycle γ S₁ S₂ ℓ N => by
      simp only [Net.bind, ns_side_bind_some f hf S₁, ns_side_bind_some f hf S₂,
        ns_net_bind_some f hf N]

private theorem ns_side_bind_some (f : Option X → Net X) (hf : ∀ x, f (some x) = .leaf x) :
    ∀ S : Side X, (S.bind fun x => .leaf (some x)).bind f = S
  | .hyb _ => by simp only [Side.bind]
  | .node ℓ b N S => by
      simp only [Side.bind, ns_net_bind_some f hf N, ns_side_bind_some f hf S]
end

mutual
/-- Every subnetwork `C` of `N` has a context: a network `K` with a leaf `none` where `C` is
substituted to give `N`. -/
private theorem ns_net_context (C : Net X) :
    ∀ N : Net X, C ∈ N.subnets →
      ∃ K : Net (Option X), none ∈ K.leaves ∧ N = K.bind fun o => o.elim C Net.leaf
  | .leaf x, h => by
      simp only [Net.subnets, List.mem_singleton] at h
      exact ⟨.leaf none, by simp [Net.leaves], by rw [h]; rfl⟩
  | .tree ℓ₁ N₁ ℓ₂ N₂, h => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact ⟨.leaf none, by simp [Net.leaves], by rw [h]; rfl⟩
      · obtain ⟨K, hK, hKN⟩ := ns_net_context C N₁ h
        refine ⟨.tree ℓ₁ K ℓ₂ (N₂.bind fun x => .leaf (some x)), by simp [Net.leaves, hK], ?_⟩
        simp only [Net.bind]
        rw [ns_net_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hKN]
      · obtain ⟨K, hK, hKN⟩ := ns_net_context C N₂ h
        refine ⟨.tree ℓ₁ (N₁.bind fun x => .leaf (some x)) ℓ₂ K, by simp [Net.leaves, hK], ?_⟩
        simp only [Net.bind]
        rw [ns_net_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hKN]
  | .cycle γ S₁ S₂ ℓ N, h => by
      simp only [Net.subnets, List.mem_cons, List.mem_append] at h
      rcases h with h | (h | h) | h
      · exact ⟨.leaf none, by simp [Net.leaves], by rw [h]; rfl⟩
      · obtain ⟨T, hT, hTS⟩ := ns_side_context C S₁ h
        refine ⟨.cycle γ T (S₂.bind fun x => .leaf (some x)) ℓ (N.bind fun x => .leaf (some x)),
          by simp [Net.leaves, hT], ?_⟩
        simp only [Net.bind]
        rw [ns_side_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl),
          ns_net_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hTS]
      · obtain ⟨T, hT, hTS⟩ := ns_side_context C S₂ h
        refine ⟨.cycle γ (S₁.bind fun x => .leaf (some x)) T ℓ (N.bind fun x => .leaf (some x)),
          by simp [Net.leaves, hT], ?_⟩
        simp only [Net.bind]
        rw [ns_side_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl),
          ns_net_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hTS]
      · obtain ⟨K, hK, hKN⟩ := ns_net_context C N h
        refine ⟨.cycle γ (S₁.bind fun x => .leaf (some x)) (S₂.bind fun x => .leaf (some x)) ℓ K,
          by simp [Net.leaves, hK], ?_⟩
        simp only [Net.bind]
        rw [ns_side_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl),
          ns_side_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hKN]

/-- The same for the subnetworks hanging from a side. -/
private theorem ns_side_context (C : Net X) :
    ∀ S : Side X, C ∈ S.subnets →
      ∃ T : Side (Option X), none ∈ T.leaves ∧ S = T.bind fun o => o.elim C Net.leaf
  | .hyb _, h => by simp [Side.subnets] at h
  | .node ℓ b N S, h => by
      simp only [Side.subnets, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨K, hK, hKN⟩ := ns_net_context C N h
        refine ⟨.node ℓ b K (S.bind fun x => .leaf (some x)), by simp [Side.leaves, hK], ?_⟩
        simp only [Side.bind]
        rw [ns_side_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hKN]
      · obtain ⟨T, hT, hTS⟩ := ns_side_context C S h
        refine ⟨.node ℓ b (N.bind fun x => .leaf (some x)) T, by simp [Side.leaves, hT], ?_⟩
        simp only [Side.bind]
        rw [ns_net_bind_some (fun o => o.elim C Net.leaf) (fun _ => rfl), ← hTS]
end

private theorem ns_pairwise_of_mem {β : Type*} {R : β → β → Prop} (hR : ∀ a b, R a b → R b a)
    {l : List β} (h : l.Pairwise R) {a b : β} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    R a b :=
  haveI : Std.Symm R := ⟨hR⟩
  h.forall ha hb hab

/-- The leaves of the context: its leaves are distinct, the leaves of `C` are distinct, and the
leaves of `C` are not leaves of the context. -/
private theorem ns_context_nodup {N C : Net X} {K : Net (Option X)} (hN : N.leaves.Nodup)
    (hK : none ∈ K.leaves) (hNK : N = K.bind fun o => o.elim C Net.leaf) :
    K.leaves.Nodup ∧ C.leaves.Nodup ∧ ∀ x, some x ∈ K.leaves → x ∉ C.leaves := by
  rw [hNK, Net.leaves_bind, List.nodup_flatMap] at hN
  obtain ⟨hnd, hpw⟩ := hN
  refine ⟨hpw.imp fun {a b} hab heq => ?_, hnd none hK, fun x hx hxC => ?_⟩
  · subst heq
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (a.elim C Net.leaf).leaves_ne_nil
    exact hab hy hy
  · have := ns_pairwise_of_mem (fun a b h => List.Disjoint.symm h) hpw hK hx (by simp)
    exact this hxC (by simp [Net.leaves])

/-- Every leaf of `N` is a leaf of `C` or of the context. -/
private theorem ns_context_cover {N C : Net X} {K : Net (Option X)}
    (hNK : N = K.bind fun o => o.elim C Net.leaf) {x : X} (hx : x ∈ N.leaves) :
    x ∈ C.leaves ∨ some x ∈ K.leaves := by
  rw [hNK, Net.leaves_bind, List.mem_flatMap] at hx
  obtain ⟨o, ho, hxo⟩ := hx
  cases o with
  | none => exact Or.inl hxo
  | some y =>
      simp only [Option.elim, Net.leaves, List.mem_singleton] at hxo
      exact Or.inr (hxo ▸ ho)

end Context

/-! ### The kernel of the context -/

section Kernel

variable {X : Type u} [DecidableEq X]

private theorem ns_lineages_sampledAt (s : Fin 4 → X) (x : X) :
    lineages (sampledAt s x) = univ.filter fun l => s l = x :=
  lineages_singletons _

private theorem ns_single_relabel (σ : Equiv.Perm (Fin 4)) (F H : Finset (Finset (Fin 4))) :
    (Pi.single F 1 : Finset (Finset (Fin 4)) → ℝ) (relabelFamily σ.symm H) =
      (Pi.single (relabelFamily σ F) 1 : Finset (Finset (Fin 4)) → ℝ) H := by
  have h : relabelFamily σ.symm H = F ↔ H = relabelFamily σ F := by
    constructor
    · rintro rfl
      have := relabelFamily_symm σ.symm H
      rw [Equiv.symm_symm] at this
      exact this.symm
    · rintro rfl
      exact relabelFamily_symm σ F
  simp only [Pi.single_apply, h]

/-- The kernel of the context `K` (the forest `F` at the leaf `none`, the sampled lineages at the
other leaves) is nice, adding the lineages sampled from the taxa of `K`. -/
private theorem ns_context_nice (K : Net (Option X)) (hKnd : K.leaves.Nodup)
    (hK : none ∈ K.leaves) (s : Fin 4 → X)
    (M : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ)
    (hMF : ∀ F G, M F G = K.forestDistOf (fun o => o.elim (Pi.single F 1) (sampledInput s)) G) :
    NiceKernel (univ.filter fun l => some (s l) ∈ K.leaves) M := by
  set S := univ.filter fun l => some (s l) ∈ K.leaves with hS
  -- the forests at the leaves
  have hinput : ∀ F, (fun o : Option X => o.elim (Pi.single F (1 : ℝ)) (sampledInput s)) =
      fun o => Pi.single (o.elim F (sampledAt s)) 1 := by
    intro F
    funext o
    cases o <;> rfl
  have hE : ∀ F, IsGood F → ∀ a ∈ K.leaves, IsGood (a.elim F (sampledAt s)) := by
    intro F hF a _
    cases a with
    | none => exact hF
    | some x => exact isGood_singletons _
  have hdisj : ∀ F, Disjoint (lineages F) S → ∀ a ∈ K.leaves, ∀ b ∈ K.leaves, a ≠ b →
      Disjoint (lineages (a.elim F (sampledAt s)))
        (lineages (b.elim F (sampledAt s))) := by
    have hxS : ∀ x, some x ∈ K.leaves → lineages (sampledAt s x) ⊆ S := by
      intro x hx l hl
      rw [ns_lineages_sampledAt, mem_filter] at hl
      rw [hS, mem_filter, hl.2]
      exact ⟨mem_univ _, hx⟩
    intro F hFS a ha b hb hab
    cases a with
    | none =>
      cases b with
      | none => exact absurd rfl hab
      | some y => exact disjoint_of_subset_right (hxS y hb) hFS
    | some x =>
      cases b with
      | none => exact disjoint_of_subset_left (hxS x ha) hFS.symm
      | some y =>
        simp only [Option.elim, ns_lineages_sampledAt]
        refine disjoint_filter.2 fun l _ h1 h2 => hab ?_
        rw [← h1, ← h2]
  refine ⟨fun σ hσ F G => ?_, fun F hF hFS => ?_, fun F hF hFS G hG => ?_⟩
  · -- relabelling
    rw [hMF, hMF, ← Net.forestDistOf_relabel σ _ K G]
    refine congrFun (ns_net_congr K fun a ha => ?_) _
    funext H
    cases a with
    | none => exact (ns_single_relabel σ F H).symm
    | some x =>
      have hfix : relabelFamily σ (sampledAt s x) = sampledAt s x := by
        refine relabel_eq_self fun l hl => hσ l ?_
        rw [ns_lineages_sampledAt, mem_filter] at hl
        rw [hS, mem_filter, hl.2]
        exact ⟨mem_univ _, ha⟩
      simp only [Option.elim, sampledInput]
      rw [ns_single_relabel, hfix]
  · -- total mass
    simp only [hMF, hinput]
    exact Net.forestDistOf_single_sum K hKnd _ (hE F hF) (hdisj F hFS)
  · -- support
    rw [hMF, hinput] at hG
    obtain ⟨hGg, hsub, hGl⟩ :=
      Net.forestDistOf_single_support K hKnd _ (hE F hF) (hdisj F hFS) hG
    refine ⟨hGg, hsub none hK, ?_⟩
    rw [hGl]
    ext l
    simp only [mem_biUnion, List.mem_toFinset, mem_union, hS, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, hl⟩
      cases a with
      | none => exact Or.inl hl
      | some x =>
        simp only [Option.elim, ns_lineages_sampledAt, mem_filter] at hl
        exact Or.inr (hl.2 ▸ ha)
    · rintro (hl | hl)
      · exact ⟨none, hK, hl⟩
      · exact ⟨some (s l), hl, by simp [ns_lineages_sampledAt]⟩

end Kernel

/-- The quartet CF of four taxa of `N` (one lineage sampled from each), at least three of them below
the top node of the cycle `Ω`, is the expected score of the forest arriving at the top node of
`Ω`. -/
theorem quartetCF_eq_sum_top {X : Type u} [DecidableEq X] (N : Net X) (hN : N.leaves.Nodup)
    (Ω : N.Cycle) (s : Fin 4 → X) (hsN : ∀ l, s l ∈ N.taxa)
    (h3 : 3 ≤ #(univ.filter fun l => s l ∈ Ω.top.taxa)) :
    N.quartetCF (s 0) (s 1) (s 2) (s 3) = ∑ F, Ω.top.forestDist s F * quartetScore F := by
  have hCmem : Ω.top ∈ N.subnets := Ω.mem
  generalize Ω.top = C at hCmem h3 ⊢
  -- the context `K` of `C` in `N`, and its kernel `M`
  obtain ⟨K, hK, hNK⟩ := ns_net_context C N hCmem
  obtain ⟨hKnd, hCnd, hKC⟩ := ns_context_nodup hN hK hNK
  obtain ⟨M, hM⟩ := ns_net_linear (sampledInput s) K (List.count_eq_one_of_mem hKnd hK)
  have hMF : ∀ F G, M F G =
      K.forestDistOf (fun o => o.elim (Pi.single F 1) (sampledInput s)) G := by
    intro F G
    rw [hM]
    simp
  set S := univ.filter fun l => some (s l) ∈ K.leaves with hS
  have hniceK : NiceKernel S M := ns_context_nice K hKnd hK s M hMF
  set P : Matrix (Finset (Finset (Fin 4))) (Finset (Finset (Fin 4))) ℝ :=
    M * kingmanAbsorption with hP
  have hnice : NiceKernel S P := by
    have := hniceK.mul niceKernel_kingmanAbsorption (disjoint_empty_right _)
    rwa [union_empty] at this
  -- the forest at the root of `N`
  have htop : N.forestDist s = C.forestDist s ᵥ* M := by
    rw [Net.forestDist_eq, Net.forestDist_eq, hNK, Net.forestDistOf_bind, ← hM]
    congr 1
    funext o
    cases o <;> rfl
  -- the forests at the top of `C`: at least three lineages, the others are added by `M`
  have hsupp : ∀ F, C.forestDist s F ≠ 0 → IsGood F ∧ Disjoint (lineages F) S ∧
      3 ≤ #(lineages F) ∧ lineages F ∪ S = univ := by
    intro F hF
    rw [Net.forestDist_eq] at hF
    obtain ⟨hFg, -, hFl⟩ := Net.forestDistOf_single_support C hCnd (sampledAt s)
      (fun x _ => isGood_singletons _) (fun x _ y _ hxy => by
        rw [ns_lineages_sampledAt, ns_lineages_sampledAt]
        exact disjoint_filter.2 fun l _ h1 h2 => hxy (h1.symm.trans h2)) hF
    have hlin : lineages F = univ.filter fun l => s l ∈ C.taxa := by
      rw [hFl]
      ext l
      simp [ns_lineages_sampledAt, Net.taxa]
    refine ⟨hFg, ?_, by rwa [hlin], ?_⟩
    · rw [hlin, hS]
      exact disjoint_filter.2 fun l _ hl hlK => hKC _ hlK (by simpa [Net.taxa] using hl)
    · rw [hlin, hS, ← filter_or]
      refine eq_univ_of_forall fun l => mem_filter.2 ⟨mem_univ _, ?_⟩
      have hl := hsN l
      simp only [Net.taxa, List.mem_toFinset] at hl ⊢
      exact ns_context_cover hNK hl
  -- the gene trees: complete good trees on the four lineages
  have hfinal : ∀ F G, IsGood F → Disjoint (lineages F) S →
      lineages F ∪ S = univ → P F G ≠ 0 →
        IsGood G ∧ (univ : Finset (Fin 4)) ∈ G := by
    intro F G hFg hFS hFu hG
    rw [hP, Matrix.mul_apply] at hG
    obtain ⟨H, -, hH⟩ := Finset.exists_ne_zero_of_sum_ne_zero hG
    obtain ⟨hHg, -, hHl⟩ := hniceK.support F hFg hFS H (left_ne_zero_of_mul hH)
    obtain ⟨hGg, -, hGl, hroot⟩ := kingmanAbsorption_support hHg (right_ne_zero_of_mul hH)
    rw [hFu] at hHl
    have hHne : H.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      rw [lineages_empty] at hHl
      exact Finset.univ_nonempty.ne_empty hHl.symm
    refine ⟨hGg, ?_⟩
    have := lineages_mem_of_card_roots_eq_one (hroot hHne)
    rwa [hGl, hHl] at this
  -- the quartet CF
  have hvec : ![s 0, s 1, s 2, s 3] = s := by
    funext i
    fin_cases i <;> rfl
  have hterm : ∀ G, (if ({0, 1} : Finset (Fin 4)) ∈ unroot G then
      (C.forestDist s ᵥ* P) G else 0) =
        ∑ F, C.forestDist s F * (P F G *
          if ({0, 1} : Finset (Fin 4)) ∈ unroot G then 1 else 0) := by
    intro G
    rw [← mul_boole]
    simp only [vecMul, dotProduct, Finset.sum_mul, mul_assoc]
  unfold Net.quartetCF Net.geneTreeDist
  rw [hvec, htop, vecMul_vecMul, ← hP, Finset.sum_congr rfl fun G _ => hterm G, Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.mul_sum]
  by_cases hF : C.forestDist s F = 0
  · rw [hF, zero_mul, zero_mul]
  obtain ⟨hFg, hFS, hF3, hFu⟩ := hsupp F hF
  rw [← hnice.score hFg hFS hF3]
  congr 1
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases hG : P F G = 0
  · rw [hG, zero_mul, zero_mul]
  obtain ⟨hGg, hGu⟩ := hfinal F G hFg hFS hFu hG
  rw [quartetScore_eq_of_univ_mem hGg hGu]

end Phylogenetics
