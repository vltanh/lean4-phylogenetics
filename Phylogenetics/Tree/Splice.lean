module

public import Phylogenetics.Tree.Splits

/-!
# Splicing trees into the vertices of a tree

A construction used by Rhodes, Allman, Ané, Baños (2026) and by Dai, Han, Molloy (2026): at each multifurcation of a tree `T`, with blocks `P`, add a family of sides that are unions of blocks and are
pairwise compatible. The result is a tree resolving `T` that, on quartets with taxa in distinct blocks
of `P`, displays exactly what the family at `P` does.

* `IsBlockUnion`, `IsBlockFamily`: the families that can be added at a vertex;
* `splice`, `splice_isUnrootedTree`, `subset_splice`, `displays_splice_iff`: the construction;
* `liftBlocks`, `isBlockFamily_image_liftBlocks`: the family of the lifts of a tree on the blocks;
* `QuartetTree.map`, `pullTree`, `pullTree_isUnrootedTree`, `displays_pullTree_iff`: restriction of a
  tree along an injection, such as a choice of representatives of the blocks;
* `IsRepTuple`, `exists_isRepTuple`: choices of representatives of the blocks;
* `IsRepTuple.mem_pullTree_iff`, `pullTree_eq_of_forall_mem`, `filter_isBlockUnion_eq_image_pullTree`:
  a tree with the blocks as sides has one restriction to all representatives, whose lifts are its sides
  that are unions of blocks;
* `reattach`, `reattach_isUnrootedTree`, `subset_pullTree_reattach`: replacing that restriction by a
  refinement and reattaching the removed taxa;
* `exists_max_quartetSupport`: a maximizing tree exists;
* `sum_ite_taxa_subset_image`: quartet trees on the image of an injection are those of its domain;

## References

* J. A. Rhodes, E. S. Allman, C. Ané, H. Baños, *Statistical inference of the Tree of Blobs of a
  phylogenetic network from quartet concordance factors*, bioRxiv 10.64898/2026.05.28.728501.
* J. Dai, Y. Han, E. K. Molloy, *Quartet-based species tree methods enable fast and consistent tree of
  blobs reconstruction under the network multispecies coalescent*, Genome Res., doi
  10.1101/gr.282203.126.
-/

@[expose] public noncomputable section

namespace Phylogenetics

open Finset
open scoped Classical

variable {X : Type*} [Fintype X] [DecidableEq X]


/-! ### Sides that are unions of blocks -/

/-- `A` is a union of blocks of `P`: each block lies inside `A` or misses it. -/
def IsBlockUnion (P : Finset (Finset X)) (A : Finset X) : Prop :=
  ∀ B ∈ P, B ⊆ A ∨ Disjoint B A

/-- The sides that can be added to a tree at the vertex with blocks `P`: nonempty and proper unions of
blocks, closed under complement and pairwise compatible. -/
structure IsBlockFamily (P L : Finset (Finset X)) : Prop where
  blockUnion : ∀ A ∈ L, IsBlockUnion P A
  nonempty : ∀ A ∈ L, A.Nonempty
  compl_nonempty : ∀ A ∈ L, Aᶜ.Nonempty
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  compatible : ∀ A ∈ L, ∀ B ∈ L, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B ∨ A ∪ B = univ

/-- A union of blocks at a vertex is compatible with every side of the tree. -/
theorem IsVertexPartition.compatible_of_isBlockUnion {T P : Finset (Finset X)}
    (hP : IsVertexPartition T P) {A C : Finset X} (hA : IsBlockUnion P A) (hC : C ∈ T) :
    A ⊆ C ∨ C ⊆ A ∨ Disjoint A C ∨ A ∪ C = univ := by
  rcases hP.edge_in_block C hC with ⟨B, hB, hCB⟩ | ⟨B, hB, hCB⟩
  · rcases hA B hB with h | h
    · exact Or.inr (Or.inl (hCB.trans h))
    · exact Or.inr (Or.inr (Or.inl (h.mono_left hCB).symm))
  · rcases hA B hB with h | h
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      by_cases hx : x ∈ C
      · exact mem_union_right _ hx
      · exact mem_union_left _ (h (hCB (mem_compl.2 hx)))
    · refine Or.inl fun x hx => ?_
      by_contra hxC
      exact disjoint_left.1 h (hCB (mem_compl.2 hxC)) hx

/-- Unions of blocks at two distinct vertices of a tree are compatible. -/
theorem IsVertexPartition.compatible_of_ne {T P P' : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hP : IsVertexPartition T P) (hP' : IsVertexPartition T P') (hne : P ≠ P') {A A' : Finset X}
    (hA : IsBlockUnion P A) (hA' : IsBlockUnion P' A') :
    A ⊆ A' ∨ A' ⊆ A ∨ Disjoint A A' ∨ A ∪ A' = univ := by
  obtain ⟨B, hB, B', hB', hu⟩ := hP.exists_union_eq_univ hT hP' hne
  have hu' : ∀ x, x ∈ B ∨ x ∈ B' := fun x => mem_union.1 (hu ▸ mem_univ x)
  rcases hA B hB with h | h <;> rcases hA' B' hB' with h' | h'
  · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
    rcases hu' x with hx | hx
    · exact mem_union_left _ (h hx)
    · exact mem_union_right _ (h' hx)
  · refine Or.inr (Or.inl fun x hx => ?_)
    rcases hu' x with hx' | hx'
    · exact h hx'
    · exact absurd hx (disjoint_left.1 h' hx')
  · refine Or.inl fun x hx => ?_
    rcases hu' x with hx' | hx'
    · exact absurd hx (disjoint_left.1 h hx')
    · exact h' hx'
  · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hx hx₂ => ?_)))
    rcases hu' x with hx' | hx'
    · exact disjoint_left.1 h hx' hx
    · exact disjoint_left.1 h' hx' hx₂

/-! ### The splice -/

/-- The tree `T` with, at each multifurcation `P`, the sides `L P` added. -/
def splice (T : Finset (Finset X)) (L : Finset (Finset X) → Finset (Finset X)) :
    Finset (Finset X) :=
  T ∪ (multifurcations T).biUnion L

theorem mem_splice {T : Finset (Finset X)} {L : Finset (Finset X) → Finset (Finset X)}
    {A : Finset X} : A ∈ splice T L ↔ A ∈ T ∨ ∃ P ∈ multifurcations T, A ∈ L P := by
  simp [splice, mem_biUnion]

theorem subset_splice (T : Finset (Finset X)) (L : Finset (Finset X) → Finset (Finset X)) :
    T ⊆ splice T L :=
  subset_union_left

/-- The splice of block families into a tree is a tree. -/
theorem splice_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations T, IsBlockFamily P (L P)) : IsUnrootedTree (splice T L) := by
  by_cases hX : 2 ≤ Fintype.card X
  · have hSF := hT.isSplitFamily hX
    refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact hSF.nonempty A h
      · exact (hL P hP).nonempty A h
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact hSF.compl_nonempty A h
      · exact (hL P hP).compl_nonempty A h
    · intro A hA
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩
      · exact mem_splice.2 (Or.inl (hSF.compl_mem A h))
      · exact mem_splice.2 (Or.inr ⟨P, hP, (hL P hP).compl_mem A h⟩)
    · exact fun x => mem_splice.2 (Or.inl (hSF.singleton_mem x))
    · intro A hA B hB
      rcases mem_splice.1 hA with h | ⟨P, hP, h⟩ <;> rcases mem_splice.1 hB with h' | ⟨P', hP', h'⟩
      · exact hSF.compatible A h B h'
      · exact compatible_symm ((mem_multifurcations.1 hP').1.compatible_of_isBlockUnion
          ((hL P' hP').blockUnion B h') h)
      · exact (mem_multifurcations.1 hP).1.compatible_of_isBlockUnion
          ((hL P hP).blockUnion A h) h'
      · by_cases he : P = P'
        · subst he
          exact (hL P hP).compatible A h B h'
        · exact (mem_multifurcations.1 hP).1.compatible_of_ne hT (mem_multifurcations.1 hP').1 he
            ((hL P hP).blockUnion A h) ((hL P' hP').blockUnion B h')
  · have hM : multifurcations T = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro P hP
      obtain ⟨hV, h4⟩ := mem_multifurcations.1 hP
      obtain ⟨B, hB⟩ := card_pos.1 (show 0 < P.card by omega)
      exact hX (hT.two_le_card_of_mem (hV.mem B hB))
    simpa [splice, hM] using hT

/-- On a quartet with taxa in distinct blocks of a multifurcation `P`, the spliced tree displays
exactly what the family at `P` does. -/
theorem displays_splice_iff {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    {L : Finset (Finset X) → Finset (Finset X)}
    (hL : ∀ P ∈ multifurcations T, IsBlockFamily P (L P)) {P : Finset (Finset X)}
    (hP : P ∈ multifurcations T) {s : QuartetTree X} (hs : InDistinctBlocks P s.taxa) :
    Displays (splice T L) s ↔ ∃ A ∈ L P, A ∩ s.taxa ∈ s.val := by
  constructor
  · rintro ⟨A, hA, hAs⟩
    rcases mem_splice.1 hA with h | ⟨P', hP', h⟩
    · exact absurd ⟨A, h, hAs⟩ (not_displays_of_inDistinctBlocks (mem_multifurcations.1 hP).1 hs)
    · by_cases he : P = P'
      · subst he
        exact ⟨A, h, hAs⟩
      · exfalso
        obtain ⟨B, hB, B', hB', hu⟩ := (mem_multifurcations.1 hP).1.exists_union_eq_univ hT
          (mem_multifurcations.1 hP').1 he
        have hu' : ∀ x, x ∈ B ∨ x ∈ B' := fun x => mem_union.1 (hu ▸ mem_univ x)
        have h1 := hs B hB
        have hc := s.card_of_mem hAs
        have hc' := s.card_of_mem (s.sdiff_mem hAs)
        rcases (hL P' hP').blockUnion A h B' hB' with hsub | hdis
        · have : s.taxa \ (A ∩ s.taxa) ⊆ B ∩ s.taxa := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
            refine mem_inter.2 ⟨?_, hx1⟩
            rcases hu' x with hb | hb
            · exact hb
            · exact absurd (mem_inter.2 ⟨hsub hb, hx1⟩) hx2
          have := card_le_card this
          omega
        · have : A ∩ s.taxa ⊆ B ∩ s.taxa := by
            intro x hx
            obtain ⟨hx1, hx2⟩ := mem_inter.1 hx
            refine mem_inter.2 ⟨?_, hx2⟩
            rcases hu' x with hb | hb
            · exact hb
            · exact absurd hx1 (disjoint_left.1 hdis hb)
          have := card_le_card this
          omega
  · rintro ⟨A, hA, hAs⟩
    exact ⟨A, mem_splice.2 (Or.inr ⟨P, hP, hA⟩), hAs⟩

/-! ### Lifts of trees on the blocks -/

/-- The union of a set of blocks. -/
def liftBlocks (P : Finset (Finset X)) (A : Finset {B // B ∈ P}) : Finset X :=
  A.biUnion Subtype.val

omit [Fintype X] in
theorem mem_liftBlocks {P : Finset (Finset X)} {A : Finset {B // B ∈ P}} {x : X} :
    x ∈ liftBlocks P A ↔ ∃ b ∈ A, x ∈ b.val := by
  simp [liftBlocks, mem_biUnion]

section Lift

variable {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)

include hd

omit [Fintype X] in
/-- The block of a taxon is unique. -/
theorem block_eq_of_mem {b c : {B // B ∈ P}} {x : X} (hb : x ∈ b.val) (hc : x ∈ c.val) : b = c := by
  by_contra hne
  exact disjoint_left.1 (hd b.val b.property c.val c.property fun e => hne (Subtype.ext e)) hb hc

omit [Fintype X] in
theorem mem_liftBlocks_of_mem {A : Finset {B // B ∈ P}} {b : {B // B ∈ P}} {x : X}
    (hx : x ∈ b.val) : x ∈ liftBlocks P A ↔ b ∈ A := by
  rw [mem_liftBlocks]
  constructor
  · rintro ⟨c, hc, hxc⟩
    exact block_eq_of_mem hd hx hxc ▸ hc
  · exact fun hb => ⟨b, hb, hx⟩

omit [Fintype X] in
theorem isBlockUnion_liftBlocks (A : Finset {B // B ∈ P}) : IsBlockUnion P (liftBlocks P A) := by
  intro B hB
  by_cases h : (⟨B, hB⟩ : {B // B ∈ P}) ∈ A
  · exact Or.inl fun x hx => mem_liftBlocks.2 ⟨_, h, hx⟩
  · exact Or.inr (disjoint_left.2 fun x hx hxA =>
      h ((mem_liftBlocks_of_mem hd (b := ⟨B, hB⟩) hx).1 hxA))

end Lift

section LiftTree

variable {P : Finset (Finset X)} (hne : ∀ B ∈ P, B.Nonempty)
  (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ)

theorem exists_block (hcover : P.sup id = univ) (x : X) : ∃ b : {B // B ∈ P}, x ∈ b.val := by
  have : x ∈ P.sup id := hcover ▸ mem_univ x
  obtain ⟨B, hB, hx⟩ : ∃ B ∈ P, x ∈ B := by simpa [mem_sup] using this
  exact ⟨⟨B, hB⟩, hx⟩

include hd hcover in
theorem liftBlocks_compl (A : Finset {B // B ∈ P}) :
    liftBlocks P Aᶜ = (liftBlocks P A)ᶜ := by
  ext x
  obtain ⟨b, hb⟩ := exists_block hcover x
  rw [mem_compl, mem_liftBlocks_of_mem hd hb, mem_liftBlocks_of_mem hd hb, mem_compl]

include hne in
omit [Fintype X] in
theorem liftBlocks_nonempty {A : Finset {B // B ∈ P}} (hA : A.Nonempty) :
    (liftBlocks P A).Nonempty := by
  obtain ⟨b, hb⟩ := hA
  obtain ⟨x, hx⟩ := hne b.val b.property
  exact ⟨x, mem_liftBlocks.2 ⟨b, hb, hx⟩⟩

include hne hd hcover in
/-- The lifts of the sides of a tree on the blocks form a block family. -/
theorem isBlockFamily_image_liftBlocks {T : Finset (Finset {B // B ∈ P})} (hT : IsUnrootedTree T) :
    IsBlockFamily P (T.image (liftBlocks P)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A' hA'
    obtain ⟨A, -, rfl⟩ := mem_image.1 hA'
    exact isBlockUnion_liftBlocks hd A
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    exact liftBlocks_nonempty hne (hT.nonempty_of_mem hA)
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    rw [← liftBlocks_compl hd hcover]
    exact liftBlocks_nonempty hne (hT.nonempty_of_mem (hT.compl_mem hA))
  · intro A' hA'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    rw [← liftBlocks_compl hd hcover]
    exact mem_image_of_mem _ (hT.compl_mem hA)
  · intro A' hA' B' hB'
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    rcases hT.compatible hA hB with h | h | h | h
    · exact Or.inl (biUnion_subset_biUnion_of_subset_left _ h)
    · exact Or.inr (Or.inl (biUnion_subset_biUnion_of_subset_left _ h))
    · refine Or.inr (Or.inr (Or.inl (disjoint_left.2 fun x hx hx' => ?_)))
      obtain ⟨b, hb, hxb⟩ := mem_liftBlocks.1 hx
      exact disjoint_left.1 h hb ((mem_liftBlocks_of_mem hd hxb).1 hx')
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun x => ?_)))
      obtain ⟨b, hb⟩ := exists_block hcover x
      have : b ∈ A ∪ B := h ▸ mem_univ b
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ (mem_liftBlocks.2 ⟨b, h', hb⟩)
      · exact mem_union_right _ (mem_liftBlocks.2 ⟨b, h', hb⟩)

end LiftTree

/-! ### Transport of quartet trees along an injection -/

section Map

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {ι : Y → X} (hι : Function.Injective ι)

/-- The image of a quartet tree under an injection. -/
def QuartetTree.map (hι : Function.Injective ι) (s : QuartetTree Y) : QuartetTree X :=
  ⟨s.val.image fun B => B.image ι, by
    obtain ⟨hc, h2, hd⟩ := s.property
    refine ⟨?_, ?_, ?_⟩
    · rw [card_image_of_injective _ (image_injective hι), hc]
    · intro B' hB'
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      rw [card_image_of_injective _ hι, h2 B hB]
    · intro B' hB' C' hC' hBC
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
      rw [disjoint_image hι]
      exact hd B hB C hC fun e => hBC (e ▸ rfl)⟩

omit [Fintype X] [Fintype Y] in
@[simp] theorem QuartetTree.map_val (s : QuartetTree Y) :
    (s.map hι).val = s.val.image fun B => B.image ι := rfl

omit [Fintype X] [Fintype Y] in
@[simp] theorem QuartetTree.map_taxa (s : QuartetTree Y) : (s.map hι).taxa = s.taxa.image ι := by
  ext x
  simp only [QuartetTree.taxa, QuartetTree.map_val, mem_sup, id, mem_image]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact ⟨y, ⟨B, hB, hy⟩, rfl⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
    exact ⟨_, ⟨B, hB, rfl⟩, mem_image_of_mem _ hy⟩

omit [Fintype X] [Fintype Y] in
theorem QuartetTree.map_injective : Function.Injective (QuartetTree.map (X := X) hι) := by
  intro s s' h
  apply Subtype.ext
  exact image_injective (image_injective hι) (congrArg Subtype.val h)

include hι in
omit [Fintype X] in
/-- A quartet tree on the image of an injection comes from its domain. -/
theorem QuartetTree.exists_map_eq (s : QuartetTree X) (h : s.taxa ⊆ univ.image ι) :
    ∃ s₀ : QuartetTree Y, s₀.map hι = s := by
  let f : Finset X → Finset Y := fun B => univ.filter fun y => ι y ∈ B
  have hf : ∀ B ∈ s.val, (f B).image ι = B := by
    intro B hB
    ext x
    simp only [mem_image, f, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, -, rfl⟩ := mem_image.1 (h (s.subset_taxa hB hx))
      exact ⟨y, hx, rfl⟩
  have hfc : ∀ B ∈ s.val, (f B).card = 2 := fun B hB => by
    rw [← card_image_of_injective _ hι, hf B hB, s.card_of_mem hB]
  have hinj : Set.InjOn f s.val := fun B hB C hC e => by
    rw [← hf B hB, ← hf C hC]
    exact congrArg (image ι) e
  refine ⟨⟨s.val.image f, ?_, ?_, ?_⟩, ?_⟩
  · rw [card_image_of_injOn hinj]
    exact s.property.1
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    exact hfc B hB
  · intro B' hB' C' hC' hBC
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hC'
    have := s.property.2.2 B hB C hC fun e => hBC (e ▸ rfl)
    exact disjoint_left.2 fun y hy hy' =>
      disjoint_left.1 this (mem_filter.1 hy).2 (mem_filter.1 hy').2
  · apply Subtype.ext
    rw [QuartetTree.map_val, image_image]
    ext B
    simp only [mem_image, Function.comp]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rw [hf C hC]
      exact hC
    · exact fun hB => ⟨B, hB, hf B hB⟩

include hι in
/-- Quartet trees on the image of an injection are those of the domain. -/
theorem sum_ite_taxa_subset_image (g : QuartetTree X → ℝ) :
    (∑ s : QuartetTree X, if s.taxa ⊆ univ.image ι then g s else 0) =
      ∑ s₀ : QuartetTree Y, g (s₀.map hι) := by
  rw [← sum_filter]
  have : (univ.filter fun s : QuartetTree X => s.taxa ⊆ univ.image ι) =
      univ.image (QuartetTree.map hι) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact QuartetTree.exists_map_eq hι s h
    · rintro ⟨s₀, rfl⟩
      rw [QuartetTree.map_taxa]
      exact image_subset_image (subset_univ _)
  rw [this, sum_image (fun a _ b _ h => QuartetTree.map_injective hι h)]

/-- The restriction of a tree along an injection. -/
def pullTree (ι : Y → X) (T : Finset (Finset X)) : Finset (Finset Y) :=
  (T.image fun A => univ.filter fun y => ι y ∈ A).filter fun A => A.Nonempty ∧ Aᶜ.Nonempty

omit [Fintype X] in
theorem mem_pullTree {T : Finset (Finset X)} {A : Finset Y} :
    A ∈ pullTree ι T ↔ (∃ C ∈ T, (univ.filter fun y => ι y ∈ C) = A) ∧ A.Nonempty ∧ Aᶜ.Nonempty := by
  simp [pullTree, mem_filter, mem_image]

include hι in
/-- The restriction of a tree along an injection, from at least two taxa, is a tree. -/
theorem pullTree_isUnrootedTree {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hY : 2 ≤ Fintype.card Y) : IsUnrootedTree (pullTree ι T) := by
  have hX : 2 ≤ Fintype.card X := hY.trans (Fintype.card_le_of_injective ι hι)
  have hSF := hT.isSplitFamily hX
  refine (isUnrootedTree_iff hY _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun A hA => (mem_pullTree.1 hA).2.1
  · exact fun A hA => (mem_pullTree.1 hA).2.2
  · intro A hA
    obtain ⟨⟨C, hC, rfl⟩, h1, h2⟩ := mem_pullTree.1 hA
    refine mem_pullTree.2 ⟨⟨Cᶜ, hSF.compl_mem C hC, ?_⟩, h2, by rwa [compl_compl]⟩
    ext y
    simp
  · intro y
    refine mem_pullTree.2 ⟨⟨{ι y}, hSF.singleton_mem _, ?_⟩, singleton_nonempty y, ?_⟩
    · ext z
      simp [hι.eq_iff]
    · rw [← card_pos, card_compl, card_singleton]
      omega
  · intro A hA B hB
    obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 hA
    obtain ⟨⟨D, hD, rfl⟩, -, -⟩ := mem_pullTree.1 hB
    rcases hSF.compatible C hC D hD with h | h | h | h
    · exact Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩
    · exact Or.inr (Or.inl fun y hy => mem_filter.2 ⟨mem_univ y, h (mem_filter.1 hy).2⟩)
    · exact Or.inr (Or.inr (Or.inl (disjoint_left.2 fun y hy hy' =>
        disjoint_left.1 h (mem_filter.1 hy).2 (mem_filter.1 hy').2)))
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
      have : ι y ∈ C ∪ D := h ▸ mem_univ _
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ y, h'⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ y, h'⟩)

omit [Fintype X] in
/-- The restriction of a tree along an injection displays what the tree does. -/
theorem displays_pullTree_iff {T : Finset (Finset X)} (s₀ : QuartetTree Y) :
    Displays (pullTree ι T) s₀ ↔ Displays T (s₀.map hι) := by
  have hpre : ∀ A : Finset X, ((univ.filter fun y => ι y ∈ A) ∩ s₀.taxa).image ι =
      A ∩ s₀.taxa.image ι := by
    intro A
    ext x
    simp only [mem_image, mem_inter, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, y, h2, rfl⟩
    · rintro ⟨h1, y, h2, rfl⟩
      exact ⟨y, ⟨h1, h2⟩, rfl⟩
  constructor
  · rintro ⟨A, hA, hAs⟩
    obtain ⟨⟨C, hC, rfl⟩, -, -⟩ := mem_pullTree.1 hA
    refine ⟨C, hC, ?_⟩
    rw [QuartetTree.map_taxa, ← hpre C, QuartetTree.map_val]
    exact mem_image_of_mem _ hAs
  · rintro ⟨A, hA, hAs⟩
    rw [QuartetTree.map_taxa, QuartetTree.map_val, mem_image] at hAs
    obtain ⟨C, hC, hCe⟩ := hAs
    have hCA : (univ.filter fun y => ι y ∈ A) ∩ s₀.taxa = C :=
      image_injective hι (by rw [hpre, hCe])
    have hCc := s₀.card_of_mem hC
    have hCc' := s₀.card_of_mem (s₀.sdiff_mem hC)
    refine ⟨univ.filter fun y => ι y ∈ A, mem_pullTree.2 ⟨⟨A, hA, rfl⟩, ?_, ?_⟩, hCA ▸ hC⟩
    · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < C.card by omega)
      exact ⟨y, (mem_inter.1 (hCA ▸ hy)).1⟩
    · obtain ⟨y, hy⟩ := card_pos.1 (show 0 < (s₀.taxa \ C).card by omega)
      refine ⟨y, mem_compl.2 fun hyA => ?_⟩
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hy
      exact h2 (hCA ▸ mem_inter.2 ⟨hyA, h1⟩)

end Map

/-! ### Representatives of the blocks -/

section Rep

variable {P : Finset (Finset X)}

/-- A choice of a taxon in each block. -/
def IsRepTuple (P : Finset (Finset X)) (x : {B // B ∈ P} → X) : Prop := ∀ b, x b ∈ b.val

omit [Fintype X] [DecidableEq X] in
theorem exists_isRepTuple (hne : ∀ B ∈ P, B.Nonempty) : ∃ x, IsRepTuple P x :=
  ⟨fun b => (hne b.val b.property).choose, fun b => (hne b.val b.property).choose_spec⟩

variable (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) {x : {B // B ∈ P} → X} (hx : IsRepTuple P x)

include hd hx

omit [Fintype X] in
theorem IsRepTuple.injective : Function.Injective x := fun b c h =>
  block_eq_of_mem hd (hx b) (h ▸ hx c)

omit [Fintype X] in
/-- Taxa among the representatives of the blocks lie in distinct blocks. -/
theorem IsRepTuple.inDistinctBlocks {q : Finset X} (hq : q ⊆ univ.image x) :
    InDistinctBlocks P q := by
  intro B hB
  refine card_le_one.2 fun y hy z hz => ?_
  obtain ⟨hyB, hyq⟩ := mem_inter.1 hy
  obtain ⟨hzB, hzq⟩ := mem_inter.1 hz
  obtain ⟨b, -, rfl⟩ := mem_image.1 (hq hyq)
  obtain ⟨c, -, rfl⟩ := mem_image.1 (hq hzq)
  have h1 : b = ⟨B, hB⟩ := block_eq_of_mem hd (hx b) hyB
  have h2 : c = ⟨B, hB⟩ := block_eq_of_mem hd (hx c) hzB
  rw [h1, h2]

omit [Fintype X] in
/-- On the representatives, a lift traces the corresponding set of blocks. -/
theorem IsRepTuple.liftBlocks_inter_image (A D : Finset {B // B ∈ P}) :
    liftBlocks P A ∩ D.image x = (A ∩ D).image x := by
  ext y
  simp only [mem_inter, mem_image]
  constructor
  · rintro ⟨h1, b, hb, rfl⟩
    exact ⟨b, ⟨(mem_liftBlocks_of_mem hd (hx b)).1 h1, hb⟩, rfl⟩
  · rintro ⟨b, ⟨h1, h2⟩, rfl⟩
    exact ⟨(mem_liftBlocks_of_mem hd (hx b)).2 h1, b, h2, rfl⟩

end Rep

/-! ### Restricting a tree that has the blocks as sides -/

section Restrict

variable {P : Finset (Finset X)} (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C)
  {x : {B // B ∈ P} → X} (hx : IsRepTuple P x)

omit [Fintype X] in
@[simp] theorem liftBlocks_singleton (b : {B // B ∈ P}) : liftBlocks P {b} = b.val := by
  simp [liftBlocks]

include hd hx

omit [Fintype X] in
/-- A lift, restricted to representatives, is the set of blocks that was lifted. -/
theorem IsRepTuple.filter_mem_liftBlocks (A : Finset {B // B ∈ P}) :
    (univ.filter fun b => x b ∈ liftBlocks P A) = A := by
  ext b
  simp only [mem_filter, mem_univ, true_and]
  exact mem_liftBlocks_of_mem hd (hx b)

/-- A union of blocks is the lift of the set of blocks whose representatives it contains. -/
theorem IsRepTuple.liftBlocks_filter_mem (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) : liftBlocks P (univ.filter fun b => x b ∈ C) = C := by
  ext y
  obtain ⟨b, hb⟩ := exists_block hcover y
  rw [mem_liftBlocks_of_mem hd hb]
  simp only [mem_filter, mem_univ, true_and]
  rcases hC b.val b.property with h | h
  · exact iff_of_true (h (hx b)) (h hb)
  · exact iff_of_false (disjoint_left.1 h (hx b)) (disjoint_left.1 h hb)

omit hd in
/-- A nonempty union of blocks contains a representative. -/
theorem IsRepTuple.filter_mem_nonempty (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) (hne : C.Nonempty) : (univ.filter fun b => x b ∈ C).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨b, hb⟩ := exists_block hcover y
  rcases hC b.val b.property with h | h
  · exact ⟨b, mem_filter.2 ⟨mem_univ b, h (hx b)⟩⟩
  · exact absurd hy (disjoint_left.1 h hb)

omit hd in
/-- A union of blocks with a nonempty complement misses a representative. -/
theorem IsRepTuple.compl_filter_mem_nonempty (hcover : P.sup id = univ) {C : Finset X}
    (hC : IsBlockUnion P C) (hne : Cᶜ.Nonempty) : (univ.filter fun b => x b ∈ C)ᶜ.Nonempty := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨b, hb⟩ := exists_block hcover y
  rcases hC b.val b.property with h | h
  · exact absurd (h hb) (mem_compl.1 hy)
  · exact ⟨b, mem_compl.2 fun hb' => disjoint_left.1 h (hx b) (mem_filter.1 hb').2⟩

omit hd hx in
/-- A side of a tree with the blocks of `P` as sides is a union of blocks, or it or its complement
lies inside a block. -/
theorem IsUnrootedTree.isBlockUnion_or {T : Finset (Finset X)} (hT : IsUnrootedTree T)
    (hall : ∀ B ∈ P, B ∈ T) {C : Finset X} (hC : C ∈ T) :
    IsBlockUnion P C ∨ (∃ B ∈ P, C ⊆ B) ∨ ∃ B ∈ P, C ∪ B = univ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  unfold IsBlockUnion at h1
  push Not at h1
  obtain ⟨B, hB, hnot1, hnot2⟩ := h1
  rcases hT.compatible hC (hall B hB) with h | h | h | h
  · exact h2 B hB h
  · exact hnot1 h
  · exact hnot2 h.symm
  · exact h3 B hB h

/-- The restriction to representatives of a tree with the blocks as sides, without mentioning the
representatives: its sides are the sets of blocks whose lifts are sides of the tree. -/
theorem IsRepTuple.mem_pullTree_iff (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) {A : Finset {B // B ∈ P}} :
    A ∈ pullTree x T ↔ liftBlocks P A ∈ T ∧ A.Nonempty ∧ Aᶜ.Nonempty := by
  constructor
  · intro hA
    obtain ⟨⟨C, hC, hCA⟩, h1, h2⟩ := mem_pullTree.1 hA
    refine ⟨?_, h1, h2⟩
    rcases hT.isBlockUnion_or hall hC with hU | ⟨B, hB, hsub⟩ | ⟨B, hB, hu⟩
    · rw [← hCA, hx.liftBlocks_filter_mem hd hcover hU]
      exact hC
    · have hAe : A = {⟨B, hB⟩} := by
        have key : ∀ c ∈ A, c = ⟨B, hB⟩ := fun c hc => by
          rw [← hCA] at hc
          exact block_eq_of_mem hd (hx c) (hsub (mem_filter.1 hc).2)
        obtain ⟨b, hb⟩ := h1
        ext c
        rw [mem_singleton]
        exact ⟨key c, fun e => e ▸ key b hb ▸ hb⟩
      rw [hAe, liftBlocks_singleton]
      exact hall B hB
    · have hAe : Aᶜ = {⟨B, hB⟩} := by
        have key : ∀ c ∈ Aᶜ, c = ⟨B, hB⟩ := fun c hc => by
          have hxc : x c ∉ C := fun h =>
            mem_compl.1 hc (hCA ▸ mem_filter.2 ⟨mem_univ c, h⟩)
          have hxu : x c ∈ C ∪ B := hu ▸ mem_univ _
          exact block_eq_of_mem hd (hx c) ((mem_union.1 hxu).resolve_left hxc)
        obtain ⟨b, hb⟩ := h2
        ext c
        rw [mem_singleton]
        exact ⟨key c, fun e => e ▸ key b hb ▸ hb⟩
      rw [← compl_compl A, hAe, liftBlocks_compl hd hcover, liftBlocks_singleton]
      exact hT.compl_mem (hall B hB)
  · rintro ⟨h1, h2, h3⟩
    exact mem_pullTree.2 ⟨⟨_, h1, hx.filter_mem_liftBlocks hd A⟩, h2, h3⟩

omit hx in
/-- A tree with the blocks as sides has the same restriction to any choice of representatives. -/
theorem pullTree_eq_of_forall_mem (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) {x x' : {B // B ∈ P} → X}
    (hx : IsRepTuple P x) (hx' : IsRepTuple P x') : pullTree x T = pullTree x' T := by
  ext A
  rw [hx.mem_pullTree_iff hd hcover hT hall, hx'.mem_pullTree_iff hd hcover hT hall]

/-- For a tree with the blocks as sides, the sides that are unions of blocks are the lifts of its
restriction to representatives. -/
theorem filter_isBlockUnion_eq_image_pullTree (hcover : P.sup id = univ) {T : Finset (Finset X)}
    (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T) :
    T.filter (IsBlockUnion P) = (pullTree x T).image (liftBlocks P) := by
  ext A
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hA, hU⟩
    refine ⟨univ.filter fun b => x b ∈ A, mem_pullTree.2 ⟨⟨A, hA, rfl⟩,
      hx.filter_mem_nonempty hcover hU (hT.nonempty_of_mem hA),
      hx.compl_filter_mem_nonempty hcover hU (hT.nonempty_of_mem (hT.compl_mem hA))⟩,
      hx.liftBlocks_filter_mem hd hcover hU⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨((hx.mem_pullTree_iff hd hcover hT hall).1 hC).1, isBlockUnion_liftBlocks hd C⟩

end Restrict

/-! ### Reattaching the taxa removed by a restriction -/

section Reattach

variable {P : Finset (Finset X)}

/-- The tree `T`, with the blocks of `P` as sides, after replacing its restriction to representatives
of the blocks by a refinement `R` and reattaching the removed taxa: each leaf of `R` is replaced by the
subtree of `T` on that block. The sides of `T` inside a block stay, and the sides of `T` that are unions
of blocks are lifts of sides of `R`. -/
def reattach (P : Finset (Finset X)) (T : Finset (Finset X)) (R : Finset (Finset {B // B ∈ P})) :
    Finset (Finset X) :=
  T ∪ R.image (liftBlocks P)

omit [Fintype X] in
theorem subset_reattach (T : Finset (Finset X)) (R : Finset (Finset {B // B ∈ P})) :
    T ⊆ reattach P T R :=
  subset_union_left

variable (hd : ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) (hcover : P.sup id = univ)
  {T : Finset (Finset X)} (hT : IsUnrootedTree T) (hall : ∀ B ∈ P, B ∈ T)
  {R : Finset (Finset {B // B ∈ P})} (hR : IsUnrootedTree R)
  {x : {B // B ∈ P} → X} (hx : IsRepTuple P x) (hsub : pullTree x T ⊆ R)

include hd hcover hT hall hR hx hsub in
private theorem compatible_liftBlocks_of_mem {A : Finset X} (hA : A ∈ T) {C : Finset {B // B ∈ P}}
    (hC : C ∈ R) :
    A ⊆ liftBlocks P C ∨ liftBlocks P C ⊆ A ∨ Disjoint A (liftBlocks P C) ∨
      A ∪ liftBlocks P C = univ := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT.nonempty_of_mem (hall B hB)
  have hfam := isBlockFamily_image_liftBlocks hne hd hcover hR
  rcases hT.isBlockUnion_or hall hA with hU | ⟨B, hB, hAB⟩ | ⟨B, hB, hu⟩
  · have hmem : (univ.filter fun b => x b ∈ A) ∈ R := hsub (mem_pullTree.2 ⟨⟨A, hA, rfl⟩,
      hx.filter_mem_nonempty hcover hU (hT.nonempty_of_mem hA),
      hx.compl_filter_mem_nonempty hcover hU (hT.nonempty_of_mem (hT.compl_mem hA))⟩)
    have := hfam.compatible _ (mem_image_of_mem _ hmem) _ (mem_image_of_mem _ hC)
    rwa [hx.liftBlocks_filter_mem hd hcover hU] at this
  · rcases isBlockUnion_liftBlocks hd C B hB with h | h
    · exact Or.inl (hAB.trans h)
    · exact Or.inr (Or.inr (Or.inl (h.mono_left hAB)))
  · rcases isBlockUnion_liftBlocks hd C B hB with h | h
    · refine Or.inr (Or.inr (Or.inr (eq_univ_iff_forall.2 fun y => ?_)))
      have : y ∈ A ∪ B := hu ▸ mem_univ y
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ h'
      · exact mem_union_right _ (h h')
    · refine Or.inr (Or.inl fun y hy => ?_)
      have : y ∈ A ∪ B := hu ▸ mem_univ y
      rcases mem_union.1 this with h' | h'
      · exact h'
      · exact absurd hy (disjoint_left.1 h h')

include hd hcover hT hall hR hx hsub in
/-- Reattaching the removed taxa to a refinement of the restriction gives a tree. -/
theorem reattach_isUnrootedTree (hP : 2 ≤ P.card) : IsUnrootedTree (reattach P T R) := by
  have hne : ∀ B ∈ P, B.Nonempty := fun B hB => hT.nonempty_of_mem (hall B hB)
  have hfam := isBlockFamily_image_liftBlocks hne hd hcover hR
  have hX : 2 ≤ Fintype.card X :=
    (by rwa [Fintype.card_coe] : 2 ≤ Fintype.card {B // B ∈ P}).trans
      (Fintype.card_le_of_injective x (hx.injective hd))
  have hSF := hT.isSplitFamily hX
  have hmem : ∀ A, A ∈ reattach P T R ↔ A ∈ T ∨ A ∈ R.image (liftBlocks P) := fun A => mem_union
  have hcompat : ∀ A ∈ T, ∀ A' ∈ R.image (liftBlocks P),
      A ⊆ A' ∨ A' ⊆ A ∨ Disjoint A A' ∨ A ∪ A' = univ := by
    intro A hA A' hA'
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hA'
    exact compatible_liftBlocks_of_mem hd hcover hT hall hR hx hsub hA hC
  refine (isUnrootedTree_iff hX _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact hSF.nonempty A h
    · exact hfam.nonempty A h
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact hSF.compl_nonempty A h
    · exact hfam.compl_nonempty A h
  · intro A hA
    rcases (hmem A).1 hA with h | h
    · exact (hmem _).2 (Or.inl (hSF.compl_mem A h))
    · exact (hmem _).2 (Or.inr (hfam.compl_mem A h))
  · exact fun y => (hmem _).2 (Or.inl (hSF.singleton_mem y))
  · intro A hA B hB
    rcases (hmem A).1 hA with h | h <;> rcases (hmem B).1 hB with h' | h'
    · exact hSF.compatible A h B h'
    · exact hcompat A h B h'
    · exact compatible_symm (hcompat B h' A h)
    · exact hfam.compatible A h B h'

include hd hR in
omit [Fintype X] in
/-- The restriction of the reattached tree to any representatives contains the refinement. -/
theorem subset_pullTree_reattach {y : {B // B ∈ P} → X} (hy : IsRepTuple P y) :
    R ⊆ pullTree y (reattach P T R) := fun C hC =>
  mem_pullTree.2 ⟨⟨liftBlocks P C, mem_union_right _ (mem_image_of_mem _ hC),
    hy.filter_mem_liftBlocks hd C⟩, hR.nonempty_of_mem hC, hR.nonempty_of_mem (hR.compl_mem hC)⟩

end Reattach

/-- If there is a tree, the score of any weights has a maximizing tree. -/
theorem exists_max_quartetSupport {T₀ : Finset (Finset X)} (hT₀ : IsUnrootedTree T₀)
    (w : QuartetTree X → ℝ) :
    ∃ T, IsUnrootedTree T ∧ ∀ T', IsUnrootedTree T' → quartetSupport w T' ≤ quartetSupport w T := by
  obtain ⟨T, hT, hmax⟩ := (univ.filter fun T : Finset (Finset X) => IsUnrootedTree T).exists_max_image
    (quartetSupport w) ⟨T₀, by simpa using hT₀⟩
  exact ⟨T, (mem_filter.1 hT).2, fun T' hT' => hmax T' (by simpa using hT')⟩

end Phylogenetics
