module

public import Phylogenetics.NMSC.Glue
public import Phylogenetics.NMSC.Level1.Displays
public import Phylogenetics.Network.Level1.ToRootedNetwork
public import Phylogenetics.Tree.Splits

/-!
# The term-based coalescent is the general one

The network multispecies coalescent on a well-formed term `N : Net X`, `Net.geneTreeDist`, is the
general coalescent `Phylogenetics.geneTreeDist` on the rooted network of its graph, at inheritance
correlation `0`.

The proof follows the term. At each constructor the graph of the term is glued from the graphs of its
parts (`MetricDigraph.IsGluedGraph`), and `NMSC.IsGlued.rootDist_eq_unit` and
`NMSC.IsGlued.rootDist_eq_bool` compute the law at its root from the laws on those parts.

## Main results

* `MetricDigraph.law_stem`, `MetricDigraph.law_tree`, `MetricDigraph.law_glue_bool`: the laws on glued
  graphs.
* `Net.law_toGraph`, `Side.law_toGraph`: the law on the graph of a term is `Net.forestDist`.
* `Net.geneTreeDist_toRootedNetwork`: the theorem.
* `Net.nmscCF_toRootedNetwork`: the quartet concordance factors of the two coalescents agree, so
  `Phylogenetics.nmsc_quartetCF` computes `Phylogenetics.nmscCF` on the cycles of a term.
-/

@[expose] public noncomputable section

open Finset Matrix
open scoped Classical

namespace Phylogenetics

set_option linter.unusedSectionVars false

namespace MetricDigraph

universe u

variable {X : Type u} {L : Type*} [Fintype L] [DecidableEq L]

section Pieces

variable {V : Type} [Fintype V] (G : MetricDigraph V X)

/-- Another arc enters the target of the arc `e`. -/
def HasOtherParent (e : G.Arc) : Prop := ∃ u, u ≠ e.1.1 ∧ G.Adj u e.1.2

/-- The inheritance probability of an arc of a graph: its given value if another arc enters the same
vertex, and otherwise one. -/
def pieceInh (e : G.Arc) : ℝ := if G.HasOtherParent e then G.inh e.1.1 e.1.2 else 1

variable {G} in
theorem pieceInh_eq {V' : Type} {G' : MetricDigraph V' X} {e : G.Arc} {e' : G'.Arc}
    (hraw : G.inh e.1.1 e.1.2 = G'.inh e'.1.1 e'.1.2)
    (h : G.HasOtherParent e ↔ G'.HasOtherParent e') : G.pieceInh e = G'.pieceInh e' := by
  unfold pieceInh
  simp only [h, hraw]

/-- The numerical parameters of a graph. -/
def pieceData : RootedNetwork.MetricData G.Arc where
  length e := G.len e.1.1 e.1.2
  inheritance := G.pieceInh

/-- A graph with a root, as a network whose taxa play no role. -/
def pieceNetwork (r : V) : RootedNetwork V G.Arc L := ⟨G.toMultigraph, r, fun _ => r⟩

/-- The law of the forest arriving at the root of a graph, at inheritance correlation `0`. -/
def law (r : V) (inj : V → Finset (Finset L)) (F : Finset (Finset L)) : ℝ :=
  NMSC.rootDist (G.pieceNetwork r) G.pieceData 0 inj F

end Pieces

/-! ### Gluing graphs -/

section Gluing

variable {T V₀ V₁ P : Type} [Fintype T] [Fintype V₀] [Fintype V₁] [Fintype P]

/-- The graph `W` is made of the upper graph `G₀` and the lower graph `G₁`, joined by one arc from each
vertex `s p` of the upper graph into the vertex `r₁` of the lower graph, of length `ℓ p`. -/
structure IsGluedGraph (W : MetricDigraph T X) (G₀ : MetricDigraph V₀ X) (G₁ : MetricDigraph V₁ X)
    (fV : V₀ ⊕ V₁ ≃ T) (r₁ : V₁) (s : P → V₀) (ℓ : P → ℝ) : Prop where
  adj₀ : ∀ u v, W.Adj (fV (.inl u)) (fV (.inl v)) ↔ G₀.Adj u v
  adj₁ : ∀ u v, W.Adj (fV (.inr u)) (fV (.inr v)) ↔ G₁.Adj u v
  adj₀₁ : ∀ u v, W.Adj (fV (.inl u)) (fV (.inr v)) ↔ v = r₁ ∧ ∃ p, s p = u
  adj₁₀ : ∀ u v, ¬ W.Adj (fV (.inr u)) (fV (.inl v))
  s_inj : Function.Injective s
  not_adj_root : ∀ u, ¬ G₁.Adj u r₁
  len₀ : ∀ u v, G₀.Adj u v → W.len (fV (.inl u)) (fV (.inl v)) = G₀.len u v
  len₁ : ∀ u v, G₁.Adj u v → W.len (fV (.inr u)) (fV (.inr v)) = G₁.len u v
  lenP : ∀ p, W.len (fV (.inl (s p))) (fV (.inr r₁)) = ℓ p
  inh₀ : ∀ u v, G₀.Adj u v → W.inh (fV (.inl u)) (fV (.inl v)) = G₀.inh u v
  inh₁ : ∀ u v, G₁.Adj u v → W.inh (fV (.inr u)) (fV (.inr v)) = G₁.inh u v

namespace IsGluedGraph

variable {W : MetricDigraph T X} {G₀ : MetricDigraph V₀ X} {G₁ : MetricDigraph V₁ X}
  {fV : V₀ ⊕ V₁ ≃ T} {r₁ : V₁} {s : P → V₀} {ℓ : P → ℝ} (hg : IsGluedGraph W G₀ G₁ fV r₁ s ℓ)
include hg

/-- The arcs of the glued graph. -/
def arcEquiv : G₀.Arc ⊕ P ⊕ G₁.Arc ≃ W.Arc :=
  Equiv.ofBijective
    (fun x => match x with
      | .inl e => ⟨(fV (.inl e.1.1), fV (.inl e.1.2)), (hg.adj₀ _ _).2 e.2⟩
      | .inr (.inl p) => ⟨(fV (.inl (s p)), fV (.inr r₁)), (hg.adj₀₁ _ _).2 ⟨rfl, p, rfl⟩⟩
      | .inr (.inr e) => ⟨(fV (.inr e.1.1), fV (.inr e.1.2)), (hg.adj₁ _ _).2 e.2⟩)
    (by
      constructor
      · rintro (a | p | a) (b | q | b) h <;> have h' := congrArg Subtype.val h <;>
          simp only [Prod.mk.injEq, fV.injective.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
            false_and, and_false] at h'
        · congr
          exact Subtype.ext (Prod.ext h'.1 h'.2)
        · rw [hg.s_inj h'.1]
        · congr
          exact Subtype.ext (Prod.ext h'.1 h'.2)
      · rintro ⟨⟨x, y⟩, h⟩
        obtain ⟨x, rfl⟩ := fV.surjective x
        obtain ⟨y, rfl⟩ := fV.surjective y
        rcases x with u | u <;> rcases y with v | v
        · exact ⟨.inl ⟨(u, v), (hg.adj₀ _ _).1 h⟩, rfl⟩
        · obtain ⟨rfl, p, rfl⟩ := (hg.adj₀₁ _ _).1 h
          exact ⟨.inr (.inl p), rfl⟩
        · exact absurd h (hg.adj₁₀ _ _)
        · exact ⟨.inr (.inr ⟨(u, v), (hg.adj₁ _ _).1 h⟩), rfl⟩)

theorem pieceInh_upper (e : G₀.Arc) : W.pieceInh (hg.arcEquiv (.inl e)) = G₀.pieceInh e := by
  refine pieceInh_eq (hg.inh₀ _ _ e.2) ?_
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨x, rfl⟩ := fV.surjective x
    rcases x with u | u
    · exact ⟨u, fun h' => hx (by rw [h']; rfl), (hg.adj₀ _ _).1 h⟩
    · exact absurd h (hg.adj₁₀ _ _)
  · rintro ⟨u, hu, h⟩
    exact ⟨fV (.inl u), fun h' => hu (Sum.inl.inj (fV.injective h')), (hg.adj₀ _ _).2 h⟩

theorem pieceInh_lower (e : G₁.Arc) : W.pieceInh (hg.arcEquiv (.inr (.inr e))) = G₁.pieceInh e := by
  refine pieceInh_eq (hg.inh₁ _ _ e.2) ?_
  have hne : e.1.2 ≠ r₁ := fun h => hg.not_adj_root e.1.1 (h ▸ e.2)
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨x, rfl⟩ := fV.surjective x
    rcases x with u | u
    · exact absurd ((hg.adj₀₁ _ _).1 h).1 hne
    · exact ⟨u, fun h' => hx (by rw [h']; rfl), (hg.adj₁ _ _).1 h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨fV (.inr u), fun h' => hu (Sum.inr.inj (fV.injective h')), (hg.adj₁ _ _).2 h⟩

/-- The structure of a glued network. -/
theorem isGlued (r₀ : V₀) :
    NMSC.IsGlued (W.pieceNetwork (fV (.inl r₀)) : RootedNetwork T W.Arc L) W.pieceData
      (G₀.pieceNetwork r₀) G₀.pieceData (G₁.pieceNetwork r₁) G₁.pieceData fV hg.arcEquiv s ℓ where
  source₀ _ := rfl
  target₀ _ := rfl
  sourceP _ := rfl
  targetP _ := rfl
  source₁ _ := rfl
  target₁ _ := rfl
  root := rfl
  not_target_root e h := by
    obtain ⟨⟨u, v⟩, hu⟩ := e
    obtain rfl : v = r₁ := h
    exact hg.not_adj_root u hu
  length₀ e := hg.len₀ _ _ e.2
  lengthP p := hg.lenP p
  length₁ e := hg.len₁ _ _ e.2
  inheritance₀ e := hg.pieceInh_upper e
  inheritance₁ e := hg.pieceInh_lower e

end IsGluedGraph

variable {W : MetricDigraph T X} {G₀ : MetricDigraph V₀ X} {G₁ : MetricDigraph V₁ X}
  {fV : V₀ ⊕ V₁ ≃ T} {r₁ : V₁}

/-- The law at the root of a graph glued along one arc. -/
theorem law_glue_unit {s : Unit → V₀} {ℓ : Unit → ℝ} (hg : IsGluedGraph W G₀ G₁ fV r₁ s ℓ) (r₀ : V₀)
    (inj : T → Finset (Finset L)) (F : Finset (Finset L)) :
    W.law (fV (.inl r₀)) inj F =
      ∑ t, (∑ F₁, G₁.law r₁ (fun v => inj (fV (.inr v))) F₁ * kingmanTransition (ℓ ()) F₁ t) *
        G₀.law r₀ (NMSC.upperInj fV s inj fun _ => t) F := by
  refine (hg.isGlued r₀).rootDist_eq_unit le_rfl ?_ inj F
  change W.pieceInh _ = 1
  refine ite_eq_right ?_
  rintro ⟨x, hx, h⟩
  obtain ⟨x, rfl⟩ := fV.surjective x
  rcases x with u | u
  · obtain ⟨-, p, rfl⟩ := (hg.adj₀₁ _ _).1 h
    exact hx rfl
  · exact hg.not_adj_root _ ((hg.adj₁ _ _).1 h)

/-- The law at the root of a graph glued along the two arcs entering a reticulation. -/
theorem law_glue_bool {s : Bool → V₀} {ℓ : Bool → ℝ} (hg : IsGluedGraph W G₀ G₁ fV r₁ s ℓ) (r₀ : V₀)
    {γ : ℝ} (h₁ : W.inh (fV (.inl (s false))) (fV (.inr r₁)) = γ)
    (h₂ : W.inh (fV (.inl (s true))) (fV (.inr r₁)) = 1 - γ) (inj : T → Finset (Finset L))
    (F : Finset (Finset L)) :
    W.law (fV (.inl r₀)) inj F =
      ∑ F₁, G₁.law r₁ (fun v => inj (fV (.inr v))) F₁ * ∑ A ∈ (roots F₁).powerset,
        γ ^ #A * (1 - γ) ^ #(roots F₁ \ A) * ∑ t₁, ∑ t₂,
          kingmanTransition (ℓ false) (forestBelow F₁ A) t₁ *
            kingmanTransition (ℓ true) (forestBelow F₁ (roots F₁ \ A)) t₂ *
              G₀.law r₀ (NMSC.upperInj fV s inj fun p => cond p t₂ t₁) F := by
  have hother : ∀ p, W.HasOtherParent (hg.arcEquiv (.inr (.inl p))) := fun p =>
    ⟨fV (.inl (s !p)), fun h => by simpa using hg.s_inj (Sum.inl.inj (fV.injective h)),
      (hg.adj₀₁ _ _).2 ⟨rfl, !p, rfl⟩⟩
  refine (hg.isGlued r₀).rootDist_eq_bool ?_ ?_ inj F
  · change W.pieceInh _ = γ
    exact (ite_eq_left (hother false)).trans h₁
  · change W.pieceInh _ = 1 - γ
    exact (ite_eq_left (hother true)).trans h₂

/-- The law of the forest at the top of an arc of length `ℓ` above the root `r` of a graph. -/
def up (G : MetricDigraph V₁ X) (r : V₁) (inj : V₁ → Finset (Finset L)) (ℓ : ℝ)
    (t : Finset (Finset L)) : ℝ :=
  ∑ F, G.law r inj F * kingmanTransition ℓ F t

/-- The graph with one vertex and no edges. -/
def pointG : MetricDigraph Unit X where
  Adj _ _ := False
  label _ := none
  len _ _ := 0
  inh _ _ := 0

/-- On a graph with one vertex and no edges, the law is the forest injected there. -/
theorem law_of_unit {G : MetricDigraph Unit X} (hG : ∀ u v, ¬ G.Adj u v)
    (inj : Unit → Finset (Finset L)) (F : Finset (Finset L)) :
    G.law () inj F = if inj () = F then 1 else 0 := by
  have hE : IsEmpty G.Arc := ⟨fun e => hG _ _ e.2⟩
  have hs : ∀ (inst : Fintype (G.Arc → Finset (Finset L))) (g : (G.Arc → Finset (Finset L)) → ℝ),
      @Finset.sum _ ℝ _ (@univ _ inst) g = g fun e => hE.elim e := by
    intro inst g
    rw [Finset.eq_singleton_iff_unique_mem.2 (⟨mem_univ _, fun x _ =>
      funext fun e => hE.elim e⟩ : (fun e => hE.elim e) ∈ @univ _ inst ∧ _), sum_singleton]
  have h1 : ∀ b t, NMSC.injWeight (G.pieceNetwork () : RootedNetwork Unit G.Arc L) G.pieceData 0
      inj b t = 1 := by
    intro b t
    refine prod_eq_one fun v hv => ?_
    simp at hv
  have h2 : ∀ t, NMSC.arriving (G.pieceNetwork () : RootedNetwork Unit G.Arc L) inj t () = inj () := by
    intro t
    ext A
    simp only [NMSC.arriving, mem_union, mem_biUnion, mem_filter]
    constructor
    · rintro (h | ⟨e, -, -⟩)
      · exact h
      · exact hE.elim e
    · exact Or.inl
  unfold law NMSC.rootDist
  rw [hs, hs, h1]
  change _ * (if NMSC.arriving (G.pieceNetwork () : RootedNetwork Unit G.Arc L) inj _ () = F then _ else _) = _
  rw [h2, one_mul]

/-- A vertex with one child, glued on a single vertex. -/
theorem law_one {W : MetricDigraph T X} {G : MetricDigraph V₁ X} {r : V₁} {fV : Unit ⊕ V₁ ≃ T}
    {ℓ : ℝ} (hg : IsGluedGraph W (pointG : MetricDigraph Unit X) G fV r (fun _ : Unit => ())
      (fun _ => ℓ)) (inj : T → Finset (Finset L)) (F : Finset (Finset L)) :
    W.law (fV (.inl ())) inj F =
      ∑ t, up G r (fun v => inj (fV (.inr v))) ℓ t *
        if inj (fV (.inl ())) ∪ t = F then 1 else 0 := by
  rw [law_glue_unit hg () inj F]
  refine sum_congr rfl fun t _ => ?_
  rw [law_of_unit (fun _ _ h => h)]
  have : NMSC.upperInj fV (fun _ : Unit => ()) inj (fun _ => t) () = inj (fV (.inl ())) ∪ t := by
    ext A
    simp [NMSC.upperInj]
  rw [this]
  rfl

/-- A new vertex with an arc of length `ℓ` to the vertex `r` of `G`. -/
def stem {A : Type} (ℓ : ℝ) (G : MetricDigraph A X) (r : A) : MetricDigraph (Option A) X where
  Adj
    | none, some a => a = r
    | some a, some a' => G.Adj a a'
    | _, _ => False
  label
    | none => none
    | some a => G.label a
  len
    | none, some _ => ℓ
    | some a, some a' => G.len a a'
    | _, _ => 0
  inh
    | some a, some a' => G.inh a a'
    | _, _ => 0

/-- The vertices of the stem, as a sum. -/
def stemVert {A : Type} : Unit ⊕ A ≃ Option A where
  toFun x := x.elim (fun _ => none) some
  invFun x := x.elim (.inl ()) .inr
  left_inv x := by rcases x with x | x <;> rfl
  right_inv x := by cases x <;> rfl

/-- A stem is glued from a vertex and a graph. -/
theorem stem_isGlued {ℓ : ℝ} {G : MetricDigraph V₁ X} {r : V₁} (hr : ∀ u, ¬ G.Adj u r) :
    IsGluedGraph (stem ℓ G r) (pointG : MetricDigraph Unit X) G stemVert r (fun _ : Unit => ())
      (fun _ => ℓ) where
  adj₀ _ _ := Iff.rfl
  adj₁ _ _ := Iff.rfl
  adj₀₁ _ v := by
    change v = r ↔ _
    simp
  adj₁₀ _ _ h := h
  s_inj _ _ _ := rfl
  not_adj_root := hr
  len₀ _ _ h := h.elim
  len₁ _ _ _ := rfl
  lenP _ := rfl
  inh₀ _ _ h := h.elim
  inh₁ _ _ _ := rfl

/-- The law at the top of a stem. -/
theorem law_stem {ℓ : ℝ} {G : MetricDigraph V₁ X} {r : V₁} (hr : ∀ u, ¬ G.Adj u r)
    (inj : Option V₁ → Finset (Finset L)) (F : Finset (Finset L)) :
    (stem ℓ G r).law none inj F =
      ∑ t, up G r (fun v => inj (some v)) ℓ t * if inj none ∪ t = F then 1 else 0 :=
  law_one (stem_isGlued hr) inj F

/-- A vertex with two children: a stem, and a second graph. -/
theorem law_two {A B : Type} [Fintype A] [Fintype B] {W : MetricDigraph T X} {G₁ : MetricDigraph A X}
    {G₂ : MetricDigraph B X} {r₁ : A} {r₂ : B} {fV : Option A ⊕ B ≃ T} {ℓ₁ ℓ₂ : ℝ}
    (hr₁ : ∀ u, ¬ G₁.Adj u r₁)
    (hg : IsGluedGraph W (stem ℓ₁ G₁ r₁) G₂ fV r₂ (fun _ : Unit => none) (fun _ => ℓ₂))
    (inj : T → Finset (Finset L)) (F : Finset (Finset L)) :
    W.law (fV (.inl none)) inj F =
      ∑ t₂, up G₂ r₂ (fun v => inj (fV (.inr v))) ℓ₂ t₂ *
        ∑ t₁, up G₁ r₁ (fun v => inj (fV (.inl (some v)))) ℓ₁ t₁ *
          if inj (fV (.inl none)) ∪ t₂ ∪ t₁ = F then 1 else 0 := by
  rw [law_glue_unit hg none inj F]
  refine sum_congr rfl fun t₂ _ => ?_
  have h1 : (fun v => NMSC.upperInj fV (fun _ : Unit => none) inj (fun _ => t₂) (some v)) =
      fun v => inj (fV (.inl (some v))) := by
    funext v
    simp [NMSC.upperInj]
  have h2 : NMSC.upperInj fV (fun _ : Unit => none) inj (fun _ => t₂) none =
      inj (fV (.inl none)) ∪ t₂ := by
    ext A
    simp [NMSC.upperInj]
  rw [law_stem hr₁, h1, h2]
  rfl

end Gluing

/-! ### The graph constructions of a term -/

section Constructions

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

/-- The vertices of a tree node, as a sum. -/
def treeVertEquiv : Option A ⊕ B ≃ TreeVert A B where
  toFun x := match x with
    | .inl none => .root
    | .inl (some a) => .left a
    | .inr b => .right b
  invFun x := match x with
    | .root => .inl none
    | .left a => .inl (some a)
    | .right b => .inr b
  left_inv x := by rcases x with (_ | _) | _ <;> rfl
  right_inv x := by cases x <;> rfl

/-- The law at a tree node on no cycle. -/
theorem law_tree [Fintype (TreeVert A B)] {ℓ₁ ℓ₂ : ℝ} {G₁ : MetricDigraph A X}
    {G₂ : MetricDigraph B X} {r₁ : A} {r₂ : B} (hr₁ : ∀ u, ¬ G₁.Adj u r₁) (hr₂ : ∀ u, ¬ G₂.Adj u r₂)
    (inj : TreeVert A B → Finset (Finset L)) (F : Finset (Finset L)) :
    (tree ℓ₁ G₁ r₁ ℓ₂ G₂ r₂).law .root inj F =
      ∑ t₂, up G₂ r₂ (fun v => inj (.right v)) ℓ₂ t₂ *
        ∑ t₁, up G₁ r₁ (fun v => inj (.left v)) ℓ₁ t₁ *
          if inj .root ∪ t₂ ∪ t₁ = F then 1 else 0 := by
  refine law_two (fV := treeVertEquiv) hr₁ ?_ inj F
  exact
    { adj₀ := by rintro (_ | a) (_ | a') <;> exact Iff.rfl
      adj₁ := fun _ _ => Iff.rfl
      adj₀₁ := by
        rintro (_ | a) v
        · change v = r₂ ↔ _
          simp
        · change False ↔ _
          simp
      adj₁₀ := by rintro _ (_ | a) h <;> exact h
      s_inj := fun _ _ _ => rfl
      not_adj_root := hr₂
      len₀ := by
        rintro (_ | a) (_ | a') h
        all_goals first | exact h.elim | rfl
      len₁ := fun _ _ _ => rfl
      lenP := fun _ => rfl
      inh₀ := by
        rintro (_ | a) (_ | a') h
        all_goals first | exact h.elim | rfl
      inh₁ := fun _ _ _ => rfl }

/-- The vertices of a node of a side, as a sum. -/
def nodeVertEquiv : Option A ⊕ B ≃ NodeVert A B where
  toFun x := match x with
    | .inl none => .node
    | .inl (some a) => .pendant a
    | .inr b => .rest b
  invFun x := match x with
    | .node => .inl none
    | .pendant a => .inl (some a)
    | .rest b => .inr b
  left_inv x := by rcases x with (_ | _) | _ <;> rfl
  right_inv x := by cases x <;> rfl

/-- The law at a node of a side that continues to a further node. -/
theorem law_node_some [Fintype (NodeVert A B)] {ℓ b : ℝ} {G : MetricDigraph A X} {r : A}
    {S : SideGraph B X} {f : B} (hf : S.first = some f) (hr : ∀ u, ¬ G.Adj u r)
    (hS : ∀ u, ¬ S.graph.Adj u f) (inj : NodeVert A B → Finset (Finset L))
    (F : Finset (Finset L)) :
    (SideGraph.node ℓ b G r S).graph.law .node inj F =
      ∑ t₂, up S.graph f (fun v => inj (.rest v)) S.topLen t₂ *
        ∑ t₁, up G r (fun v => inj (.pendant v)) b t₁ *
          if inj .node ∪ t₂ ∪ t₁ = F then 1 else 0 := by
  refine law_two (fV := nodeVertEquiv) hr ?_ inj F
  exact
    { adj₀ := by rintro (_ | a) (_ | a') <;> exact Iff.rfl
      adj₁ := fun _ _ => Iff.rfl
      adj₀₁ := by
        rintro (_ | a) v
        · change S.first = some v ↔ _
          rw [hf]
          simp [eq_comm]
        · change False ↔ _
          simp
      adj₁₀ := by rintro _ (_ | a) h <;> exact h
      s_inj := fun _ _ _ => rfl
      not_adj_root := hS
      len₀ := by
        rintro (_ | a) (_ | a') h
        all_goals first | exact h.elim | rfl
      len₁ := fun _ _ _ => rfl
      lenP := fun _ => rfl
      inh₀ := by
        rintro (_ | a) (_ | a') h
        all_goals first | exact h.elim | rfl
      inh₁ := fun _ _ _ => rfl }

/-- The vertices of the last node of a side, as a sum. -/
def nodeVertEquivEmpty : Unit ⊕ A ≃ NodeVert A Empty where
  toFun x := match x with
    | .inl _ => .node
    | .inr a => .pendant a
  invFun x := match x with
    | .node => .inl ()
    | .pendant a => .inr a
    | .rest b => b.elim
  left_inv x := by rcases x with _ | _ <;> rfl
  right_inv x := by
    cases x with
    | node => rfl
    | pendant a => rfl
    | rest b => exact b.elim

/-- The law at the last node of a side. -/
theorem law_node_none [Fintype (NodeVert A Empty)] {ℓ b ℓ' : ℝ} {G : MetricDigraph A X} {r : A}
    (hr : ∀ u, ¬ G.Adj u r) (inj : NodeVert A Empty → Finset (Finset L)) (F : Finset (Finset L)) :
    (SideGraph.node ℓ b G r (SideGraph.hyb ℓ')).graph.law .node inj F =
      ∑ t, up G r (fun v => inj (.pendant v)) b t * if inj .node ∪ t = F then 1 else 0 := by
  refine law_one (fV := nodeVertEquivEmpty) ?_ inj F
  exact
    { adj₀ := fun _ _ => Iff.rfl
      adj₁ := fun _ _ => Iff.rfl
      adj₀₁ := by
        rintro _ v
        change v = r ↔ _
        simp
      adj₁₀ := fun _ _ h => h
      s_inj := fun _ _ _ => rfl
      not_adj_root := hr
      len₀ := fun _ _ h => h.elim
      len₁ := fun _ _ _ => rfl
      lenP := fun _ => rfl
      inh₀ := fun _ _ h => h.elim
      inh₁ := fun _ _ _ => rfl }

/-! ### Cycles -/

section Cycles

variable {γ ℓ : ℝ}

/-- The vertices of a cycle whose two sides have nodes, as a sum. -/
def cycleVertTwo : TreeVert A B ⊕ Option C ≃ CycleVert A B C where
  toFun x := match x with
    | .inl .root => .top
    | .inl (.left a) => .side₁ a
    | .inl (.right b) => .side₂ b
    | .inr none => .hyb
    | .inr (some c) => .below c
  invFun x := match x with
    | .top => .inl .root
    | .side₁ a => .inl (.left a)
    | .side₂ b => .inl (.right b)
    | .hyb => .inr none
    | .below c => .inr (some c)
  left_inv x := by rcases x with (_ | _ | _) | (_ | _) <;> rfl
  right_inv x := by cases x <;> rfl

/-- A cycle whose two sides have nodes is glued from the top node with its sides, and the hybrid node
with what lies below it. -/
theorem cycle_isGlued_two [Fintype (TreeVert A B)] [Fintype (CycleVert A B C)] {S₁ : SideGraph A X}
    {S₂ : SideGraph B X} {G : MetricDigraph C X} {r : C} {f₁ l₁ : A} {f₂ l₂ : B}
    (hf₁ : S₁.first = some f₁) (hl₁ : S₁.last = some l₁) (hf₂ : S₂.first = some f₂)
    (hl₂ : S₂.last = some l₂) :
    IsGluedGraph (cycle γ S₁ S₂ ℓ G r) (tree S₁.topLen S₁.graph f₁ S₂.topLen S₂.graph f₂) (stem ℓ G r)
      cycleVertTwo none (fun p => cond p (.right l₂) (.left l₁)) (fun p => cond p S₂.hybLen S₁.hybLen) where
  adj₀ := by
    rintro (_ | a | b) (_ | a' | b')
    all_goals first
      | exact Iff.rfl
      | (change S₁.first = some _ ↔ _ = f₁; rw [hf₁]; simp [eq_comm])
      | (change S₂.first = some _ ↔ _ = f₂; rw [hf₂]; simp [eq_comm])
  adj₁ := by rintro (_ | c) (_ | c') <;> exact Iff.rfl
  adj₀₁ := by
    rintro (_ | a | b) (_ | c)
    · change (S₁.first = none ∨ S₂.first = none) ↔ _
      simp [hf₁, hf₂]
    · change False ↔ _
      simp
    · change S₁.last = some a ↔ _
      rw [hl₁]
      constructor
      · intro h
        exact ⟨rfl, false, by simpa using h⟩
      · rintro ⟨-, p, h⟩
        cases p <;> simp_all
    · change False ↔ _
      simp
    · change S₂.last = some b ↔ _
      rw [hl₂]
      constructor
      · intro h
        exact ⟨rfl, true, by simpa using h⟩
      · rintro ⟨-, p, h⟩
        cases p <;> simp_all
    · change False ↔ _
      simp
  adj₁₀ := by rintro (_ | c) (_ | a | b) h <;> exact h
  s_inj := by
    rintro (_ | _) (_ | _) h
    all_goals simp_all
  not_adj_root := by rintro (_ | c) h <;> exact h
  len₀ := by
    rintro (_ | a | b) (_ | a' | b') h
    all_goals first | exact h.elim | rfl
  len₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl
  lenP := by rintro (_ | _) <;> rfl
  inh₀ := by
    rintro (_ | a | b) (_ | a' | b') h
    all_goals first | exact h.elim | rfl
  inh₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl

/-- The vertices of a cycle whose first side has no node, as a sum. -/
def cycleVertLeft : Option B ⊕ Option C ≃ CycleVert Empty B C where
  toFun x := match x with
    | .inl none => .top
    | .inl (some b) => .side₂ b
    | .inr none => .hyb
    | .inr (some c) => .below c
  invFun x := match x with
    | .top => .inl none
    | .side₁ a => a.elim
    | .side₂ b => .inl (some b)
    | .hyb => .inr none
    | .below c => .inr (some c)
  left_inv x := by rcases x with (_ | _) | (_ | _) <;> rfl
  right_inv x := by
    cases x with
    | side₁ a => exact a.elim
    | _ => rfl

/-- A cycle whose first side is a hybrid edge. -/
theorem cycle_isGlued_left [Fintype (CycleVert Empty B C)] {ℓ₁ : ℝ}
    {S₂ : SideGraph B X} {G : MetricDigraph C X} {r : C} {f₂ l₂ : B}
    (hf₂ : S₂.first = some f₂) (hl₂ : S₂.last = some l₂) :
    IsGluedGraph (cycle γ (SideGraph.hyb ℓ₁) S₂ ℓ G r) (stem S₂.topLen S₂.graph f₂) (stem ℓ G r)
      cycleVertLeft none (fun p => cond p (some l₂) none) (fun p => cond p S₂.hybLen ℓ₁) where
  adj₀ := by
    rintro (_ | b) (_ | b')
    all_goals first
      | exact Iff.rfl
      | (change S₂.first = some _ ↔ _ = f₂; rw [hf₂]; simp [eq_comm])
  adj₁ := by rintro (_ | c) (_ | c') <;> exact Iff.rfl
  adj₀₁ := by
    rintro (_ | b) (_ | c)
    · change ((none : Option Empty) = none ∨ S₂.first = none) ↔ _
      simp only [true_or, true_iff]
      exact ⟨trivial, false, rfl⟩
    · change False ↔ _
      simp
    · change S₂.last = some b ↔ _
      rw [hl₂]
      constructor
      · intro h
        exact ⟨rfl, true, by simpa using h⟩
      · rintro ⟨-, p, h⟩
        cases p <;> simp_all
    · change False ↔ _
      simp
  adj₁₀ := by rintro (_ | c) (_ | b) h <;> exact h
  s_inj := by
    rintro (_ | _) (_ | _) h
    all_goals simp_all
  not_adj_root := by rintro (_ | c) h <;> exact h
  len₀ := by
    rintro (_ | b) (_ | b') h
    all_goals first | exact h.elim | rfl
  len₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl
  lenP := by rintro (_ | _) <;> rfl
  inh₀ := by
    rintro (_ | b) (_ | b') h
    all_goals first | exact h.elim | rfl
  inh₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl

/-- The vertices of a cycle whose second side has no node, as a sum. -/
def cycleVertRight : Option A ⊕ Option C ≃ CycleVert A Empty C where
  toFun x := match x with
    | .inl none => .top
    | .inl (some a) => .side₁ a
    | .inr none => .hyb
    | .inr (some c) => .below c
  invFun x := match x with
    | .top => .inl none
    | .side₁ a => .inl (some a)
    | .side₂ b => b.elim
    | .hyb => .inr none
    | .below c => .inr (some c)
  left_inv x := by rcases x with (_ | _) | (_ | _) <;> rfl
  right_inv x := by
    cases x with
    | side₂ b => exact b.elim
    | _ => rfl

/-- A cycle whose second side is a hybrid edge. -/
theorem cycle_isGlued_right [Fintype (CycleVert A Empty C)] {ℓ₂ : ℝ}
    {S₁ : SideGraph A X} {G : MetricDigraph C X} {r : C} {f₁ l₁ : A}
    (hf₁ : S₁.first = some f₁) (hl₁ : S₁.last = some l₁) :
    IsGluedGraph (cycle γ S₁ (SideGraph.hyb ℓ₂) ℓ G r) (stem S₁.topLen S₁.graph f₁) (stem ℓ G r)
      cycleVertRight none (fun p => cond p none (some l₁)) (fun p => cond p ℓ₂ S₁.hybLen) where
  adj₀ := by
    rintro (_ | a) (_ | a')
    all_goals first
      | exact Iff.rfl
      | (change S₁.first = some _ ↔ _ = f₁; rw [hf₁]; simp [eq_comm])
  adj₁ := by rintro (_ | c) (_ | c') <;> exact Iff.rfl
  adj₀₁ := by
    rintro (_ | a) (_ | c)
    · change (S₁.first = none ∨ (none : Option Empty) = none) ↔ _
      simp only [or_true, true_iff]
      exact ⟨trivial, true, rfl⟩
    · change False ↔ _
      simp
    · change S₁.last = some a ↔ _
      rw [hl₁]
      constructor
      · intro h
        exact ⟨rfl, false, by simpa using h⟩
      · rintro ⟨-, p, h⟩
        cases p <;> simp_all
    · change False ↔ _
      simp
  adj₁₀ := by rintro (_ | c) (_ | a) h <;> exact h
  s_inj := by
    rintro (_ | _) (_ | _) h
    all_goals simp_all
  not_adj_root := by rintro (_ | c) h <;> exact h
  len₀ := by
    rintro (_ | a) (_ | a') h
    all_goals first | exact h.elim | rfl
  len₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl
  lenP := by
    rintro (_ | _)
    · rfl
    · simp [cycle, cycleVertRight, hf₁]
      rfl
  inh₀ := by
    rintro (_ | a) (_ | a') h
    all_goals first | exact h.elim | rfl
  inh₁ := by
    rintro (_ | c) (_ | c') h
    all_goals first | exact h.elim | rfl

end Cycles

end Constructions

/-! ### Sums of forests -/

section Sums

theorem sum_comm_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ a, ∑ b, f a b c d := by
  have h : ∑ x : α × β × γ × δ, f x.1 x.2.1 x.2.2.1 x.2.2.2 =
      ∑ y : δ × γ × α × β, f y.2.2.1 y.2.2.2 y.2.1 y.1 :=
    Fintype.sum_equiv
      { toFun := fun x => (x.2.2.2, x.2.2.1, x.1, x.2.1)
        invFun := fun y => (y.2.2.1, y.2.2.2, y.2.1, y.1)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun _ => rfl
  simpa only [Fintype.sum_prod_type] using h

/-- The law of the union of the forests of the two sides of a cycle with nodes. -/
theorem forestUnion_two (K₁ K₂ : Finset (Finset L) → ℝ) (U₁ U₂ : Finset (Finset L) → Finset (Finset L) → ℝ)
    (F : Finset (Finset L)) :
    ∑ t₁, ∑ t₂, K₁ t₁ * K₂ t₂ * ∑ x₂, U₂ t₂ x₂ * ∑ x₁, U₁ t₁ x₁ *
        (if ∅ ∪ x₂ ∪ x₁ = F then 1 else 0) =
      forestUnion (fun x => ∑ t, K₁ t * U₁ t x) (fun x => ∑ t, K₂ t * U₂ t x) F := by
  unfold forestUnion
  have hrhs : ∀ x₁ x₂ : Finset (Finset L),
      (if x₁ ∪ x₂ = F then (∑ t, K₁ t * U₁ t x₁) * (∑ t, K₂ t * U₂ t x₂) else 0) =
        ∑ t₁, ∑ t₂, K₁ t₁ * K₂ t₂ * (U₂ t₂ x₂ * (U₁ t₁ x₁ *
          (if ∅ ∪ x₂ ∪ x₁ = F then 1 else 0))) := by
    intro x₁ x₂
    have hc : (∅ ∪ x₂ ∪ x₁ = F) ↔ (x₁ ∪ x₂ = F) := by
      rw [empty_union, union_comm]
    by_cases h : x₁ ∪ x₂ = F
    · rw [ite_eq_left h, ite_eq_left (hc.2 h), Finset.sum_mul_sum]
      refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => ?_
      ring
    · rw [ite_eq_right h, ite_eq_right fun h' => h (hc.1 h')]
      simp
  simp_rw [hrhs]
  simp only [mul_sum]
  exact sum_comm_four fun t₁ t₂ x₂ x₁ => K₁ t₁ * K₂ t₂ * (U₂ t₂ x₂ * (U₁ t₁ x₁ *
    (if ∅ ∪ x₂ ∪ x₁ = F then 1 else 0)))

/-- The law of the union when the first side is a hybrid edge. -/
theorem forestUnion_left (K₁ K₂ : Finset (Finset L) → ℝ) (U₂ : Finset (Finset L) → Finset (Finset L) → ℝ)
    (F : Finset (Finset L)) :
    ∑ t₁, ∑ t₂, K₁ t₁ * K₂ t₂ * ∑ x₂, U₂ t₂ x₂ * (if ∅ ∪ t₁ ∪ x₂ = F then 1 else 0) =
      forestUnion K₁ (fun x => ∑ t, K₂ t * U₂ t x) F := by
  unfold forestUnion
  refine sum_congr rfl fun t₁ _ => ?_
  have hrhs : ∀ x₂ : Finset (Finset L),
      (if t₁ ∪ x₂ = F then K₁ t₁ * (∑ t, K₂ t * U₂ t x₂) else 0) =
        ∑ t₂, K₁ t₁ * K₂ t₂ * (U₂ t₂ x₂ * (if ∅ ∪ t₁ ∪ x₂ = F then 1 else 0)) := by
    intro x₂
    rw [empty_union]
    by_cases h : t₁ ∪ x₂ = F
    · rw [ite_eq_left h, mul_sum]
      refine sum_congr rfl fun t₂ _ => ?_
      rw [ite_eq_left h]
      ring
    · rw [ite_eq_right h]
      simp [ite_eq_right h]
  simp_rw [hrhs]
  simp only [mul_sum]
  rw [sum_comm]

/-- The law of the union when the second side is a hybrid edge. -/
theorem forestUnion_right (K₁ K₂ : Finset (Finset L) → ℝ) (U₁ : Finset (Finset L) → Finset (Finset L) → ℝ)
    (F : Finset (Finset L)) :
    ∑ t₁, ∑ t₂, K₁ t₁ * K₂ t₂ * ∑ x₁, U₁ t₁ x₁ * (if ∅ ∪ t₂ ∪ x₁ = F then 1 else 0) =
      forestUnion (fun x => ∑ t, K₁ t * U₁ t x) K₂ F := by
  unfold forestUnion
  have hrhs : ∀ x₁ x₂ : Finset (Finset L),
      (if x₁ ∪ x₂ = F then (∑ t, K₁ t * U₁ t x₁) * K₂ x₂ else 0) =
        ∑ t₁, K₁ t₁ * K₂ x₂ * (U₁ t₁ x₁ * (if ∅ ∪ x₂ ∪ x₁ = F then 1 else 0)) := by
    intro x₁ x₂
    have hc : (∅ ∪ x₂ ∪ x₁ = F) ↔ (x₁ ∪ x₂ = F) := by
      rw [empty_union, union_comm]
    by_cases h : x₁ ∪ x₂ = F
    · rw [ite_eq_left h, sum_mul]
      refine sum_congr rfl fun t₁ _ => ?_
      rw [ite_eq_left (hc.2 h)]
      ring
    · rw [ite_eq_right h]
      symm
      refine sum_eq_zero fun t₁ _ => ?_
      rw [ite_eq_right fun h' => h (hc.1 h')]
      ring
  simp_rw [hrhs]
  simp only [mul_sum]
  calc ∑ t₁, ∑ t₂, ∑ x₁, K₁ t₁ * K₂ t₂ * (U₁ t₁ x₁ * (if ∅ ∪ t₂ ∪ x₁ = F then 1 else 0))
      = ∑ t₁, ∑ x₁, ∑ t₂, K₁ t₁ * K₂ t₂ * (U₁ t₁ x₁ * (if ∅ ∪ t₂ ∪ x₁ = F then 1 else 0)) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ x₁, ∑ t₁, ∑ t₂, K₁ t₁ * K₂ t₂ * (U₁ t₁ x₁ * (if ∅ ∪ t₂ ∪ x₁ = F then 1 else 0)) := sum_comm
    _ = ∑ x₁, ∑ t₂, ∑ t₁, K₁ t₁ * K₂ t₂ * (U₁ t₁ x₁ * (if ∅ ∪ t₂ ∪ x₁ = F then 1 else 0)) :=
        sum_congr rfl fun _ _ => sum_comm

/-- The law of the union of the forests at the two children of a vertex. -/
theorem forestUnion_children (μ ν : Finset (Finset L) → ℝ) (F : Finset (Finset L)) :
    ∑ t₂, ν t₂ * ∑ t₁, μ t₁ * (if ∅ ∪ t₂ ∪ t₁ = F then 1 else 0) = forestUnion μ ν F := by
  unfold forestUnion
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => ?_
  have hc : (∅ ∪ t₂ ∪ t₁ = F) ↔ (t₁ ∪ t₂ = F) := by
    rw [empty_union, union_comm]
  by_cases h : t₁ ∪ t₂ = F
  · rw [ite_eq_left h, ite_eq_left (hc.2 h)]
    ring
  · rw [ite_eq_right h, ite_eq_right fun h' => h (hc.1 h')]
    ring

end Sums

/-! ### Laws at the top node of a cycle -/

section CycleLaws

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {γ ℓ : ℝ} {G : MetricDigraph C X} {r : C}

omit [Fintype L] [DecidableEq L] in
theorem mul_congr_right {a x y : ℝ} (h : x = y) : a * x = a * y := by rw [h]

/-- The arc above the hybrid node: the forest arriving there is the one at the top of its child arc. -/
theorem law_stem_hyb (hr : ∀ u, ¬ G.Adj u r) (inj : Option C → Finset (Finset L))
    (hnone : inj none = ∅) (F : Finset (Finset L)) :
    (stem ℓ G r).law none inj F = up G r (fun c => inj (some c)) ℓ F := by
  rw [law_stem hr, hnone, Finset.sum_eq_single F]
  · simp
  · intro t _ ht
    rw [ite_eq_right (by simpa using ht)]
    simp
  · simp

/-- The law at the top node of a cycle whose two sides have nodes. -/
theorem law_cycle_two [Fintype (TreeVert A B)] [Fintype (CycleVert A B C)] {S₁ : SideGraph A X}
    {S₂ : SideGraph B X} {f₁ l₁ : A} {f₂ l₂ : B} (hf₁ : S₁.first = some f₁) (hl₁ : S₁.last = some l₁)
    (hf₂ : S₂.first = some f₂) (hl₂ : S₂.last = some l₂) (h₁ : ∀ u, ¬ S₁.graph.Adj u f₁)
    (h₂ : ∀ u, ¬ S₂.graph.Adj u f₂) (hr : ∀ u, ¬ G.Adj u r)
    (inj : CycleVert A B C → Finset (Finset L)) (htop : inj .top = ∅) (hhyb : inj .hyb = ∅)
    (F : Finset (Finset L)) :
    (cycle γ S₁ S₂ ℓ G r).law .top inj F =
      ∑ F₁, up G r (fun c => inj (.below c)) ℓ F₁ * ∑ A' ∈ (roots F₁).powerset,
        γ ^ #A' * (1 - γ) ^ #(roots F₁ \ A') *
          forestUnion
            (fun x => ∑ t, kingmanTransition S₁.hybLen (forestBelow F₁ A') t *
              up S₁.graph f₁ (fun a => inj (.side₁ a) ∪ if a = l₁ then t else ∅) S₁.topLen x)
            (fun x => ∑ t, kingmanTransition S₂.hybLen (forestBelow F₁ (roots F₁ \ A')) t *
              up S₂.graph f₂ (fun b => inj (.side₂ b) ∪ if b = l₂ then t else ∅) S₂.topLen x) F := by
  have hg := cycle_isGlued_two (γ := γ) (ℓ := ℓ) (G := G) (r := r) hf₁ hl₁ hf₂ hl₂
  refine (law_glue_bool hg (L := L) .root (γ := γ) rfl rfl inj F).trans ?_
  refine sum_congr rfl fun F₁ _ => ?_
  rw [law_stem_hyb hr _ hhyb]
  refine mul_congr_right (sum_congr rfl fun A' _ => mul_congr_right ?_)
  refine Eq.trans ?_ (forestUnion_two (kingmanTransition S₁.hybLen (forestBelow F₁ A'))
    (kingmanTransition S₂.hybLen (forestBelow F₁ (roots F₁ \ A')))
    (fun t x => up S₁.graph f₁ (fun a => inj (.side₁ a) ∪ if a = l₁ then t else ∅) S₁.topLen x)
    (fun t x => up S₂.graph f₂ (fun b => inj (.side₂ b) ∪ if b = l₂ then t else ∅) S₂.topLen x) F)
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => mul_congr_right ?_
  rw [law_tree h₁ h₂]
  have hl : (fun a => NMSC.upperInj cycleVertTwo (fun p => cond p (.right l₂) (.left l₁)) inj
      (fun p => cond p t₂ t₁) (TreeVert.left a)) =
      fun a => inj (.side₁ a) ∪ if a = l₁ then t₁ else ∅ := by
    funext a
    ext Z
    by_cases ha : a = l₁
    · subst ha
      simp [NMSC.upperInj, cycleVertTwo]
    · simp [NMSC.upperInj, cycleVertTwo, ha, Ne.symm ha]
  have hr' : (fun b => NMSC.upperInj cycleVertTwo (fun p => cond p (.right l₂) (.left l₁)) inj
      (fun p => cond p t₂ t₁) (TreeVert.right b)) =
      fun b => inj (.side₂ b) ∪ if b = l₂ then t₂ else ∅ := by
    funext b
    ext Z
    by_cases hb : b = l₂
    · subst hb
      simp [NMSC.upperInj, cycleVertTwo]
    · simp [NMSC.upperInj, cycleVertTwo, hb, Ne.symm hb]
  have ht : NMSC.upperInj cycleVertTwo (fun p => cond p (.right l₂) (.left l₁)) inj
      (fun p => cond p t₂ t₁) TreeVert.root = ∅ := by
    ext Z
    simpa [NMSC.upperInj, cycleVertTwo] using fun h => absurd (htop ▸ h) (notMem_empty Z)
  rw [hl, hr', ht]

/-- The law at the top node of a cycle whose first side is a hybrid edge. -/
theorem law_cycle_left [Fintype (CycleVert Empty B C)] {ℓ₁ : ℝ} {S₂ : SideGraph B X} {f₂ l₂ : B}
    (hf₂ : S₂.first = some f₂) (hl₂ : S₂.last = some l₂) (h₂ : ∀ u, ¬ S₂.graph.Adj u f₂)
    (hr : ∀ u, ¬ G.Adj u r) (inj : CycleVert Empty B C → Finset (Finset L)) (htop : inj .top = ∅)
    (hhyb : inj .hyb = ∅) (F : Finset (Finset L)) :
    (cycle γ (SideGraph.hyb ℓ₁) S₂ ℓ G r).law .top inj F =
      ∑ F₁, up G r (fun c => inj (.below c)) ℓ F₁ * ∑ A' ∈ (roots F₁).powerset,
        γ ^ #A' * (1 - γ) ^ #(roots F₁ \ A') *
          forestUnion (kingmanTransition ℓ₁ (forestBelow F₁ A'))
            (fun x => ∑ t, kingmanTransition S₂.hybLen (forestBelow F₁ (roots F₁ \ A')) t *
              up S₂.graph f₂ (fun b => inj (.side₂ b) ∪ if b = l₂ then t else ∅) S₂.topLen x) F := by
  have hg := cycle_isGlued_left (γ := γ) (ℓ := ℓ) (G := G) (r := r) (ℓ₁ := ℓ₁) hf₂ hl₂
  refine (law_glue_bool hg (L := L) none (γ := γ) rfl rfl inj F).trans ?_
  refine sum_congr rfl fun F₁ _ => ?_
  rw [law_stem_hyb hr _ hhyb]
  refine mul_congr_right (sum_congr rfl fun A' _ => mul_congr_right ?_)
  refine Eq.trans ?_ (forestUnion_left (kingmanTransition ℓ₁ (forestBelow F₁ A'))
    (kingmanTransition S₂.hybLen (forestBelow F₁ (roots F₁ \ A')))
    (fun t x => up S₂.graph f₂ (fun b => inj (.side₂ b) ∪ if b = l₂ then t else ∅) S₂.topLen x) F)
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => mul_congr_right ?_
  rw [law_stem h₂]
  have hr' : (fun b => NMSC.upperInj cycleVertLeft (fun p => cond p (some l₂) none) inj
      (fun p => cond p t₂ t₁) (some b)) =
      fun b => inj (.side₂ b) ∪ if b = l₂ then t₂ else ∅ := by
    funext b
    ext Z
    by_cases hb : b = l₂
    · subst hb
      simp [NMSC.upperInj, cycleVertLeft]
    · simp [NMSC.upperInj, cycleVertLeft, hb, Ne.symm hb]
  have ht : NMSC.upperInj cycleVertLeft (fun p => cond p (some l₂) none) inj
      (fun p => cond p t₂ t₁) none = ∅ ∪ t₁ := by
    ext Z
    have : inj (cycleVertLeft (.inl none)) = ∅ := htop
    simp [NMSC.upperInj, this]
  rw [hr', ht]

/-- The law at the top node of a cycle whose second side is a hybrid edge. -/
theorem law_cycle_right [Fintype (CycleVert A Empty C)] {ℓ₂ : ℝ} {S₁ : SideGraph A X} {f₁ l₁ : A}
    (hf₁ : S₁.first = some f₁) (hl₁ : S₁.last = some l₁) (h₁ : ∀ u, ¬ S₁.graph.Adj u f₁)
    (hr : ∀ u, ¬ G.Adj u r) (inj : CycleVert A Empty C → Finset (Finset L)) (htop : inj .top = ∅)
    (hhyb : inj .hyb = ∅) (F : Finset (Finset L)) :
    (cycle γ S₁ (SideGraph.hyb ℓ₂) ℓ G r).law .top inj F =
      ∑ F₁, up G r (fun c => inj (.below c)) ℓ F₁ * ∑ A' ∈ (roots F₁).powerset,
        γ ^ #A' * (1 - γ) ^ #(roots F₁ \ A') *
          forestUnion
            (fun x => ∑ t, kingmanTransition S₁.hybLen (forestBelow F₁ A') t *
              up S₁.graph f₁ (fun a => inj (.side₁ a) ∪ if a = l₁ then t else ∅) S₁.topLen x)
            (kingmanTransition ℓ₂ (forestBelow F₁ (roots F₁ \ A'))) F := by
  have hg := cycle_isGlued_right (γ := γ) (ℓ := ℓ) (G := G) (r := r) (ℓ₂ := ℓ₂) hf₁ hl₁
  refine (law_glue_bool hg (L := L) none (γ := γ) rfl ?_ inj F).trans ?_
  · simp [cycle, cycleVertRight, hf₁]
  refine sum_congr rfl fun F₁ _ => ?_
  rw [law_stem_hyb hr _ hhyb]
  refine mul_congr_right (sum_congr rfl fun A' _ => mul_congr_right ?_)
  refine Eq.trans ?_ (forestUnion_right (kingmanTransition S₁.hybLen (forestBelow F₁ A'))
    (kingmanTransition ℓ₂ (forestBelow F₁ (roots F₁ \ A')))
    (fun t x => up S₁.graph f₁ (fun a => inj (.side₁ a) ∪ if a = l₁ then t else ∅) S₁.topLen x) F)
  refine sum_congr rfl fun t₁ _ => sum_congr rfl fun t₂ _ => mul_congr_right ?_
  rw [law_stem h₁]
  have hl : (fun a => NMSC.upperInj cycleVertRight (fun p => cond p none (some l₁)) inj
      (fun p => cond p t₂ t₁) (some a)) =
      fun a => inj (.side₁ a) ∪ if a = l₁ then t₁ else ∅ := by
    funext a
    ext Z
    by_cases ha : a = l₁
    · subst ha
      simp [NMSC.upperInj, cycleVertRight]
    · simp [NMSC.upperInj, cycleVertRight, ha, Ne.symm ha]
  have ht : NMSC.upperInj cycleVertRight (fun p => cond p none (some l₁)) inj
      (fun p => cond p t₂ t₁) none = ∅ ∪ t₂ := by
    ext Z
    have : inj (cycleVertRight (.inl none)) = ∅ := htop
    simp [NMSC.upperInj, this]
  rw [hl, ht]

end CycleLaws

section Terms

variable [DecidableEq X]

/-- The forests injected at the vertices of a graph: the sampled lineages of the labelled vertices. -/
def injOf {V : Type} (G : MetricDigraph V X) (s : L → X) (v : V) : Finset (Finset L) :=
  match G.label v with
  | some x => sampledAt s x
  | none => ∅

/-- The law at the top of an arc, from the law below it. -/
theorem up_eq {V : Type} [Fintype V] {G : MetricDigraph V X} {r : V} {inj : V → Finset (Finset L)}
    {μ : Finset (Finset L) → ℝ} (h : ∀ F, G.law r inj F = μ F) (ℓ : ℝ) (t : Finset (Finset L)) :
    up G r inj ℓ t = (μ ᵥ* kingmanTransition ℓ) t := by
  simp only [up, h]
  rfl

theorem up_congr_inj {V : Type} [Fintype V] {G : MetricDigraph V X} {r : V}
    {inj inj' : V → Finset (Finset L)} (h : ∀ v, inj v = inj' v) (ℓ : ℝ) (t : Finset (Finset L)) :
    up G r inj ℓ t = up G r inj' ℓ t := by
  rw [funext h]

/-- The union of the forests along the rest of a side and along a pendant arc. -/
theorem forestUnion_rest (μ ν : Finset (Finset L) → ℝ) (F : Finset (Finset L)) :
    ∑ t₂, ν t₂ * ∑ t₁, μ t₁ * (if ∅ ∪ t₂ ∪ t₁ = F then 1 else 0) = forestUnion ν μ F := by
  unfold forestUnion
  simp only [mul_sum]
  refine sum_congr rfl fun t₂ _ => sum_congr rfl fun t₁ _ => ?_
  rw [empty_union]
  by_cases h : t₂ ∪ t₁ = F
  · rw [ite_eq_left h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    ring

/-- The union with a mixture is the mixture of the unions. -/
theorem forestUnion_sum_left (K : Finset (Finset L) → ℝ)
    (U : Finset (Finset L) → Finset (Finset L) → ℝ) (μ : Finset (Finset L) → ℝ)
    (Z : Finset (Finset L)) :
    forestUnion (fun x => ∑ t, K t * U t x) μ Z = ∑ t, K t * forestUnion (U t) μ Z := by
  unfold forestUnion
  have h : ∀ x y : Finset (Finset L),
      (if x ∪ y = Z then (∑ t, K t * U t x) * μ y else 0) =
        ∑ t, K t * if x ∪ y = Z then U t x * μ y else 0 := by
    intro x y
    by_cases hc : x ∪ y = Z
    · simp only [ite_eq_left hc, sum_mul, mul_assoc]
    · simp only [ite_eq_right hc, mul_zero, sum_const_zero]
  simp only [h, mul_sum]
  exact (sum_congr rfl fun _ _ => sum_comm).trans sum_comm

/-- The union of a forest at a hybrid edge and a forest along a pendant arc. -/
theorem forestUnion_single_left (K μ : Finset (Finset L) → ℝ) (Z : Finset (Finset L)) :
    forestUnion K μ Z = ∑ t, K t * ∑ x, μ x * (if (∅ ∪ t) ∪ x = Z then 1 else 0) := by
  unfold forestUnion
  refine sum_congr rfl fun t _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [empty_union]
  by_cases h : t ∪ x = Z
  · rw [ite_eq_left h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    ring

end Terms

end MetricDigraph

open MetricDigraph

section Terms

universe u

variable {X : Type u} {L : Type*} [Fintype L] [DecidableEq L] [DecidableEq X]

theorem Net.not_adj_root : (N : Net X) → ∀ u, ¬ N.toGraph.Adj u N.root
  | .leaf _, _ => id
  | .tree .., u => by cases u <;> exact id
  | .cycle .., u => by cases u <;> exact id

theorem Side.not_adj_first : (S : Side X) → ∀ {f : S.Vert}, S.toGraph.first = some f →
    ∀ u, ¬ S.toGraph.graph.Adj u f
  | .hyb _, _, h, _ => by cases h
  | .node _ _ _ _, f, h, u => by
    obtain rfl : NodeVert.node = f := Option.some.inj h
    cases u <;> exact id

mutual

/-- The law on the graph of a term is the coalescent on the term. -/
theorem Net.law_toGraph (s : L → X) : (N : Net X) → N.IsMetric → ∀ F : Finset (Finset L),
    N.toGraph.law N.root (injOf N.toGraph s) F = N.forestDist s F
  | .leaf x, _, F => by
    refine (law_of_unit (fun _ _ h => h) _ F).trans ?_
    change (if sampledAt s x = F then (1 : ℝ) else 0) = if F = sampledAt s x then 1 else 0
    simp only [eq_comm]
  | .tree ℓ₁ N₁ ℓ₂ N₂, ⟨_, _, h₁, h₂⟩, F => by
    refine (law_tree (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) N₁.not_adj_root N₂.not_adj_root _ F).trans ?_
    refine Eq.trans ?_ (forestUnion_children (N₁.forestDist s ᵥ* kingmanTransition ℓ₁)
      (N₂.forestDist s ᵥ* kingmanTransition ℓ₂) F)
    refine sum_congr rfl fun t₂ _ => congrArg₂ (· * ·)
      (up_eq (inj := injOf N₂.toGraph s) (Net.law_toGraph s N₂ h₂) ℓ₂ t₂)
      (sum_congr rfl fun t₁ _ => congrArg₂ (· * ·)
        (up_eq (inj := injOf N₁.toGraph s) (Net.law_toGraph s N₁ h₁) ℓ₁ t₁) rfl)
  | .cycle _ (.hyb _) (.hyb _) _ _, ⟨_, _, _, _, _, _, hne⟩, _ => by
    simp [Side.nodes] at hne
  | .cycle γ (.hyb ℓ₁) (.node ℓ₂ b₂ N₂ S₂) ℓ N, ⟨_, _, _, _, hS₂, hN, _⟩, F => by
    refine (law_cycle_left (γ := γ) (ℓ := ℓ) (ℓ₁ := ℓ₁)
      (S₂ := (Side.node ℓ₂ b₂ N₂ S₂).toGraph) rfl rfl ((Side.node ℓ₂ b₂ N₂ S₂).not_adj_first rfl)
      N.not_adj_root _ rfl rfl F).trans ?_
    refine sum_congr rfl fun F₁ _ => congrArg₂ (· * ·)
      (up_eq (inj := injOf N.toGraph s) (Net.law_toGraph s N hN) ℓ F₁)
      (sum_congr rfl fun A' _ => mul_congr_right ?_)
    have e₂ := fun x => (Side.law_toGraph s (Side.node ℓ₂ b₂ N₂ S₂) hS₂ _ _ rfl rfl
      (forestBelow F₁ (roots F₁ \ A')) x).symm
    exact congrArg (fun ν => forestUnion _ ν F) (funext e₂)
  | .cycle γ (.node ℓ₁ b₁ N₁ S₁) (.hyb ℓ₂) ℓ N, ⟨_, _, _, hS₁, _, hN, _⟩, F => by
    refine (law_cycle_right (γ := γ) (ℓ := ℓ) (ℓ₂ := ℓ₂)
      (S₁ := (Side.node ℓ₁ b₁ N₁ S₁).toGraph) rfl rfl ((Side.node ℓ₁ b₁ N₁ S₁).not_adj_first rfl)
      N.not_adj_root _ rfl rfl F).trans ?_
    refine sum_congr rfl fun F₁ _ => congrArg₂ (· * ·)
      (up_eq (inj := injOf N.toGraph s) (Net.law_toGraph s N hN) ℓ F₁)
      (sum_congr rfl fun A' _ => mul_congr_right ?_)
    have e₁ := fun x => (Side.law_toGraph s (Side.node ℓ₁ b₁ N₁ S₁) hS₁ _ _ rfl rfl
      (forestBelow F₁ A') x).symm
    exact congrArg (fun μ => forestUnion μ _ F) (funext e₁)
  | .cycle γ (.node ℓ₁ b₁ N₁ S₁) (.node ℓ₂ b₂ N₂ S₂) ℓ N, ⟨_, _, _, hS₁, hS₂, hN, _⟩, F => by
    refine (law_cycle_two (γ := γ) (ℓ := ℓ) (S₁ := (Side.node ℓ₁ b₁ N₁ S₁).toGraph)
      (S₂ := (Side.node ℓ₂ b₂ N₂ S₂).toGraph) rfl rfl rfl rfl
      ((Side.node ℓ₁ b₁ N₁ S₁).not_adj_first rfl) ((Side.node ℓ₂ b₂ N₂ S₂).not_adj_first rfl)
      N.not_adj_root _ rfl rfl F).trans ?_
    refine sum_congr rfl fun F₁ _ => congrArg₂ (· * ·)
      (up_eq (inj := injOf N.toGraph s) (Net.law_toGraph s N hN) ℓ F₁)
      (sum_congr rfl fun A' _ => mul_congr_right ?_)
    have e₁ := fun x => (Side.law_toGraph s (Side.node ℓ₁ b₁ N₁ S₁) hS₁ _ _ rfl rfl
      (forestBelow F₁ A') x).symm
    have e₂ := fun x => (Side.law_toGraph s (Side.node ℓ₂ b₂ N₂ S₂) hS₂ _ _ rfl rfl
      (forestBelow F₁ (roots F₁ \ A')) x).symm
    exact congrArg₂ (fun μ ν => forestUnion μ ν F) (funext e₁) (funext e₂)

/-- The law along a side with nodes: the forest `b` takes the hybrid edge at the bottom, and the forest
at the top of that edge is injected at the last node of the side. -/
theorem Side.law_toGraph (s : L → X) : (S : Side X) → S.IsMetric → ∀ (f l : S.Vert),
    S.toGraph.first = some f → S.toGraph.last = some l → ∀ b Y : Finset (Finset L),
    S.forestDist s b Y = ∑ t, kingmanTransition S.toGraph.hybLen b t *
      up S.toGraph.graph f (fun v => injOf S.toGraph.graph s v ∪ if v = l then t else ∅)
        S.toGraph.topLen Y
  | .hyb _, _, _, _, h, _, _, _ => by cases h
  | .node ℓ b N (.hyb ℓ'), ⟨_, _, hN, _⟩, f, l, hf, hl, b₀, Y => by
    obtain rfl : NodeVert.node = f := Option.some.inj hf
    obtain rfl : NodeVert.node = l := Option.some.inj hl
    change (forestUnion (kingmanTransition ℓ' b₀) (N.forestDist s ᵥ* kingmanTransition b) ᵥ*
      kingmanTransition ℓ) Y = _
    change ∑ Z, forestUnion (kingmanTransition ℓ' b₀) (N.forestDist s ᵥ* kingmanTransition b) Z *
      kingmanTransition ℓ Z Y = _
    simp only [forestUnion_single_left (kingmanTransition ℓ' b₀), sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    change _ = kingmanTransition ℓ' b₀ t * ∑ Z, _ * kingmanTransition ℓ Z Y
    rw [mul_sum]
    refine sum_congr rfl fun Z _ => ?_
    rw [mul_assoc]
    refine congrArg (_ * · ) (congrArg (· * _) ?_)
    refine Eq.symm ((law_node_none N.not_adj_root _ Z).trans ?_)
    refine sum_congr rfl fun x _ => congrArg₂ (· * ·)
      ((up_congr_inj (fun v => ?_) _ _).trans
        (up_eq (inj := injOf N.toGraph s) (Net.law_toGraph s N hN) b x))
      (if_congr (iff_of_eq (congrArg (fun y => y ∪ x = Z) ?_)) rfl rfl)
    · rw [ite_eq_right (by simp), union_empty]
      rfl
    · split_ifs with h
      · rfl
      · exact absurd rfl h
  | .node ℓ b N (.node ℓ' b' N' S'), ⟨_, _, hN, hS⟩, f, l, hf, hl, b₀, Y => by
    obtain rfl : NodeVert.node = f := Option.some.inj hf
    obtain ⟨l', hl'⟩ : ∃ l', (Side.node ℓ' b' N' S').toGraph.last = some l' := ⟨_, rfl⟩
    obtain rfl : NodeVert.rest l' = l := by
      have h2 : (SideGraph.node ℓ b N.toGraph N.root (Side.node ℓ' b' N' S').toGraph).last =
          some (.rest l') := by
        simp only [SideGraph.node, hl', Option.map_some, Option.getD_some]
      exact Option.some.inj (h2.symm.trans hl)
    have hIH := fun x => Side.law_toGraph s (Side.node ℓ' b' N' S') hS _ l' rfl hl' b₀ x
    change ∑ Z, forestUnion ((Side.node ℓ' b' N' S').forestDist s b₀)
      (N.forestDist s ᵥ* kingmanTransition b) Z * kingmanTransition ℓ Z Y = _
    simp only [funext hIH]
    simp only [forestUnion_sum_left, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    change _ = _ * ∑ Z, _ * kingmanTransition ℓ Z Y
    rw [mul_sum]
    refine sum_congr rfl fun Z _ => ?_
    rw [mul_assoc]
    refine congrArg (_ * · ) (congrArg (· * _) ?_)
    refine Eq.symm ((law_node_some rfl N.not_adj_root
      ((Side.node ℓ' b' N' S').not_adj_first rfl) _ Z).trans ?_)
    refine Eq.trans ?_ (forestUnion_rest (N.forestDist s ᵥ* kingmanTransition b) _ Z)
    refine sum_congr rfl fun t₂ _ => congrArg₂ (· * ·)
      (up_congr_inj (fun v => ?_) _ _)
      (sum_congr rfl fun t₁ _ => congrArg₂ (· * ·)
        ((up_congr_inj (fun v => ?_) _ _).trans
          (up_eq (inj := injOf N.toGraph s) (Net.law_toGraph s N hN) b t₁))
        (if_congr (iff_of_eq (congrArg (fun y => y ∪ t₂ ∪ t₁ = Z) ?_)) rfl rfl))
    · have e : ((NodeVert.rest v : (Side.node ℓ b N (Side.node ℓ' b' N' S')).Vert) =
          NodeVert.rest l') ↔ v = l' :=
        ⟨fun h => NodeVert.rest.inj h, fun h => congrArg NodeVert.rest h⟩
      exact congrArg₂ (· ∪ ·) rfl (if_congr e rfl rfl)
    · rw [ite_eq_right (by simp), union_empty]
      rfl
    · rw [ite_eq_right (by simp)]
      rfl

end

/-- The inheritance of the numerical parameters of a network is that of its pieces. -/
theorem MetricDigraph.metricData_inheritance_eq {V : Type} {G : MetricDigraph V X} [Fintype V]
    (hG : G.IsNetwork) (e : G.Arc) : G.metricData.inheritance e = G.pieceInh e := by
  have hiff : G.IsHybrid e.1.2 ↔ G.HasOtherParent e := by
    constructor
    · intro h
      obtain ⟨u, u', huu', hu⟩ := indeg_eq_two_iff.1 h.1
      rcases (hu e.1.1).1 e.2 with h₁ | h₁
      · exact ⟨u', fun h' => huu' (h₁.symm.trans h'.symm), (hu u').2 (Or.inr rfl)⟩
      · exact ⟨u, fun h' => huu' (h'.trans h₁), (hu u).2 (Or.inl rfl)⟩
    · rintro ⟨u, hu, h⟩
      refine isHybrid_of_two_le_indeg hG ?_
      have : ({e.1.1, u} : Set V) ⊆ {x | G.Adj x e.1.2} := by
        rintro x (rfl | rfl)
        · exact e.2
        · exact h
      have h2 := Set.ncard_le_ncard this (Set.toFinite _)
      rwa [Set.ncard_pair hu.symm] at h2
  change (if G.IsHybrid e.1.2 then _ else _) = if G.HasOtherParent e then _ else _
  simp only [hiff]

variable {N : Net X}

/-- The taxa of the rooted network of a term, injected at their leaves, are the sampled lineages of the
labelled vertices. -/
theorem Net.taxaInj_toRootedNetwork [Fintype N.toGraph.Taxon] [DecidableEq N.toGraph.Taxon]
    (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length) (v : N.Vert) :
    NMSC.taxaInj (Net.toRootedNetwork hN h2) univ v =
      injOf N.toGraph (Subtype.val : N.toGraph.Taxon → X) v := by
  have hG := Net.isNetwork_toGraph hN h2
  have hlabel := MetricDigraph.label_toRootedNetwork_leaf hG
  unfold injOf NMSC.taxaInj
  cases hv : N.toGraph.label v with
  | none =>
    simp only
    ext A
    simp only [mem_image, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_exists,
      not_and]
    rintro x hx -
    have := hlabel x
    change N.toGraph.label ((Net.toRootedNetwork hN h2).leaf x) = _ at this
    rw [hx, hv] at this
    cases this
  | some x =>
    simp only
    ext A
    simp only [sampledAt, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      have := hlabel y
      change N.toGraph.label ((Net.toRootedNetwork hN h2).leaf y) = _ at this
      rw [hy, hv] at this
      exact (Option.some.inj this).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      have := hlabel y
      refine hG.labelled.label_injective _ _ x (by rw [← hy]; exact this) hv

/-- **The term-based coalescent is the general one.** For a well-formed network term, the distribution of
gene trees under the coalescent on the term, `Net.geneTreeDist`, with one lineage per taxon, is the general
network multispecies coalescent `Phylogenetics.geneTreeDist` of its rooted network, at inheritance
correlation `0`. -/
theorem Net.geneTreeDist_toRootedNetwork [instE : Fintype N.toGraph.Arc] [Fintype N.toGraph.Taxon]
    [DecidableEq N.toGraph.Taxon] (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length)
    (G : Finset (Finset N.toGraph.Taxon)) :
    Phylogenetics.geneTreeDist (Net.toRootedNetwork hN h2) N.metricData 0 G =
      N.geneTreeDist (Subtype.val : N.toGraph.Taxon → X) G := by
  obtain rfl : instE = Subtype.fintype (fun p : N.Vert × N.Vert => N.toGraph.Adj p.1 p.2) :=
    Subsingleton.elim _ _
  have hG := Net.isNetwork_toGraph hN h2
  have hP := Net.toRootedNetwork_isPhylogenetic hN h2
  have hroot : (Net.toRootedNetwork hN h2).root = N.root :=
    (MetricDigraph.eq_toRootedNetwork_root hG
      ((indeg_eq_zero_iff (G := N.toGraph)).2 N.not_adj_root)).symm
  have hF : ∀ F, NMSC.rootDist (Net.toRootedNetwork hN h2) N.metricData 0
      (NMSC.taxaInj (Net.toRootedNetwork hN h2) univ) F = N.forestDist Subtype.val F := by
    intro F
    have key := NMSC.rootDist_congr (N' := Net.toRootedNetwork hN h2) (θ' := N.metricData)
      (N := N.toGraph.pieceNetwork N.root) (θ := N.toGraph.pieceData) (ρ := 0)
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) hroot (fun _ => rfl)
      (fun e => MetricDigraph.metricData_inheritance_eq hG e)
      (NMSC.taxaInj (Net.toRootedNetwork hN h2) univ) F
    have hinj : (fun v => NMSC.taxaInj (Net.toRootedNetwork hN h2) univ ((Equiv.refl N.Vert) v)) =
        injOf N.toGraph (Subtype.val : N.toGraph.Taxon → X) :=
      funext fun v => Net.taxaInj_toRootedNetwork hN h2 v
    rw [hinj] at key
    exact key.trans (Net.law_toGraph Subtype.val N hN.1 F)
  rw [NMSC.geneTreeDist_eq_injDist hP, NMSC.injDist_eq_sum_rootDist]
  simp only [hF]
  rfl

/-- **The quartet concordance factors agree.** For a well-formed network term and four distinct taxa, the
concordance factor of the general coalescent on its rooted network, at inheritance correlation `0`, is the
concordance factor `Net.quartetCF` of the term. -/
theorem Net.nmscCF_toRootedNetwork [Fintype N.toGraph.Arc] [Fintype N.toGraph.Taxon]
    [DecidableEq N.toGraph.Taxon] (hN : N.WellFormed) (h2 : 2 ≤ N.leaves.length)
    {a b c e : N.toGraph.Taxon} (h : ({a, b, c, e} : Finset N.toGraph.Taxon).card = 4) :
    nmscCF (Net.toRootedNetwork hN h2) N.metricData 0 (quartetTree a b c e h) =
      N.quartetCF a.1 b.1 c.1 e.1 := by
  obtain ⟨hab, hac, hae, hbc, hbe, hce⟩ := ne_of_card_four h
  rw [quartetCF_eq_displays_sample N hN.2 Subtype.val hab hac hae hbc hbe hce]
  unfold nmscCF
  refine sum_congr rfl fun G _ => ?_
  rw [Net.geneTreeDist_toRootedNetwork hN h2 G]
  exact if_congr (displays_unroot_quartetTree_iff h) rfl rfl

end Terms

end Phylogenetics
