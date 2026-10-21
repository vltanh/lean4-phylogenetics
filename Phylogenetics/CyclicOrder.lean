module

public import Phylogenetics.Defs
import Mathlib.Data.Fin.Tuple.Sort
/-!
# Sorting and cyclic orders

* a tuple with distinct values has a permutation sorting it increasingly
  (`Phylogenetics.exists_perm_strictMono`), and only one (`Phylogenetics.eq_of_strictMono_comp`); a
  tuple sorted by a permutation has distinct values (`Phylogenetics.injective_of_strictMono_comp`),
  and if that permutation is a cyclic order `ord` up to rotation and reversal, so is every
  permutation sorting the tuple (`Phylogenetics.sameCyclicOrder_of_strictMono_comp`);
* `Phylogenetics.SameCyclicOrder` (equality of cyclic orders up to rotation and reversal) is
  symmetric and transitive. -/

@[expose] public noncomputable section

namespace Phylogenetics

/-! ### Sorting -/

/-- A tuple with distinct values has a permutation sorting it increasingly. -/
theorem exists_perm_strictMono {α : Type*} [LinearOrder α] {n : ℕ} {f : Fin n → α}
    (hf : Function.Injective f) : ∃ σ : Equiv.Perm (Fin n), StrictMono fun k => f (σ k) :=
  ⟨Tuple.sort f,
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)⟩

/-- A tuple that a permutation sorts strictly increasingly has distinct values. -/
theorem injective_of_strictMono_comp {α : Type*} [LinearOrder α] {n : ℕ} {f : Fin n → α}
    {τ : Equiv.Perm (Fin n)} (hτ : StrictMono fun k => f (τ k)) : Function.Injective f :=
  fun a b hab => by
    have h' : τ.symm a = τ.symm b := hτ.injective (by simp [hab])
    simpa using h'

/-- Two permutations that sort a tuple strictly increasingly are equal. -/
theorem eq_of_strictMono_comp {α : Type*} [LinearOrder α] {n : ℕ} {f : Fin n → α}
    {σ τ : Equiv.Perm (Fin n)} (hσ : StrictMono fun k => f (σ k))
    (hτ : StrictMono fun k => f (τ k)) : σ = τ := by
  have h := Tuple.unique_monotone (f := f) hσ.monotone hτ.monotone
  exact Equiv.ext fun k => injective_of_strictMono_comp hτ (congrFun h k)

/-- If a permutation `τ` sorts the tuple `f` strictly increasingly and is the cyclic order `ord` up
to rotation and reversal, then the values of `f` are distinct, and every permutation sorting them
is `ord` up to rotation and reversal. -/
theorem sameCyclicOrder_of_strictMono_comp {α : Type*} [LinearOrder α] {n : ℕ} {f : Fin n → α}
    {τ ord : Equiv.Perm (Fin n)} (hτ : StrictMono fun k => f (τ k))
    (hτo : SameCyclicOrder τ ord) :
    Function.Injective f ∧
      ∀ σ : Equiv.Perm (Fin n), StrictMono (fun k => f (σ k)) → SameCyclicOrder σ ord :=
  ⟨injective_of_strictMono_comp hτ, fun _ hσ => eq_of_strictMono_comp hσ hτ ▸ hτo⟩

/-! ### Cyclic orders -/

/-- Equality of cyclic orders up to rotation and reversal is symmetric. -/
theorem SameCyclicOrder.symm {d : ℕ} [NeZero d] {σ τ : Equiv.Perm (Fin d)}
    (h : SameCyclicOrder σ τ) : SameCyclicOrder τ σ := by
  obtain ⟨r, hr | hr⟩ := h
  · exact ⟨-r, Or.inl fun k => by rw [hr, neg_add_cancel_right]⟩
  · exact ⟨r, Or.inr fun k => by rw [hr, sub_sub_cancel]⟩

/-- Equality of cyclic orders up to rotation and reversal is transitive. -/
theorem SameCyclicOrder.trans {d : ℕ} [NeZero d] {σ τ ρ : Equiv.Perm (Fin d)}
    (h₁ : SameCyclicOrder σ τ) (h₂ : SameCyclicOrder τ ρ) : SameCyclicOrder σ ρ := by
  obtain ⟨r₁, h₁ | h₁⟩ := h₁ <;> obtain ⟨r₂, h₂ | h₂⟩ := h₂
  · exact ⟨r₁ + r₂, Or.inl fun k => by rw [h₁, h₂, add_assoc]⟩
  · exact ⟨r₂ - r₁, Or.inr fun k => by rw [h₁, h₂]; congr 1; abel⟩
  · exact ⟨r₁ + r₂, Or.inr fun k => by rw [h₁, h₂]; congr 1; abel⟩
  · exact ⟨r₂ - r₁, Or.inl fun k => by rw [h₁, h₂]; congr 1; abel⟩

end Phylogenetics
