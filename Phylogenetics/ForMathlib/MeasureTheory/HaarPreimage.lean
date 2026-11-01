module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Preimages of null sets under surjective linear maps

The image of an additive Haar measure under a surjective linear map is a multiple of an additive Haar
measure, so the preimage of a null set is null. The factor may be infinite, but that does not matter on a
null set.

## Main results

* `addHaar_preimage_eq_zero_of_surjective`: preimages of null sets are null.
* `MeasureTheory.Measure.prod_pi_volume_preimage_eq_zero`: the form for the coordinates
  `(ι → ℝ) × (κ → ℝ)`, with the product of Lebesgue measures.
-/

@[expose] public section

open MeasureTheory Measure

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The preimage of a null set under a surjective linear map is null, for additive Haar measures. -/
theorem addHaar_preimage_eq_zero_of_surjective (L : E →ₗ[ℝ] F) (hL : Function.Surjective L)
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] {s : Set F}
    (hs : ν s = 0) : μ (L ⁻¹' s) = 0 := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨c, -, hc⟩ := L.exists_map_addHaar_eq_smul_addHaar μ ν hL
  have hm : Measurable L := L.continuous_of_finiteDimensional.measurable
  refine measure_mono_null (Set.preimage_mono (subset_toMeasurable ν s)) ?_
  rw [← Measure.map_apply hm (measurableSet_toMeasurable ν s), hc, Measure.smul_apply,
    measure_toMeasurable, hs, smul_zero]

end LinearMap

namespace MeasureTheory.Measure

/-- The preimage of a null set under a surjective linear map is null, in coordinates `(ι → ℝ) × (κ → ℝ)`
with the product of Lebesgue measures. -/
theorem prod_pi_volume_preimage_eq_zero {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] (L : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ((ι' → ℝ) × (κ' → ℝ))) (hL : Function.Surjective L)
    {s : Set ((ι' → ℝ) × (κ' → ℝ))}
    (hs : ((Measure.pi fun _ : ι' => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : κ' => (volume : Measure ℝ))) s = 0) :
    ((Measure.pi fun _ : ι => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : κ => (volume : Measure ℝ))) (L ⁻¹' s) = 0 :=
  L.addHaar_preimage_eq_zero_of_surjective hL _ _ hs

end MeasureTheory.Measure
