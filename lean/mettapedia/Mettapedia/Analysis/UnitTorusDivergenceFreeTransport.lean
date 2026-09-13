import Mettapedia.Analysis.UnitTorusContinuousRate

/-! # Zero mean of continuous incompressible transport on a unit torus -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusContinuousRate

open MeasureTheory
variable {d : Type*} [Fintype d]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_sum_mul_rate_eq_zero (f : T → ℝ) (df b db : d → T → ℝ)
    (shift : d → ℝ → T) (hf : Continuous f) (hdf : ∀ j, Continuous (df j))
    (hb : ∀ j, Continuous (b j)) (hdb : ∀ j, Continuous (db j))
    (hs : ∀ j, Continuous (shift j)) (hs0 : ∀ j, shift j 0 = 0)
    (hf' : ∀ j x h, HasDerivAt (fun t ↦ f (x + shift j t)) (df j (x + shift j h)) h)
    (hb' : ∀ j x h, HasDerivAt (fun t ↦ b j (x + shift j t)) (db j (x + shift j h)) h)
    (hdiv : ∀ x, ∑ j, db j x = 0) :
    (∫ x : T, ∑ j, b j x * df j x) = 0 := by
  have hi (j : d) : Integrable (fun x : T ↦ b j x * df j x) :=
    ((hb j).mul (hdf j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj (j : d) : Integrable (fun x : T ↦ f x * db j x) :=
    (hf.mul (hdb j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (j : d) : (∫ x : T, b j x * df j x) = -(∫ x : T, f x * db j x) := by
    simpa only [mul_comm (b j _) (df j _)] using
      integral_rate_mul f (b j) (df j) (db j) (shift j) hf (hb j) (hdf j) (hdb j)
        (hs j) (hs0 j) (hf' j) (hb' j)
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ ↦ hj j)]
  simp only [← Finset.mul_sum, hdiv, mul_zero, integral_zero, neg_zero]

end Mettapedia.Analysis.UnitTorusContinuousRate
