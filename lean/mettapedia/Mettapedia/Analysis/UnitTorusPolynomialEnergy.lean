import Mettapedia.Analysis.UnitTorusFourierUniqueness
import Mettapedia.Analysis.UnitTorusFourierEnergy

/-!
# Finite Fourier polynomial energy and multiplier bounds

Parseval bounds a finite family of multiplier outputs by one input energy.
There is no factor for the number of frequencies or output entries.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusPolynomialEnergy

open MeasureTheory UnitAddTorus UnitTorusFourierUniqueness UnitTorusFourierEnergy
variable {d ι : Type*} [Fintype d] [Fintype ι]
local notation "T" => UnitAddTorus d
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_norm_polynomial_sq (P : Finset (d → ℤ)) (a : (d → ℤ) → ℂ) :
    (∫ x : T, ‖polynomial P a x‖ ^ 2) = ∑ q ∈ P, ‖a q‖ ^ 2 := by
  classical
  have h := hasSum_norm_mFourierCoeff_sq (polynomial P a)
    ((polynomial P a).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [← h.tsum_eq]
  simp_rw [mFourierCoeff_polynomial]
  rw [tsum_eq_sum (s := P) (fun q hq ↦ by simp [hq])]
  exact Finset.sum_congr rfl (fun q hq ↦ by simp [hq])

theorem sum_integral_multiplier_sq_le (P : Finset (d → ℤ)) (a : (d → ℤ) → ℂ)
    (m : ι → (d → ℤ) → ℂ) (L : ℝ)
    (hL : ∀ q ∈ P, (∑ j, ‖m j q‖ ^ 2) ≤ L) :
    (∑ j, ∫ x : T, ‖polynomial P (fun q ↦ m j q * a q) x‖ ^ 2) ≤
      L * ∫ x : T, ‖polynomial P a x‖ ^ 2 := by
  simp_rw [integral_norm_polynomial_sq, norm_mul, mul_pow]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hL q hq) (sq_nonneg _)

end Mettapedia.Analysis.UnitTorusPolynomialEnergy
