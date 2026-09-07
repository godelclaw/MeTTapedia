import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalStrainReality
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierMaterialPaths

/-!
# Uniform spatial bounds for the lifted infinite velocity

A first absolute Fourier moment bounds the spatial Lipschitz constant.
The estimate holds on the whole real lift, not only in a chosen torus chart.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteVelocityLipschitz

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFourierMaterialPaths PancakeFrequencyProjectorCommutator
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeCurlOutputTail
open PancakeConcreteSmoothCellCutoff PancakeHigherDerivativeMoments
open PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem norm_realModeDot_le (q : Wavevector) (v : X3) :
    ‖realModeDot q v‖ ≤ 3 * ‖frequencyVec q‖ * ‖v‖ := by
  calc
    _ ≤ ∑ i : Fin 3, ‖(q i : ℝ) * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖frequencyVec q‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      gcongr
      · simpa only [← Complex.norm_real, Complex.ofReal_intCast] using norm_frequency_coordinate_le q i
      · exact norm_le_pi_norm v i
    _ = _ := by simp; ring

theorem norm_materialCharacterRate_le (q : Wavevector) (v : X3) (x : T3) :
    ‖unitTorusDerivativePhase * (realModeDot q v : ℂ) * UnitAddTorus.mFourier q x‖ ≤
      (3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖v‖ := by
  rw [norm_mul, norm_mul, norm_mFourier_apply, mul_one,
    norm_derivativePhase, Complex.norm_real]
  calc
    _ ≤ (2 * Real.pi) * (3 * ‖frequencyVec q‖ * ‖v‖) := by
      gcongr
      exact norm_realModeDot_le q v
    _ = _ := by ring

theorem norm_character_lift_sub_le (q : Wavevector) (x y : X3) :
    ‖UnitAddTorus.mFourier q (torusPoint x) - UnitAddTorus.mFourier q (torusPoint y)‖ ≤
      (3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖x - y‖ := by
  have hd (t : ℝ) := hasDerivAt_mFourier_torusPoint q
    (fun h i ↦ y i + h * (x i - y i)) (x - y) t (fun i ↦ by
      simpa only [Pi.sub_apply, id_eq, one_mul] using
        ((hasDerivAt_id t).mul_const (x i - y i)).const_add (y i))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hd t).hasDerivWithinAt)
    (fun t _ ↦ norm_materialCharacterRate_le q (x - y) _)
  simpa only [one_mul, zero_mul, add_zero, add_sub_cancel] using h

theorem norm_fullFourierField_le (u : FourierVelocity)
    (g : Wavevector → ℝ) (_hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, ‖u q‖ ≤ g q) (x : T3) :
    ‖fullFourierField id u x‖ ≤ ∑' q, g q := by
  have ha := hSum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hu
  rw [fullFourierField_apply id u ha]
  exact tsum_of_norm_bounded hSum.hasSum (fun q ↦ by
    simpa only [id_eq, norm_smul, norm_mFourier_apply, one_mul] using hu q)

theorem norm_fullFourierField_lift_sub_le (u : FourierVelocity)
    (g : Wavevector → ℝ) (_hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, fourierMoment 1 u q ≤ g q) (x y : X3) :
    ‖fullFourierField id u (torusPoint x) - fullFourierField id u (torusPoint y)‖ ≤
      (3 * (2 * Real.pi) * (∑' q, g q)) * ‖x - y‖ := by
  have hb (q) : ‖u q‖ ≤ g q :=
    (norm_coefficient_le_indexedFirstMoment id u q).trans (by
      simpa only [indexedFirstMoment_id] using hu q)
  have ha := hSum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  have hs (z : T3) : Summable (fun q ↦ UnitAddTorus.mFourier q z • u q) :=
    ha.of_norm_bounded (fun q ↦ by rw [norm_smul, norm_mFourier_apply, one_mul])
  simp only [fullFourierField_apply id u ha, id_eq]
  rw [← (hs (torusPoint x)).tsum_sub (hs (torusPoint y))]
  have hq (q) :
      ‖UnitAddTorus.mFourier q (torusPoint x) • u q -
        UnitAddTorus.mFourier q (torusPoint y) • u q‖ ≤
      (3 * (2 * Real.pi) * ‖x - y‖) * g q := by
    rw [← sub_smul, norm_smul]
    calc
      _ ≤ ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖x - y‖) *
          ‖coefficientVec (u q)‖ := by
        gcongr
        · exact norm_character_lift_sub_le q x y
        · exact norm_coefficient_sup_le_euclidean _
      _ ≤ (3 * (2 * Real.pi) * ‖x - y‖) * fourierMoment 1 u q := by
        simp only [fourierMoment, pow_one]
        nlinarith [mul_nonneg (norm_nonneg (coefficientVec (u q))) (norm_nonneg (x - y)),
          Real.pi_pos]
      _ ≤ _ := by gcongr; exact hu q
  calc
    _ ≤ ∑' q, (3 * (2 * Real.pi) * ‖x - y‖) * g q :=
      tsum_of_norm_bounded (hSum.mul_left _).hasSum hq
    _ = _ := by rw [tsum_mul_left]; ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteVelocityLipschitz
