import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedDivCurl

/-!
# Radial dissipation pays the mixed vorticity-gradient cost

The weighted div–curl flux is absorbed by radial eighth-moment dissipation,
leaving the sixth vorticity moment and squared nonlinear advection. Combining
this with the angular helicity estimate charges radial and angular derivatives
once each. No time-integrated bound for the remaining advection is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMixedGradientBudget

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeBlockReality LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalVorticityEighthMoment HelicityAngularSource HelicityAngularBudget LocalWeightedDivCurl

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sixthMoment (u : FourierVelocity) : ℝ := ∫ x : T3, ‖fullVorticity u x‖ ^ 6

def advectionSquareIntegral (u : FourierVelocity) : ℝ := ∫ x : T3, ‖advection u x‖ ^ 2

def weightedFlux (u : FourierVelocity) (x : T3) : ℝ :=
  -4 * (‖fullVorticity u x‖ ^ 2 *
    ∑ j : Fin 3, ⟪fullVorticity u x, fullCurlGradient u j x⟫ * advection u x j)

theorem continuous_weightedFlux (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (weightedFlux u) := by
  have hw := continuous_fullVorticity u hu
  apply continuous_const.mul
  apply (hw.norm.pow 2).mul
  exact continuous_finsetSum _ (fun j _ ↦
    (hw.inner (LocalSquaredGapGradient.continuous_fullCurlGradient u j)).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) j).comp (continuous_advection u)))

/-- The div–curl correction uses the radial, not the angular, dissipation. -/
theorem weightedFlux_le (u : FourierVelocity) (x : T3) (ε : ℝ) (hε : 0 < ε) :
    weightedFlux u x ≤ ε * radialGradientDensity u x + (4 / ε) * ‖advection u x‖ ^ 2 := by
  have hy (a b : ℝ) : -4 * a * b ≤ ε * a ^ 2 + (4 / ε) * b ^ 2 := by
    have h : -4 * a * b ≤ (ε ^ 2 * a ^ 2 + 4 * b ^ 2) / ε :=
      (le_div_iff₀ hε).mpr (by nlinarith only [sq_nonneg (ε * a + 2 * b)])
    convert h using 1
    field_simp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j (_ : j ∈ Finset.univ) ↦
    hy (‖fullVorticity u x‖ ^ 2 * ⟪fullVorticity u x, fullCurlGradient u j x⟫) (advection u x j))
  calc
    weightedFlux u x = ∑ j : Fin 3,
        -4 * (‖fullVorticity u x‖ ^ 2 * ⟪fullVorticity u x, fullCurlGradient u j x⟫) *
          advection u x j := by simp only [weightedFlux, Fin.sum_univ_three]; ring
    _ ≤ _ := hs
    _ = _ := by
      rw [EuclideanSpace.real_norm_sq_eq (advection u x)]
      simp only [radialGradientDensity, Fin.sum_univ_three]
      ring

theorem mixedGradientCost_eq_add_flux (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    mixedGradientCost u = sixthMoment u + ∫ x : T3, weightedFlux u x := by
  rw [mixedGradientCost_eq u hu hd hr]
  simp only [sixthMoment, weightedFlux, integral_const_mul]
  ring

theorem mixedGradientCost_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (ε : ℝ) (hε : 0 < ε) :
    mixedGradientCost u ≤ sixthMoment u + ε * radialDissipation u +
      (4 / ε) * advectionSquareIntegral u := by
  have hu1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hu
  have hF : Integrable (weightedFlux u) :=
    (continuous_weightedFlux u hu1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : Integrable (fun x : T3 ↦ ‖advection u x‖ ^ 2) :=
    ((continuous_advection u).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRA : Integrable (fun x : T3 ↦ ε * radialGradientDensity u x +
      (4 / ε) * ‖advection u x‖ ^ 2) := (hR.const_mul ε).add (hA.const_mul (4 / ε))
  have h := integral_mono hF hRA (fun x ↦ weightedFlux_le u x ε hε)
  rw [integral_add (hR.const_mul ε) (hA.const_mul (4 / ε)), integral_const_mul,
    integral_const_mul] at h
  rw [mixedGradientCost_eq_add_flux u hu hd hr]
  change _ ≤ sixthMoment u + ε * (∫ x : T3, radialGradientDensity u x) +
    (4 / ε) * (∫ x : T3, ‖advection u x‖ ^ 2)
  linarith

/-- The mixed cost is eliminated from the angular source estimate. Radial
and angular dissipation recombine with exactly one coefficient `η`. -/
theorem weightedSource_le_dissipation_advection (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (η : ℝ) (hη : 0 < η) :
    weightedSource u ≤ η * weightedPalinstrophy u + sixthMoment u / η +
      4 * advectionSquareIntegral u / η ^ 3 := by
  have hM := div_le_div_of_nonneg_right
    (mixedGradientCost_le u hu hd hr (η ^ 2) (sq_pos_of_pos hη)) (le_of_lt hη)
  calc
    weightedSource u ≤ η * (weightedPalinstrophy u - radialDissipation u) +
        mixedGradientCost u / η := weightedSource_le u hu hd hr η hη
    _ ≤ η * (weightedPalinstrophy u - radialDissipation u) +
        (sixthMoment u + η ^ 2 * radialDissipation u +
          (4 / η ^ 2) * advectionSquareIntegral u) / η := add_le_add le_rfl hM
    _ = _ := by field_simp; ring

end Mettapedia.FluidDynamics.NavierStokes.LocalMixedGradientBudget
