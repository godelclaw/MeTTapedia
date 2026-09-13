import Mettapedia.Analysis.AngularCurlDecomposition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedCurlCancellation

/-!
# Angular curl cost for the actual vorticity

The polynomial angular curl retains the scaled curl-helicity pairing,
but its spatial cost is bounded by twice the angular octic dissipation.
This is a different functional from the full regularized projection cost.
The exact stretching identity below retains the spectral defect; no
coercive evolving energy or time-integrated budget is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAngularCurlBudget

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalVorticityEighthMoment GaussianRootWeightedIncrement

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def angularCurl (u : FourierVelocity) (x : T3) : R3 :=
  AngularCurlDecomposition.angularCurl (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

def angularCurlDensity (u : FourierVelocity) (x : T3) : ℝ :=
  AngularCurlDecomposition.angularCurlDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

def angularCurlEnergy (u : FourierVelocity) : ℝ := ∫ x : T3, angularCurlDensity u x

def angularHelicityIntegral (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 2 *
    (∑ j : Fin 3, fullVorticity u x j * ⟪fullVorticity u x, fullCurlGradient u j x⟫) *
      ⟪fullVorticity u x, angularCurl u x⟫

theorem angularCurlDensity_nonneg (u : FourierVelocity) (x : T3) :
    0 ≤ angularCurlDensity u x := AngularCurlDecomposition.angularCurlDensity_nonneg _ _

theorem angularCurlDensity_le (u : FourierVelocity) (x : T3) :
    angularCurlDensity u x ≤
      2 * (weightedPalinstrophyDensity u x - radialGradientDensity u x) :=
  AngularCurlDecomposition.angularCurlDensity_le _ _

theorem continuous_angularCurlDensity (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (angularCurlDensity u) :=
  AngularCurlDecomposition.continuous_angularCurlDensity _ _ (continuous_fullVorticity u hu)
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)

theorem angularCurlEnergy_nonneg (u : FourierVelocity) : 0 ≤ angularCurlEnergy u :=
  integral_nonneg (angularCurlDensity_nonneg u)

theorem angularCurlEnergy_le (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    angularCurlEnergy u ≤ 2 * (weightedPalinstrophy u - radialDissipation u) := by
  have hG : Integrable (weightedPalinstrophyDensity u) :=
    (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hR : Integrable (radialGradientDensity u) :=
    (continuous_radialGradientDensity u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (angularCurlDensity u) := (continuous_angularCurlDensity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : T3, 2 * (weightedPalinstrophyDensity u x - radialGradientDensity u x) :=
      integral_mono hK ((hG.sub hR).const_mul 2) (angularCurlDensity_le u)
    _ = _ := by rw [integral_const_mul, integral_sub hG hR]; rfl

theorem angularHelicityIntegral_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    angularHelicityIntegral u = longitudinalHelicityIntegral u := by
  apply integral_congr_ae
  filter_upwards with x
  rw [fullVorticity_curl_eq_curlJet u hu]
  exact (AngularCurlDecomposition.weighted_helicity_eq _ _ _).symm

/-- The angular substitution preserves the exact signed source, including
the unresolved spectral mismatch. It is not an estimate of that mismatch. -/
theorem stretching_spectral_identity (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0) (κ : ℝ) :
    κ * stretching u = -6 * angularHelicityIntegral u - weightedStrainSpectralDefect κ u := by
  rw [angularHelicityIntegral_eq u (summable_fourierMoment_of_le u (by omega : 2 ≤ 4) hu)]
  exact LocalWeightedCurlCancellation.stretching_spectral_identity u hu hd κ

end Mettapedia.FluidDynamics.NavierStokes.LocalAngularCurlBudget
