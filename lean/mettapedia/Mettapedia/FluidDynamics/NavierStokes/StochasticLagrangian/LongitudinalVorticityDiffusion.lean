import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLongitudinalVorticity

/-!
# Ordinary diffusion of longitudinal vorticity

The Laplacian below is defined by ordinary second derivatives of the
reconstructed field. Its product rule identifies the viscous cross term
in the material evolution, with coefficient `-2ν`. No sign or integrable
majorant is assigned to this cross term or the velocity-curvature source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalVorticityDiffusion

open Mettapedia.Analysis LongitudinalJetEvolution
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeInfiniteSpatialLaplacian
open PancakeFourierTranslationCurve PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeInfiniteSpatialCurl PancakeDyadicDirectionEvolution PancakeFourierMaterialPaths
open FullLambVector FullVorticityGradientTransport LocalLongitudinalVorticity
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalWeightedCurlCancellation
open LocalJointDiffusionBudget LocalVorticityGradientEvolution
open PancakeTransverseEnergyFreezing PancakeHaarTransportRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def thirdGradient (u : FourierVelocity) (i j k : Fin 3) (x : T3) : R3 :=
  mixedGradient (indexedDerivativeCoeff id i u) j k x

theorem hasDerivAt_mixedGradient_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (i j k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ mixedGradient u i j (x + coordinateShift k t))
      (thirdGradient u i j k (x + coordinateShift k h)) h :=
  hasDerivAt_velocityJet_shift _ (summable_fourierMoment_derivative 2 u hu i) j k x h

def longitudinalGradient (u : FourierVelocity) (k : Fin 3) (x : T3) : R3 :=
  rate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fullCurlGradient u k x) (fun j ↦ mixedGradient (fourierCurl u) j k x)

def longitudinalSecond (u : FourierVelocity) (k : Fin 3) (x : T3) : R3 :=
  rate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (mixedGradient (fourierCurl u) k k x) (fun j ↦ thirdGradient (fourierCurl u) j k k x) +
      2 • longitudinal (fullCurlGradient u k x) (fun j ↦ mixedGradient (fourierCurl u) j k x)

theorem hasDerivAt_longitudinal_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ longitudinalVorticity u (x + coordinateShift k t))
      (longitudinalGradient u k (x + coordinateShift k h)) h :=
  hasDerivAt_longitudinal
    (hasDerivAt_fullVorticity_shift_second u
      (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) k x h)
    (fun j ↦ hasDerivAt_fullCurlGradient_shift_mixed u hu j k x h)

theorem deriv_longitudinal_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (k : Fin 3) (x : T3) (h : ℝ) :
    deriv (fun t ↦ longitudinalVorticity u (x + coordinateShift k t)) h =
      longitudinalGradient u k (x + coordinateShift k h) :=
  (hasDerivAt_longitudinal_shift u hu k x h).deriv

theorem hasDerivAt_longitudinalGradient_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ longitudinalGradient u k (x + coordinateShift k t))
      (longitudinalSecond u k (x + coordinateShift k h)) h := by
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 4) hu
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  exact hasDerivAt_rate
    (hasDerivAt_fullVorticity_shift_second u hu2 k x h)
    (fun j ↦ hasDerivAt_fullCurlGradient_shift_mixed u hu3 j k x h)
    (hasDerivAt_fullCurlGradient_shift_mixed u hu3 k k x h)
    (fun j ↦ hasDerivAt_mixedGradient_shift (fourierCurl u)
      (summable_fourierMoment_curl 3 u hu) j k k x h)

theorem deriv_deriv_longitudinal_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (k : Fin 3) (x : T3) :
    deriv (deriv (fun t ↦ longitudinalVorticity u (x + coordinateShift k t))) 0 =
      longitudinalSecond u k x := by
  have he : deriv (fun t ↦ longitudinalVorticity u (x + coordinateShift k t)) =
      fun h ↦ longitudinalGradient u k (x + coordinateShift k h) :=
    funext (deriv_longitudinal_shift u
      (summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu) k x)
  rw [he]
  simpa only [coordinateShift_zero, add_zero] using
    (hasDerivAt_longitudinalGradient_shift u hu k x 0).deriv

/-- Ordinary real coordinate Laplacian, not an independently prescribed jet. -/
def longitudinalLaplacian (u : FourierVelocity) (x : T3) : R3 :=
  ∑ k : Fin 3, deriv (deriv (fun t ↦ longitudinalVorticity u (x + coordinateShift k t))) 0

def viscousCross (u : FourierVelocity) (x : T3) : R3 :=
  diffusionCross (fun k ↦ fullCurlGradient u k x) (fun j k ↦ mixedGradient (fourierCurl u) j k x)

theorem sum_mixedGradient_curl (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (x : T3) :
    (∑ k : Fin 3, mixedGradient (fourierCurl u) k k x) = fullVorticityLaplacian u x := by
  exact sum_fullCurlSecond u hu x

theorem sum_thirdGradient_curl (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (j : Fin 3) (x : T3) :
    (∑ k : Fin 3, thirdGradient (fourierCurl u) j k k x) = gradientLaplacian u j x := by
  have hd := summable_fourierMoment_derivative 2 (fourierCurl u)
    (summable_fourierMoment_curl 3 u hu) j
  simp only [gradientLaplacian, spatialLaplacian, coordinateDerivative2_fullFourierField _ hd,
    map_sum, thirdGradient, mixedGradient, velocityJet]

theorem longitudinalLaplacian_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (x : T3) :
    longitudinalLaplacian u x = viscousRate u x + 2 • viscousCross u x := by
  have hu3 := summable_fourierMoment_of_le u (by omega : 3 ≤ 4) hu
  simp only [longitudinalLaplacian, deriv_deriv_longitudinal_shift u hu]
  unfold longitudinalSecond viscousRate
  rw [← sum_mixedGradient_curl u hu3 x]
  simp_rw [← sum_thirdGradient_curl u hu _ x]
  simp only [rate, longitudinal, viscousCross, diffusionCross, Fin.sum_univ_three, PiLp.add_apply]
  module

theorem materialRate_sub_laplacian (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    materialRate ν u (fun j ↦ PancakeInfiniteRealCurl.realFullField u x j) x -
      ν • longitudinalLaplacian u x = inviscidRate u x - (2 * ν) • viscousCross u x := by
  rw [materialRate_eq ν u hu hd hr, longitudinalLaplacian_eq u hu]
  module

open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories

variable {ν T B : ℝ} {u₀ : FourierVelocity}

/-- The ordinary diffusion decomposition on the actual solution and material
trajectory. This is an evolution identity, not a regularity estimate. -/
theorem hasDerivAt_longitudinal_material_diffusion
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → Fin 3 → ℝ)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ longitudinalVorticity (s.coefficients τ) (torusPoint (X τ)))
      (ν • longitudinalLaplacian (s.coefficients t) (torusPoint (X t)) +
        inviscidRate (s.coefficients t) (torusPoint (X t)) -
          (2 * ν) • viscousCross (s.coefficients t) (torusPoint (X t))) t := by
  have h := hasDerivAt_longitudinal_material_split s g hg hSum hu X hX t ht
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  rw [longitudinalLaplacian_eq _ hm]
  have he : ν • (viscousRate (s.coefficients t) (torusPoint (X t)) +
      2 • viscousCross (s.coefficients t) (torusPoint (X t))) +
      inviscidRate (s.coefficients t) (torusPoint (X t)) -
      (2 * ν) • viscousCross (s.coefficients t) (torusPoint (X t)) =
      inviscidRate (s.coefficients t) (torusPoint (X t)) +
        ν • viscousRate (s.coefficients t) (torusPoint (X t)) := by module
  rw [he]
  exact h

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalVorticityDiffusion
