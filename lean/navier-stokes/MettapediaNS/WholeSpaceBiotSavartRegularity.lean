import Euler.DivCurlTensorRecovery
import MettapediaNS.WholeSpaceStrain
import MettapediaNS.WholeSpacePressure

/-!
# All-order regularity of the constructed Biot–Savart velocity

OpenAI's div–curl recovery theorem supplies every actual square-integrable
Fréchet derivative from the smooth finite-energy velocity and compact curl
already constructed using Alpöge–Buckmaster's potential theory. No derivative
budget or evolution law is inserted as a structure field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart

open MeasureTheory EulerSmoothLimit EulerLpTranslation EulerOrdinarySobolev
  EulerMeanSolenoidal EulerVectorCalculus EulerMeanCutoffCurl
  WholeSpaceViscousEnergy SpatialBKMIntegrand
open scoped ContDiff

theorem hasCompactSupport_vectorCurl_velocity {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (hd : ∀ x, divergence vort x = 0) :
    HasCompactSupport (vectorCurl (velocity vort)) := by
  simpa only [show vectorCurl (velocity vort) = vort from
    funext (vectorCurl_velocity_eq hvort hc hd)] using hc

/-- The upstream smooth-field object is constructed from the given vorticity. -/
def smoothVelocity (vort : Space → Space) (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) :
    SmoothL2Field Space :=
  EulerComparatorRecovery.smoothL2Field_of_curl_compact (velocity vort)
    (contDiff_velocity hvort hc) (memLp_velocity hvort hc)
    (divergence_velocity_eq_zero hvort hc hd)
    (hasCompactSupport_vectorCurl_velocity hvort hc hd)

@[simp] theorem smoothVelocity_field (vort : Space → Space) (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) :
    (smoothVelocity vort hvort hc hd).field = velocity vort := rfl

theorem memLp_iteratedFDeriv_velocity {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (velocity vort)) 2 volume :=
  (smoothVelocity vort hvort hc hd).integrable n

theorem smoothVelocity_mem_solenoidal {vort : Space → Space} (hvort : ContDiff ℝ ∞ vort)
    (hc : HasCompactSupport vort) (hd : ∀ x, divergence vort x = 0) :
    (smoothVelocity vort hvort hc hd).toLp ∈ solenoidalSpace :=
  smooth_mem_solenoidal _ (contDiff_velocity hvort hc)
    (smoothVelocity vort hvort hc hd).memLp (divergence_velocity_eq_zero hvort hc hd)

/-- The source's actual essential supremum is the constructed velocity's
vorticity norm. The constant time path is only notation for a spatial slice. -/
theorem spatialBKMIntegrand_eq_vorticityNorm {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (hd : ∀ x, divergence vort x = 0) :
    spatialBKMIntegrand volume (fun _ : ℝ ↦ vort) 0 =
      vorticityNorm (smoothVelocity vort hvort hc hd) := by
  have hcurl : curlField (velocity vort) = vort := funext (curlField_velocity_eq hvort hc hd)
  simpa only [smoothVelocity_field, hcurl] using
    WholeSpaceBKM.spatialBKMIntegrand_curl_eq_vorticityNorm
      (fun _ : ℝ ↦ smoothVelocity vort hvort hc hd) 0

theorem norm_fderiv_velocity_le_spatialBKMIntegrand {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (hd : ∀ x, divergence vort x = 0) (x : Space) :
    ‖fderiv ℝ (velocity vort) x‖ ≤ logarithmicGradientConstant *
      (1 + ‖(smoothVelocity vort hvort hc hd).toLp‖ +
        spatialBKMIntegrand volume (fun _ : ℝ ↦ vort) 0 *
          Real.log (Real.exp 1 + tensorNorm 3 (smoothVelocity vort hvort hc hd))) := by
  rw [spatialBKMIntegrand_eq_vorticityNorm hvort hc hd]
  exact logarithmic_gradient_bound_solenoidal (smoothVelocity vort hvort hc hd) _
    (smoothVelocity_mem_solenoidal hvort hc hd)
    ((vorticityNorm_le_iff _ _).mp le_rfl) x

/-- The velocity, all its L² jets, and the pressure are constructed. Only
ordinary source admissibility remains; this is a spatial production estimate,
not a bound on a Navier–Stokes trajectory up to its possible singular time. -/
theorem h3_projectedProduction_velocity_le {vort : Space → Space}
    (hvort : ContDiff ℝ ∞ vort) (hc : HasCompactSupport vort)
    (hd : ∀ x, divergence vort x = 0) (ν : ℝ) :
    let A := smoothVelocity vort hvort hc hd
    integerEnergyProduction 3 A (projectedNavierStokesRhs ν A) +
        2 * ν * wordDissipation 3 A ≤
      gradientEnergyConstant * (logarithmicGradientConstant *
        (1 + ‖A.toLp‖ + spatialBKMIntegrand volume (fun _ : ℝ ↦ vort) 0 *
          Real.log (Real.exp 1 + tensorNorm 3 A))) * wordEnergy 3 A :=
  h3_projectedProduction_add_dissipation_le ν (smoothVelocity vort hvort hc hd) _
    (norm_fderiv_velocity_le_spatialBKMIntegrand hvort hc hd)
    (divergence_velocity_eq_zero hvort hc hd)

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBiotSavart
