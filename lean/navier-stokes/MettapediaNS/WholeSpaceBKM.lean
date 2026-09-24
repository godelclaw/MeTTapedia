import Euler.OrdinaryLogarithmicGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialBKMIntegrand
import MettapediaNS.WholeSpaceViscousEnergy

/-!
# Whole-space BKM interface for the upstream logarithmic estimate

The analytic estimate is imported from `Euler.OrdinaryLogarithmicGradient`;
it assumes no Euler evolution equation. This module identifies the actual
coordinate curls and the spatial essential supremum used by the pancake
route with the upstream bounded-continuous-field norm.

All fields below live on Euclidean three-space and have the actual smooth
square-integrable jets required by `SmoothL2Field`. In particular, these
statements do not apply to a nonzero periodic lift by ignoring its failure
to be square-integrable on the whole space. No physical-time vorticity
budget or Navier–Stokes continuation theorem is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBKM

open MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerVectorCalculus EulerMeanCutoffCurl
  EulerOrdinarySobolev EulerMeanSolenoidal SpatialBKMIntegrand WholeSpaceViscousEnergy
open scoped ContDiff ENNReal

/-- The two libraries use the same coordinate curl on differentiable fields. -/
theorem curlField_eq_vectorCurl {u : Space → Space} {x : Space}
    (hu : DifferentiableAt ℝ u x) : curlField u x = vectorCurl u x := by
  ext i
  simp only [vectorCurl, curl_apply, partialDerivative, fderiv_coordinate u x hu]
  fin_cases i <;> simp [curlField]

/-- The upstream vorticity norm is exactly the existing spatial BKM integrand,
not merely an upper envelope. Finiteness is derived from the upstream field. -/
theorem spatialBKMIntegrand_curl_eq_vorticityNorm
    (A : ℝ → SmoothL2Field Space) (t : ℝ) :
    spatialBKMIntegrand volume (fun s ↦ curlField (A s).field) t =
      vorticityNorm (A t) := by
  have hcurl (s : ℝ) (x : Space) :
      curlField (A s).field x = vectorCurl (A s).field x :=
    curlField_eq_vectorCurl ((A s).smooth.differentiable (by simp) x)
  have hb (x : Space) : ‖curlField (A t).field x‖ ≤ vorticityNorm (A t) := by
    rw [hcurl]
    exact (vorticityNorm_le_iff (A t) _).mp le_rfl x
  have hf := spatialEssentialSupNorm_ne_top_of_bound volume
    (fun s ↦ curlField (A s).field) t (vorticityNorm (A t)) hb
  apply le_antisymm
  · exact spatialBKMIntegrand_le_of_bound volume _ t _ (vorticityNorm_nonneg _) hb
  · apply (vorticityNorm_le_iff (A t) _).mpr
    intro x
    rw [← hcurl]
    exact norm_le_spatialBKMIntegrand volume _ t
      (continuous_curlField_of_contDiff ((A t).smooth.of_le (by simp))) hf x

/-- The extended norm has the same value, so conversion to `ℝ` has not
silently replaced an infinite essential supremum by zero. -/
theorem spatialEssentialSupNorm_curl_eq_ofReal_vorticityNorm
    (A : ℝ → SmoothL2Field Space) (t : ℝ) :
    spatialEssentialSupNorm volume (fun s ↦ curlField (A s).field) t =
      ENNReal.ofReal (vorticityNorm (A t)) := by
  rw [← spatialBKMIntegrand_curl_eq_vorticityNorm A t]
  apply (ofReal_spatialBKMIntegrand_of_bound volume _ t (vorticityNorm (A t)) ?_).symm
  intro x
  rw [curlField_eq_vectorCurl ((A t).smooth.differentiable (by simp) x)]
  exact (vorticityNorm_le_iff (A t) _).mp le_rfl x

/-- Direct application of the upstream logarithmic gradient bound, using
the pancake route's actual spatial essential-supremum integrand. -/
theorem norm_fderiv_le_spatialBKMIntegrand
    (A : ℝ → SmoothL2Field Space) (t : ℝ)
    (hdiv : ∀ x, divergence (A t).field x = 0) (x : Space) :
    ‖fderiv ℝ (A t).field x‖ ≤ logarithmicGradientConstant *
      (1 + ‖(A t).toLp‖ +
        spatialBKMIntegrand volume (fun s ↦ curlField (A s).field) t *
          Real.log (Real.exp 1 + tensorNorm 3 (A t))) := by
  rw [spatialBKMIntegrand_curl_eq_vorticityNorm]
  exact logarithmic_gradient_bound (A t) hdiv (vorticityNorm (A t))
    ((vorticityNorm_le_iff (A t) _).mp le_rfl) x

/-- The same imported estimate for the existing transported-momentum
velocity, when its actual spatial slices have the upstream regularity.
The equality hypothesis identifies fields, not estimates or solution laws. -/
theorem norm_fderiv_le_transportedVorticityBKMIntegrand
    (M : TransportedMomentumData) (A : ℝ → SmoothL2Field Space)
    (hfield : ∀ s, (A s).field = M.u s) (t : ℝ)
    (hdiv : ∀ x, divergence (M.u t) x = 0) (x : Space) :
    ‖fderiv ℝ (M.u t) x‖ ≤ logarithmicGradientConstant *
      (1 + ‖(A t).toLp‖ + transportedVorticityBKMIntegrand M t *
        Real.log (Real.exp 1 + tensorNorm 3 (A t))) := by
  have h := norm_fderiv_le_spatialBKMIntegrand A t
    (by simpa only [hfield] using hdiv) x
  simpa only [hfield, transportedVorticityBKMIntegrand] using h

/-- The imported spatial logarithmic estimate and nonlinear energy estimate
combine for the full viscous right-hand side, retaining exact dissipation.
The remaining coefficient is the actual spatial BKM integrand. -/
theorem h3_energyProduction_add_dissipation_le_spatialBKMIntegrand
    (ν : ℝ) (A : ℝ → SmoothL2Field Space) (P : SmoothL2Field Space) (t : ℝ)
    (hdiv : ∀ x, divergence (A t).field x = 0)
    (hA : (A t).toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction 3 (A t) (navierStokesRhs ν (A t) P) +
        2 * ν * wordDissipation 3 (A t) ≤
      gradientEnergyConstant * (logarithmicGradientConstant *
        (1 + ‖(A t).toLp‖ +
          spatialBKMIntegrand volume (fun s ↦ curlField (A s).field) t *
            Real.log (Real.exp 1 + tensorNorm 3 (A t)))) * wordEnergy 3 (A t) :=
  h3_energyProduction_add_dissipation_le ν (A t) P _
    (norm_fderiv_le_spatialBKMIntegrand A t hdiv) hdiv hA hP

/-- Continuity of the existing integrand follows from the upstream jet-path
theorem; no new supremum-continuity argument is needed. -/
theorem continuous_spatialBKMIntegrand_curl
    (A : ℝ → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n)) :
    Continuous (spatialBKMIntegrand volume (fun t ↦ curlField (A t).field)) := by
  simp_rw [show spatialBKMIntegrand volume (fun t ↦ curlField (A t).field) =
      (fun t ↦ vorticityNorm (A t)) from
    funext (spatialBKMIntegrand_curl_eq_vorticityNorm A)]
  exact vorticityNorm_continuous A hA

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceBKM
