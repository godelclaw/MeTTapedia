import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialTheorems
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialBKMIntegrand

/-!
# The spatial essential-supremum BKM integrand of the Fourier solutions

The pancake route measures vorticity by the spatial essential supremum before
integrating in time. For the Fourier solutions the vorticity is continuous on
the torus and the Haar measure is positive on open sets, so the essential
supremum is the supremum, attained on the compact torus: the route's
integrand is the vorticity supremum `vorticitySup` of the continuation
theorems, at every time before the end of a tame solution.

Consequently global regularity of the Fourier class is exactly the
finite-horizon bound on the time integral of the route's integrand, and that
bound gives the official periodic statement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierBKMIntegrand

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakeCurlOutputTail LocalLowDiffusionBudget
open PancakeHigherDerivativeMoments FourierVorticitySupContinuation FourierTameContinuation
open FourierGlobalSolution FourierRegularityEquivalence FourierOfficialTheorems
open FourierDyadicBlockContinuation SpatialBKMIntegrand OfficialPeriodicProblem

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The vorticity of a coefficient curve as the space-time field of the route. -/
def vorticityField (c : ℝ → FourierVelocity) : ℝ → T3 → EuclideanSpace ℝ (Fin 3) :=
  fun t x ↦ fullVorticity (c t) x

/-- **The spatial essential-supremum integrand is the vorticity supremum.** -/
theorem spatialBKMIntegrand_eq_vorticitySup (c : ℝ → FourierVelocity) {t : ℝ}
    (hu : Summable (fourierMoment 1 (c t))) :
    spatialBKMIntegrand volume (vorticityField c) t = vorticitySup (c t) := by
  have hcont : Continuous (vorticityField c t) := continuous_fullVorticity (c t) hu
  obtain ⟨x₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont.norm.continuousOn
  have hmax' : ∀ x, ‖fullVorticity (c t) x‖ ≤ ‖fullVorticity (c t) x₀‖ := fun x ↦ hmax (mem_univ x)
  have h1 : spatialEssentialSupNorm volume (vorticityField c) t =
      ENNReal.ofReal ‖fullVorticity (c t) x₀‖ := by
    rw [spatialEssentialSupNorm_eq_iSup volume (vorticityField c) t hcont]
    exact le_antisymm (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal (hmax' x))
      (le_iSup (fun x ↦ ENNReal.ofReal ‖vorticityField c t x‖) x₀)
  have h2 : vorticitySup (c t) = ‖fullVorticity (c t) x₀‖ :=
    le_antisymm (ciSup_le hmax') (norm_fullVorticity_le_vorticitySup (c t) hu x₀)
  rw [spatialBKMIntegrand, h1, ENNReal.toReal_ofReal (norm_nonneg _), h2]

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- Along a tame solution the route's integrand is the vorticity supremum on
every interval before the end time. -/
theorem integral_spatialBKM_eq (hm : 7 ≤ m) {T : ℝ} (c : TameSolutionOn nu m u₀ T) {τ : ℝ}
    (hτ : τ ∈ Ico (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..τ, spatialBKMIntegrand volume (vorticityField c.coefficients) t =
      ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) := by
  obtain ⟨S, hτS, _, B, s, hsc, g, _, hg, hu⟩ := exists_local_envelope m hm c τ hτ
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le hτ.1] at ht
  apply spatialBKMIntegrand_eq_vorticitySup
  rw [← hsc]
  exact hg.of_nonneg_of_le (fun k ↦ fourierMoment_nonneg _ _ _) fun k ↦
    (fourierMoment_mono _ (by norm_num) k).trans (hu t ⟨ht.1, ht.2.trans hτS.le⟩ k)

/-- **Regularity is the finite-horizon bound on the route's integrand.** -/
theorem periodicRegularity_iff_spatialBKM (hm : 7 ≤ m) :
    PeriodicRegularity m ↔ ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ ∈ Ico (0 : ℝ) T,
        ∫ t in (0 : ℝ)..τ, spatialBKMIntegrand volume (vorticityField c.coefficients) t ≤ A := by
  rw [periodicRegularity_iff_vorticitySup hm]
  refine forall₂_congr fun nu _ ↦ forall₂_congr fun u₀ _ ↦ forall₂_congr fun H _ ↦
    exists_congr fun A ↦ forall₂_congr fun T _ ↦ forall_congr' fun c ↦
      forall₂_congr fun τ hτ ↦ ?_
  rw [integral_spatialBKM_eq hm c hτ]

/-- **The route's integrand bound gives the official statement.** -/
theorem periodicStatementB_of_spatialBKM (hm : 7 ≤ m)
    (h : ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ ∈ Ico (0 : ℝ) T,
        ∫ t in (0 : ℝ)..τ, spatialBKMIntegrand volume (vorticityField c.coefficients) t ≤ A) :
    PeriodicStatementB :=
  periodicStatementB_of_periodicRegularity hm ((periodicRegularity_iff_spatialBKM hm).mpr h)

end Mettapedia.FluidDynamics.NavierStokes.FourierBKMIntegrand
