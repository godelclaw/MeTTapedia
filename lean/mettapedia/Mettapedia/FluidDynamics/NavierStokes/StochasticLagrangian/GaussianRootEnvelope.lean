import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePeriodicEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianSquaredRootLocalization

/-!
# The common pressure envelope applied to actual Gaussian localization

Both translated inputs and the frozen direction are the constructed
objects. The common almost-everywhere kernel bound controls every patch
and every target point simultaneously. No scalar-root derivative is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnvelope

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol LocalLowDiffusionBudget
open GaussianRootVorticity GaussianSquaredRootLocalization LocalGaussianPressurePartition
open PancakeBilinearPeriodization PressureDyadicPeriodization
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3
local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def rootLocalizationIntegrand (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (q : T6) (x : T3) (i : ↑centers) : C3 :=
  let c := rootPatch gamma chi modes u centers tau i
  let w := fun y ↦ complexifyVector (fullVorticity u y)
  let y := x - firstTorusDisplacement q
  let z := x - secondTorusDisplacement q
  let B := periodicKernel N hN t (localDirection chi modes u i.1) q
  ((c x : ℂ) * (c x : ℂ)) • B (w y) (w z) - B ((c y : ℂ) • w y) ((c z : ℂ) • w z)

theorem ae_sum_norm_rootLocalizationIntegrand_sq_le (N : ℝ) (hN : 0 < N) (t : ℝ)
    (M : T6 → ℝ) (hM : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ‖periodicKernel N hN t e q‖ ≤ M q)
    (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) :
    ∀ᵐ q : T6, ∀ x : T3,
      (∑ i : ↑centers, ‖rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i‖ ^ 2) ≤
      M q ^ 2 * ‖fullVorticity u (x - firstTorusDisplacement q)‖ ^ 2 *
        ‖fullVorticity u (x - secondTorusDisplacement q)‖ ^ 2 *
        (squaredPatchDifference gamma chi modes u centers tau x (x - firstTorusDisplacement q) +
          squaredPatchDifference gamma chi modes u centers tau x (x - secondTorusDisplacement q)) := by
  filter_upwards [hM] with q hq x
  exact sum_norm_rootLocalization_integrand_sq_le gamma chi modes u centers tau x
    (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)
    (fun i ↦ periodicKernel N hN t (localDirection chi modes u i.1) q) (M q)
    (fun i ↦ hq _ (PancakeSpectralFiniteDifference.topVector_norm _))

/-- The envelope and its summable costs are constructed, not additional localization hypotheses. -/
theorem exists_uniform_rootLocalization_envelope :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∃ M : (N : ℝ) → 0 < N → ℕ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N,
        (∀ n, (∀ q, 0 ≤ M N hN n q) ∧ Measurable (M N hN n) ∧
          Integrable (M N hN n) ∧ Integrable (fun q ↦ ‖q‖ * M N hN n q)) ∧
        Summable (fun n ↦ ∫ q : T6, M N hN n q) ∧
        (∑' n, ∫ q : T6, M N hN n q) ≤ C0 ∧
        Summable (fun n ↦ ∫ q : T6, ‖q‖ * M N hN n q) ∧
        (∑' n, ∫ q : T6, ‖q‖ * M N hN n q) ≤ C1 / N ∧
        ∀ gamma : ℝ, ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector, ∀ u : FourierVelocity,
        ∀ centers : Finset T3, ∀ tau : ℝ,
        ∀ᵐ q : T6, ∀ n : ℕ, ∀ x : T3,
          (∑ i : ↑centers, ‖rootLocalizationIntegrand N hN
            (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q x i‖ ^ 2) ≤
          M N hN n q ^ 2 * ‖fullVorticity u (x - firstTorusDisplacement q)‖ ^ 2 *
            ‖fullVorticity u (x - secondTorusDisplacement q)‖ ^ 2 *
            (squaredPatchDifference gamma chi modes u centers tau x (x - firstTorusDisplacement q) +
              squaredPatchDifference gamma chi modes u centers tau x (x - secondTorusDisplacement q)) := by
  obtain ⟨C0, C1, hC0, hC1, M, h⟩ := PressurePeriodicEnvelope.exists_uniform_dyadic_envelope
  refine ⟨C0, C1, hC0, hC1, M, ?_⟩
  intro N hN
  obtain ⟨hprop, hdom, hs0, hb0, hs1, hb1⟩ := h N hN
  refine ⟨hprop, hs0, hb0, hs1, hb1, ?_⟩
  intro gamma chi modes u centers tau
  apply ae_all_iff.mpr
  intro n
  exact ae_sum_norm_rootLocalizationIntegrand_sq_le N hN _ (M N hN n)
    (hdom.mono (fun _ hq ↦ hq n)) gamma chi modes u centers tau

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootEnvelope
