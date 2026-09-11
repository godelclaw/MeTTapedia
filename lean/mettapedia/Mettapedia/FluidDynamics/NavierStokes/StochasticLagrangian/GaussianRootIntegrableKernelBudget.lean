import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootKernelBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicAction

/-!
# Gaussian root localization for integrable pressure kernels

The actual root-patch difference bound extends from finite continuous
pressure kernels to any operator-norm-integrable kernel. In particular it
applies to the corrected periodic dyadic family, without an unweighted
scalar-root gradient or inverse vorticity magnitude.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootIntegrableKernelBudget

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol
open PancakePeriodicCoherentSplit PancakeCurlOutputTail LocalLowDiffusionBudget
open GaussianRootVorticity GaussianRootPartition GaussianRootDifference GaussianRootDifferentiation
open GaussianRootKernelBudget
open PressureKernelAction (kernelAction)
open PressureIntegrableKernelAction
open Mettapedia.Analysis.BilinearKernelLocalization Mettapedia.Analysis.BilinearKernelIntegrability

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_rootLocalization_le (B : T6 → Op) (hB : Integrable B)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) (x : T3) :
    let c := rootPatch gamma chi modes u centers tau i
    let w := fun x ↦ complexifyVector (fullVorticity u x)
    ‖((c x : ℂ) * (c x : ℂ)) • kernelAction B w w x -
      kernelAction B (fun y ↦ (c y : ℂ) • w y) (fun y ↦ (c y : ℂ) • w y) x‖ ≤
      ∫ q : T6, ‖B q‖ * rootLocalizationDensity gamma chi modes u centers tau i
        x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) := by
  dsimp only
  have hcp := continuous_rootPatch gamma hg chi modes u hu centers hc tau i
  have ha := continuous_rootFieldFactor gamma hg chi modes u hu centers hc tau i
  have hw := continuous_fullVorticity u hu
  have hwc : Continuous (fun x ↦ complexifyVector (fullVorticity u x)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  have hcc : Continuous (fun x ↦ (rootPatch gamma chi modes u centers tau i x : ℂ)) :=
    Complex.continuous_ofReal.comp hcp
  have hdom : Integrable (fun q : T6 ↦ ‖B q‖ * rootLocalizationDensity gamma chi modes u centers tau i
      x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)) := by
    apply integrable_norm_kernel_mul_continuous B _ hB
    unfold rootLocalizationDensity rootDifferenceCost
    fun_prop
  rw [kernelAction_localization _ _ _ _ _ x hB hwc hwc hcc hcc]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hdom
  filter_upwards [] with q
  rw [← smul_sub_apply_smul]
  exact norm_rootLocalization_integrand_le gamma chi modes u centers tau i x
    (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) (B q)

theorem norm_periodic_rootLocalization_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) (x : T3) :
    let c := rootPatch gamma chi modes u centers tau i
    let w := fun x ↦ complexifyVector (fullVorticity u x)
    let B := PressureDyadicPeriodization.periodicKernel N hN t e
    ‖((c x : ℂ) * (c x : ℂ)) • kernelAction B w w x -
      kernelAction B (fun y ↦ (c y : ℂ) • w y) (fun y ↦ (c y : ℂ) • w y) x‖ ≤
      ∫ q : T6, ‖B q‖ * rootLocalizationDensity gamma chi modes u centers tau i
        x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) :=
  norm_rootLocalization_le _ (PressureDyadicPeriodization.integrable_periodicKernel N hN t e)
    gamma hg chi modes u hu centers hc tau i x

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootIntegrableKernelBudget
