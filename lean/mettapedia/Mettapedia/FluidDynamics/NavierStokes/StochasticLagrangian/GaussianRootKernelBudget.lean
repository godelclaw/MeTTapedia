import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootEnergy

/-!
# Actual Gaussian root localization inside the pressure kernel

The root-cutoff differences retain their full vorticity factors before
integration. The bound has no inverse vorticity magnitude and no
unweighted scalar-root gradient. Its kernel moment is not claimed to be
uniform as the retained frequencies exhaust the lattice.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootKernelBudget

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open FourierPressureTraceSymbol LocalLowDiffusionBudget FinitePressureKernel PressureKernelAction
open GaussianRootVorticity GaussianRootPartition GaussianRootDifference GaussianRootDifferentiation
open Mettapedia.Analysis.BilinearKernelLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def rootDifferenceCost (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y : T3) : ℝ :=
  |rootFieldFactor gamma chi modes u centers tau i x - rootFieldFactor gamma chi modes u centers tau i y| *
    Real.sqrt ‖fullVorticity u y‖ * ‖fullVorticity u y‖ +
  |rootFieldFactor gamma chi modes u centers tau i x| * Real.sqrt ‖fullVorticity u y‖ *
    ‖fullVorticity u x - fullVorticity u y‖

def rootLocalizationDensity (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y z : T3) : ℝ :=
  |rootPatch gamma chi modes u centers tau i x| * rootDifferenceCost gamma chi modes u centers tau i x y *
    ‖fullVorticity u z‖ +
  |rootPatch gamma chi modes u centers tau i y| * ‖fullVorticity u y‖ *
    rootDifferenceCost gamma chi modes u centers tau i x z

theorem norm_rootLocalization_integrand_le
    (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (i : ↑centers) (x y z : T3)
    (B : C3 →L[ℂ] C3 →L[ℂ] C3) :
    let c := rootPatch gamma chi modes u centers tau i
    let w := fun x ↦ complexifyVector (fullVorticity u x)
    ‖((c x : ℂ) * (c x : ℂ)) • B (w y) (w z) - B ((c y : ℂ) • w y) ((c z : ℂ) • w z)‖ ≤
      ‖B‖ * rootLocalizationDensity gamma chi modes u centers tau i x y z := by
  dsimp only
  have h := norm_smul_sub_apply_smul_le B
    (rootPatch gamma chi modes u centers tau i x : ℂ) (rootPatch gamma chi modes u centers tau i x : ℂ)
    (rootPatch gamma chi modes u centers tau i y : ℂ) (rootPatch gamma chi modes u centers tau i z : ℂ)
    (complexifyVector (fullVorticity u y)) (complexifyVector (fullVorticity u z))
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, norm_complexifyVector] at h
  have hy := abs_rootPatch_sub_mul_vorticity_norm_le gamma chi modes u centers tau i x y
  have hz := abs_rootPatch_sub_mul_vorticity_norm_le gamma chi modes u centers tau i x z
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hy (abs_nonneg _)) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (norm_nonneg _)))) (norm_nonneg B))

theorem norm_pressureKernel_rootLocalization_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (i : ↑centers) (e : R3) (he : ‖e‖ = 1) (S T : Finset Wavevector) (x : T3) :
    let c := rootPatch gamma chi modes u centers tau i
    let w := fun x ↦ complexifyVector (fullVorticity u x)
    let B := pressureKernel e he S T
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
  have hB := continuous_pressureKernel e he S T
  have hdom : Integrable (fun q : T6 ↦ ‖pressureKernel e he S T q‖ *
      rootLocalizationDensity gamma chi modes u centers tau i
        x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)) := by
    have hcont : Continuous (fun q : T6 ↦ ‖pressureKernel e he S T q‖ *
        rootLocalizationDensity gamma chi modes u centers tau i
          x (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)) := by
      unfold rootLocalizationDensity rootDifferenceCost
      fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [kernelAction_localization _ _ _ _ _ x hB hwc hwc hcc hcc]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hdom
  filter_upwards [] with q
  rw [← smul_sub_apply_smul]
  exact norm_rootLocalization_integrand_le gamma chi modes u centers tau i x
    (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) (pressureKernel e he S T q)

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootKernelBudget
