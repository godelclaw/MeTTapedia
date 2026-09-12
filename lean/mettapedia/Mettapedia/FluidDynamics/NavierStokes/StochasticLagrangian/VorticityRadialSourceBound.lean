import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityWeightedStretching

/-!
# Cubic radial increments bound the signed eighth-moment source

The estimate is applied to the actual kernel and full vorticity, after
exchanging source and receiver. The remaining cost keeps the smaller
endpoint vorticity magnitude inside the spatial integral. No bound on
this coefficient, no uniform absolute kernel bound, and no time budget
is supplied by this result.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSourceBound

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeBlockReality PancakePeriodicComplexStretch LocalLowDiffusionBudget
open VorticityStretchingKernel VorticityWeightedStretching
open Mettapedia.Analysis.SignedCrossKernel

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def radialPairCost (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∫ y : T3, radialCost n (kernel modes (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem radialPairCost_nonneg (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity) :
    0 ≤ radialPairCost n modes u :=
  integral_nonneg (fun _ ↦ integral_nonneg (fun _ ↦ by unfold radialCost; positivity))

theorem abs_finiteStretching_double_le (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    |finiteStretching (2 * n) modes u| ≤ 2 * radialPairCost n modes u := by
  have h := abs_integral_weightedStretch_double_le (volume : Measure T3)
    (fun x y ↦ kernel modes (x - y)) (fullVorticity u)
    ((continuous_kernel modes).comp (continuous_fst.sub continuous_snd))
    (continuous_fullVorticity u hu) n (kernel_sub_swap modes)
  simpa only [weightedStretch, integral_const_mul, integral_kernel_stretch modes u hu hr hd,
    finiteStretching, radialPairCost] using h

/-- The exact radial weight used by the actual eighth-moment dissipation. -/
theorem abs_eighthMoment_finiteStretching_le (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    |finiteStretching 6 modes u| ≤ 2 * radialPairCost 3 modes u :=
  abs_finiteStretching_double_le 3 modes u hu hr hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityRadialSourceBound
