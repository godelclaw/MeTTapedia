import Mettapedia.Analysis.PeriodicRieszPolynomial
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRegularizedPayment

/-!
# Exact source and dissipation payment for the annular polynomial

The finite Fourier representative has the same paired source and signed
high-amplitude remainder as the periodized kernel. Consequently the existing
viscosity-dependent threshold applies unchanged at every cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource

open MeasureTheory Filter PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeCurlOutputTail PancakeHigherDerivativeMoments LocalLowDiffusionBudget
open PancakeBlockReality
open VorticityRegularizedIncrement
open Mettapedia.Analysis SignedCrossKernel
open scoped Topology
local notation "T3" => UnitAddTorus (Fin 3)
local notation "H" => PeriodicRieszPolynomial.kernel (d := 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pairedSource (n N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    pairedStretch n (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

def highAmplitudeSource (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * ∫ x : T3, ∫ y : T3,
    highAmplitudeStretch n L (H N (x - y)) (fullVorticity u x) (fullVorticity u y)

theorem pairedSource_eq (n N : ℕ) (u : FourierVelocity) :
    pairedSource n N u = VorticityRegularizedPairing.pairedSource n N u := by
  unfold pairedSource VorticityRegularizedPairing.pairedSource
  exact congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    (PeriodicRieszPolynomial.integral_pair_eq (d := 3) N
      (fun x y hKernel ↦ pairedStretch n hKernel (fullVorticity u x) (fullVorticity u y)))

theorem highAmplitudeSource_eq (n : ℕ) (L : ℝ) (N : ℕ) (u : FourierVelocity) :
    highAmplitudeSource n L N u = VorticityRegularizedPayment.highAmplitudeSource n L N u := by
  unfold highAmplitudeSource VorticityRegularizedPayment.highAmplitudeSource
  exact congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    (PeriodicRieszPolynomial.integral_pair_eq (d := 3) N
      (fun x y hKernel ↦ highAmplitudeStretch n L hKernel (fullVorticity u x) (fullVorticity u y)))

theorem source_eq_pairedSource (n N : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    VorticityRegularizedSource.source n N u = pairedSource n N u := by
  rw [pairedSource_eq]
  exact VorticityRegularizedPairing.source_eq_pairedSource n N u hu

theorem pairedSource_le_half_dissipation_add_remainder (nu : ℝ) (hnu : 0 < nu) (N : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) :
    pairedSource 6 N u ≤ (nu / 2) * LocalVorticityEighthMoment.weightedPalinstrophy u +
      highAmplitudeSource 6 (dissipationThreshold nu) N u := by
  rw [← source_eq_pairedSource 6 N u
    (summable_fourierMoment_of_le u (by norm_num : 1 ≤ 3) hu), highAmplitudeSource_eq]
  exact VorticityRegularizedPayment.source_le_half_dissipation_add_remainder nu hnu N u hu

theorem tendsto_pairedSource (n : ℕ) (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    Tendsto (fun N : ℕ ↦ pairedSource n N u) atTop
      (𝓝 (VorticityWeightedStretching.fullStretching n u)) := by
  simpa only [pairedSource_eq] using
    VorticityRegularizedPairing.tendsto_pairedSource n u hu hr hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityAnnularPolynomialSource
