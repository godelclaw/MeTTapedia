import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakDivergence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelWeakFourier

/-! Actual weak derivatives, a nonzero localized divergence, and channel normalization checks. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureWeakDivergenceAudit

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakeHaarTransportRate
open PancakePeriodicVorticityEquation PeriodicFourierWeakDerivative
open PeriodicVectorWeakDerivative PressureCoherentChannelWeakFourier
open PressureCoherentChannelPeriodization PancakeBilinearPeriodization
open GaussianRootVorticity GaussianRootPartition PancakeHigherDerivativeMoments
open FourierPressureTraceSymbol (complexifyVector)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (v : R3) (j : Fin 3) (x : T3) : coordinateRate (fun _ ↦ v) j x = 0 := by
  ext i
  simp [coordinateRate, shiftRate]

example (v : R3) (x : T3) : divergence (fun _ ↦ v) x = 0 := by
  simp [divergence, coordinateRate, shiftRate]

-- A nonconstant scalar multiple of a constant divergence-free vector
-- need not have zero divergence. This is not a singularity example.
def localizedConstant (x : T3) : R3 :=
  WithLp.toLp 2 ![(UnitAddTorus.mFourier (Pi.single 0 1) x).im, 0, 0]

theorem divergence_localizedConstant_at_zero : divergence localizedConstant 0 = 2 * Real.pi := by
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_character_shift (Pi.single 0 1) 0 (0 : T3))).deriv
  simpa [divergence, coordinateRate, localizedConstant, shiftRate, Fin.sum_univ_succ,
    unitTorusDerivativePhase, UnitAddTorus.mFourier, Function.comp_def] using hd

example : divergence localizedConstant 0 ≠ 0 := by
  rw [divergence_localizedConstant_at_zero]
  exact ne_of_gt (mul_pos (by norm_num) Real.pi_pos)

example (t : ℝ) (e : R3) :
    UnitAddTorus.mFourierCoeff (periodicKernel 8 (by norm_num) t e (.first 0))
      (pairWavevector (Pi.single 0 16) 0) =
        (2 : ℂ) • UnitAddTorus.mFourierCoeff (periodicKernel 8 (by norm_num) t e .undifferentiated)
          (pairWavevector (Pi.single 0 16) 0) := by
  have h := mFourierCoeff_first_factor 8 (by norm_num) t e 0 (Pi.single 0 16) 0
  norm_num at h
  exact h

example (t : ℝ) (e : R3) :
    UnitAddTorus.mFourierCoeff (periodicKernel 8 (by norm_num) t e (.second 2))
      (pairWavevector 0 (Pi.single 2 (-24))) =
        (-3 : ℂ) • UnitAddTorus.mFourierCoeff (periodicKernel 8 (by norm_num) t e .undifferentiated)
          (pairWavevector 0 (Pi.single 2 (-24))) := by
  have h := mFourierCoeff_second_factor 8 (by norm_num) t e 2 0 (Pi.single 2 (-24))
  norm_num at h
  exact h

example (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) :
    (∫ x : T3, GaussianRootWeakDivergence.divergence gamma chi modes u centers tau i x) = 0 :=
  integral_divergence_zero _
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i)

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) (i : ↑centers) (k p : Wavevector) (v : C3) :
    (unitTorusDerivativePhase * (N : ℂ)) •
      (UnitAddTorus.mFourierCoeff (periodicKernel N hN t e (.first j)) (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector
          (rootVorticity gamma chi modes u centers tau i x)) k) v) =
      UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector
          (GaussianRootWeakDivergence.coordinateDerivative gamma chi modes u centers tau i j x)) k) v :=
  first_channel_weakDerivative N hN t e j _
    (continuous_rootVorticity gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i)
    (locallyLipschitz_rootVorticity gamma hg chi modes u hu centers hc tau i) k p v

end Mettapedia.FluidDynamics.NavierStokes.PressureWeakDivergenceAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.ae_hasDerivAt_coordinateRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.memLp_coordinateRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.mFourierCoeff_complexify_coordinateRate
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.memLp_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.integral_divergence_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.mFourierCoeff_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative.divergence_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.ae_hasDerivAt_coordinateDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.memLp_coordinateDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.memLp_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.mFourierCoeff_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.ae_weighted_coordinate_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.ae_weighted_divergence_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.integrable_weighted_divergence_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakDivergence.integral_weighted_divergence_le_coordinate_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelWeakFourier.first_channel_weakDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelWeakFourier.second_channel_weakDerivative
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureWeakDivergenceAudit.divergence_localizedConstant_at_zero
