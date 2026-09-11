import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentChannelPeriodization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicVectorWeakDerivative

/-!
# Exact weak-derivative normalization for coherent pressure channels

An input-coordinate channel equals the undifferentiated channel applied
to the corresponding weak derivative, after multiplication by `2 pi i N`.
The identities use actual Fourier coefficients of locally Lipschitz vector
fields. They are coefficient identities, not an unproved interchange of
a nonsmooth input derivative with a physical-space kernel integral.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelWeakFourier

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator PancakeBilinearPeriodization
open PressureCoherentChannelPeriodization
open PressureCoherentDivergenceChannelKernel (scaledMultiplier_first scaledMultiplier_second)
open PressureLowOutputSymbol (pairEquiv)
open PeriodicVectorWeakDerivative (coordinateRate mFourierCoeff_complexify_coordinateRate)
open PancakeFourierMaterialPaths (torusPoint)
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)
open FourierPressureTraceSymbol (complexifyVector)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

theorem pairEquiv_frequency_pairWavevector (k p : Wavevector) :
    pairEquiv (euclideanFrequencyPairOfWavevector (pairWavevector k p)) =
      (realFrequency k, realFrequency p) := by
  apply pairEquiv.symm.injective
  simp only [pairEquiv.symm_apply_apply]
  ext j
  fin_cases j <;> rfl

theorem mFourierCoeff_first_factor (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (k p : Wavevector) :
    UnitAddTorus.mFourierCoeff (periodicKernel N hN t e (.first j)) (pairWavevector k p) =
      (((N⁻¹ : ℝ) : ℂ) * (k j : ℂ)) •
        UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) (pairWavevector k p) := by
  rw [mFourierCoeff_periodicKernel_factor, pairEquiv_frequency_pairWavevector, scaledMultiplier_first]
  simp [realFrequency]

theorem mFourierCoeff_second_factor (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (k p : Wavevector) :
    UnitAddTorus.mFourierCoeff (periodicKernel N hN t e (.second j)) (pairWavevector k p) =
      (((N⁻¹ : ℝ) : ℂ) * (p j : ℂ)) •
        UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) (pairWavevector k p) := by
  rw [mFourierCoeff_periodicKernel_factor, pairEquiv_frequency_pairWavevector, scaledMultiplier_second]
  simp [realFrequency]

theorem first_channel_weakDerivative (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (f : T3 → R3) (hf : Continuous f) (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r)))
    (k p : Wavevector) (v : C3) :
    (unitTorusDerivativePhase * (N : ℂ)) •
      (UnitAddTorus.mFourierCoeff (periodicKernel N hN t e (.first j)) (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (f x)) k) v) =
      UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) (pairWavevector k p)
        (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (coordinateRate f j x)) k) v := by
  rw [mFourierCoeff_first_factor, mFourierCoeff_complexify_coordinateRate f j hf hfL]
  simp only [smul_apply, map_smul, smul_smul]
  congr 1
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  push_cast
  field_simp

theorem second_channel_weakDerivative (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (j : Fin 3)
    (g : T3 → R3) (hg : Continuous g) (hgL : LocallyLipschitz (fun r : X3 ↦ g (torusPoint r)))
    (k p : Wavevector) (v : C3) :
    (unitTorusDerivativePhase * (N : ℂ)) •
      (UnitAddTorus.mFourierCoeff (periodicKernel N hN t e (.second j)) (pairWavevector k p)
        v (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (g x)) p)) =
      UnitAddTorus.mFourierCoeff (periodicKernel N hN t e .undifferentiated) (pairWavevector k p)
        v (UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (coordinateRate g j x)) p) := by
  rw [mFourierCoeff_second_factor, mFourierCoeff_complexify_coordinateRate g j hg hgL]
  simp only [smul_apply, map_smul, smul_smul]
  congr 1
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  push_cast
  field_simp

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentChannelWeakFourier
