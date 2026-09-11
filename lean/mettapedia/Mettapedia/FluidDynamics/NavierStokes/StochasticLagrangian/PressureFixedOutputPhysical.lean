import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicPhysicalIdentification

/-!
# Fixed-output kernels in the actual pressure coefficient

The low-pass filter is already part of the kernel action. The exact signed
identity retains the complementary input sector and holds at every output
frequency, not only on an inner output ball.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputPhysical

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open FourierPressureCommutator PancakeBlockReality FourierPressureTraceSymbol
open PancakeFrequencyProjectorCommutator PancakeInfiniteSpatialCurl
open PancakeGalerkinKineticEnergy
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open PressureFixedOutputSymbol PressureFixedOutputAction PressureDyadicPhysicalIdentification
open GaussianRootOperatorBudget ComplexPressurePair FourierPressureTiltEnergy
open Mettapedia.Analysis.DyadicAnnulus

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_operator_vorticity (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (operator N hN j e
      (complexVorticityField u hu1) (complexVorticityField u hu1)) q =
      (outputMultiplier N q : ℂ) • ∑' k,
        (normalizedCutoff ((inputScale N j)⁻¹ • realFrequency k) : ℂ) •
          tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  rw [complexVorticityField_eq_fullFourierField u hu hu1 hr]
  rw [mFourierCoeff_operator N hN j e he _ _
    (PhysicalPressurePair.summable_norm_fourierCurl u hu)
    (PhysicalPressurePair.summable_norm_fourierCurl u hu) q]
  exact tsum_const_smul'' _

theorem tiltCoefficient_eq_operator_add_complement (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (q : Wavevector) :
    coefficientVec (tiltCoefficient (fun q ↦ (outputMultiplier N q : ℂ)) u e q) =
      -UnitAddTorus.mFourierCoeff (operator N hN j e
        (complexVorticityField u hu1) (complexVorticityField u hu1)) q -
          (outputMultiplier N q : ℂ) • complementaryTiltCoefficient (inputScale N j) e u q := by
  rw [PhysicalPressurePair.tiltCoefficient_eq_tsum_pairs _ u hd hu e q,
    mFourierCoeff_operator_vorticity N hN j e he u hu hu1 hr q,
    ← annular_add_complementaryTiltCoefficient (inputScale N j) e he u hu q]
  simp only [neg_smul, smul_add, sub_eq_add_neg]

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputPhysical
