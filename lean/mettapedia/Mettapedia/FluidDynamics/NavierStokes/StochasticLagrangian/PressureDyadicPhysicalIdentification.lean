import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicFourierReconstruction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PhysicalPressurePair
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootOperatorBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputReconstruction

/-!
# The dyadic pressure sector in the actual pressure-tilt coefficient

The kernel acts on the actual complexified real vorticity. On low output
frequencies its coefficient is the normalized input-annulus part of the
physical pressure convolution. The complementary input weight is displayed
explicitly in an exact signed decomposition; it is not claimed to vanish or
to satisfy a time-integrated estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeGalerkinKineticEnergy FourierPressureCommutator
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve PancakeInfiniteSpatialCurl
open PancakeBlockReality FourierPressureTraceSymbol LocalLowDiffusionBudget
open PressureBilinearOperator PressureDyadicFourierReconstruction GaussianRootOperatorBudget
open FullVorticityFourierCoefficients ComplexPressurePair ComplexPressureMisalignment
open PressureTwoInputReconstruction PancakeAnisotropyDepletion PancakeTransverseEnergyFreezing
open LocalPressureCommutator FourierPressureTiltEnergy
open Mettapedia.Analysis.DyadicAnnulus

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem complexVorticityField_eq_fullFourierField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) :
    complexVorticityField u hu1 = fullFourierField id (fun k ↦ coefficientVec (fourierCurl u k)) := by
  apply ContinuousMap.ext
  intro x
  change complexifyVector (fullVorticity u x) = _
  rw [complexify_fullVorticity u hu1 hr]
  have ha := FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu1
  have hb := PhysicalPressurePair.summable_norm_fourierCurl u hu
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm.toContinuousLinearMap
  have hs := (ContinuousMap.evalCLM ℂ x).summable (summable_modeField id (fourierCurl u) ha)
  change Summable (fun k : Wavevector ↦ UnitAddTorus.mFourier k x • fourierCurl u k) at hs
  rw [fullFourierField_apply id (fourierCurl u) ha, fullFourierField_apply id _ hb]
  change L (∑' k, UnitAddTorus.mFourier k x • fourierCurl u k) = _
  rw [L.map_tsum hs]
  apply tsum_congr
  intro k
  exact L.map_smul _ _

theorem mFourierCoeff_sumAction_vorticity_low (N : ℝ) (hN : 0 < N)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (q : Wavevector) (hq : ‖realFrequency q‖ ≤ N / 256) :
    UnitAddTorus.mFourierCoeff (PressureDyadicAction.sumAction N hN e
      (complexVorticityField u hu1) (complexVorticityField u hu1)) q =
      ∑' k, (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
        tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  rw [complexVorticityField_eq_fullFourierField u hu hu1 hr]
  exact mFourierCoeff_sumAction_low N hN e he _ _
    (PhysicalPressurePair.summable_norm_fourierCurl u hu)
    (PhysicalPressurePair.summable_norm_fourierCurl u hu) q hq

def complementaryTiltCoefficient (N : ℝ) (e : R3) (u : FourierVelocity) (q : Wavevector) : C3 :=
  ∑' k, (1 - (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ)) •
    tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))

theorem summable_norm_curlTiltPair (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    Summable (fun k ↦ ‖tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))‖) := by
  have hw := PhysicalPressurePair.summable_norm_fourierCurl u hu
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _
    (hw.mul_right (∑' p, ‖coefficientVec (fourierCurl u p)‖))
  intro k
  exact (norm_tiltPair_le e he k (q - k) _ _).trans
    (mul_le_mul_of_nonneg_left (hw.le_tsum (q - k) (fun _ _ ↦ norm_nonneg _)) (norm_nonneg _))

theorem annular_add_complementaryTiltCoefficient (N : ℝ) (e : R3) (he : ‖e‖ = 1)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    (∑' k, (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
      tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))) +
        complementaryTiltCoefficient N e u q =
      ∑' k, tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  have hs := summable_norm_curlTiltPair e he u hu q
  have hw (k : Wavevector) : ‖(normalizedCutoff (N⁻¹ • realFrequency k) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (normalizedCutoff_nonneg _)]
    exact normalizedCutoff_le_one _
  have hc (k : Wavevector) : ‖1 - (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (normalizedCutoff_le_one _))]
    exact sub_le_self _ (normalizedCutoff_nonneg _)
  have ha : Summable (fun k ↦ (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ) •
      tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))) :=
    hs.of_norm_bounded (fun k ↦ (norm_smul_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)).trans_eq (one_mul _)))
  have hb : Summable (fun k ↦ (1 - (normalizedCutoff (N⁻¹ • realFrequency k) : ℂ)) •
      tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))) :=
    hs.of_norm_bounded (fun k ↦ (norm_smul_le _ _).trans
      ((mul_le_mul_of_nonneg_right (hc k) (norm_nonneg _)).trans_eq (one_mul _)))
  rw [complementaryTiltCoefficient, ← ha.tsum_add hb]
  apply tsum_congr
  intro k
  rw [← add_smul]
  simp

/-- Exact physical sign and explicit complementary input sector. -/
theorem tiltCoefficient_eq_sumAction_add_complement (N : ℝ) (hN : 0 < N)
    (chi : Wavevector → ℂ) (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (q : Wavevector) (hq : ‖realFrequency q‖ ≤ N / 256) :
    coefficientVec (FourierPressureTiltEnergy.tiltCoefficient chi u e q) =
      (-chi q) • (UnitAddTorus.mFourierCoeff (PressureDyadicAction.sumAction N hN e
        (complexVorticityField u hu1) (complexVorticityField u hu1)) q +
          complementaryTiltCoefficient N e u q) := by
  rw [PhysicalPressurePair.tiltCoefficient_eq_tsum_pairs chi u hd hu e q,
    mFourierCoeff_sumAction_vorticity_low N hN e he u hu hu1 hr q hq,
    annular_add_complementaryTiltCoefficient N e he u hu q]

/-- Reconstruction into the actual spatial pressure channel. The output
filter is retained, and every reconstructed output must be in the low ball. -/
theorem transverse_pressure_eq_dyadic_decomposition (N : ℝ) (hN : 0 < N)
    (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (e : R3) (he : ‖e‖ = 1)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (houtputs : ∀ q ∈ outputs, ‖realFrequency q‖ ≤ N / 256) (x : T3) :
    lineRemainder e (filteredPressureOperator chi outputs u x e) =
      complexRealPartEuclidean (WithLp.ofLp (vectorPolynomial outputs
        (fun q ↦ (-chi q) • (UnitAddTorus.mFourierCoeff (PressureDyadicAction.sumAction N hN e
          (complexVorticityField u hu1) (complexVorticityField u hu1)) q +
            complementaryTiltCoefficient N e u q)) x)) := by
  have hv : vectorPolynomial outputs (fun q ↦ coefficientVec (tiltCoefficient chi u e q)) x =
      vectorPolynomial outputs
        (fun q ↦ (-chi q) • (UnitAddTorus.mFourierCoeff (PressureDyadicAction.sumAction N hN e
          (complexVorticityField u hu1) (complexVorticityField u hu1)) q +
            complementaryTiltCoefficient N e u q)) x := by
    apply Finset.sum_congr rfl
    intro q hq
    exact congrArg (fun v : C3 ↦ UnitAddTorus.mFourier q x • v)
      (tiltCoefficient_eq_sumAction_add_complement N hN chi e he u hu hu1 hr hd q (houtputs q hq))
  rw [transverse_pressure_eq_real_reconstruction]
  have h := congrArg (fun v : C3 ↦ complexRealPartEuclidean (WithLp.ofLp v)) hv
  simpa only [vectorPolynomial_eq_coefficientReconstruction, coefficientVec,
    WithLp.ofLp_toLp] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicPhysicalIdentification
