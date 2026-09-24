import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputComplement
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputJointSource

/-!
# Complete high-input pressure and finite complement in the joint source

The infinite input tail is an actual continuous bilinear operator. Its
complement uses finite input and output sums, and the signed pointwise
identity keeps every other nonviscous source channel explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakeSpatialStrainEvolution PancakeAnisotropyDepletion PancakeSpectralFiniteDifference
open PancakeSobolevFiberEnvelope PancakeBlockReality PancakeCurlOutputTail
open PancakeInfiniteVelocityEnvelope PancakeHigherDerivativeMoments PancakeTransverseEnergyFreezing
open LocalAlignmentForcing LocalPressureCommutator LocalJointSourceTilt LocalSourceCommutator
open FourierPressureCommutator FourierPressureTilt FourierPressureTiltEnergy GaussianRootOperatorBudget
open PressureFixedOutputSymbol PressureFixedOutputReconstruction PressureFixedOutputJointSource
open PressureHighInputAction PressureHighInputComplement PressureTwoInputReconstruction
open Mettapedia.Analysis.UnitTorusFourierUniqueness

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem tailOperator_vorticity_eq_vectorPolynomial (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) :
    tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1) x =
      vectorPolynomial (outputModes N) (fun q ↦ UnitAddTorus.mFourierCoeff
        (tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1)) q) x := by
  have hz (q : Wavevector) (hq : q ∉ outputModes N) : UnitAddTorus.mFourierCoeff
      (tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1)) q = 0 := by
    rw [mFourierCoeff_tailOperator_vorticity N hN J e he u hu hu1 hr q,
      outputMultiplier_eq_zero_of_not_mem N hN q hq, Complex.ofReal_zero, zero_smul]
  have h := eq_polynomial
    (tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1))
    (outputModes N) hz
  simpa only [polynomial_apply, vectorPolynomial] using congrArg (fun f : C(T3, C3) ↦ f x) h

def lowInputField (N : ℝ) (J : ℕ) (e : R3) (u : FourierVelocity) (x : T3) : C3 :=
  vectorPolynomial (outputModes N) (fun q ↦ (outputMultiplier N q : ℂ) •
    lowInputCoefficient N J e u q) x

theorem tiltPolynomial_eq_tail_add_low (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    vectorPolynomial (outputModes N)
      (fun q ↦ coefficientVec (tiltCoefficient (fun q ↦ (outputMultiplier N q : ℂ)) u e q)) x =
      -tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
        lowInputField N J e u x := by
  rw [tailOperator_vorticity_eq_vectorPolynomial N hN J e he u hu hu1 hr x]
  simp only [lowInputField, vectorPolynomial]
  simp_rw [tiltCoefficient_eq_tail_add_low N hN J e he u hu hu1 hr hd, smul_sub, smul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem transverse_pressure_eq_tail_add_low (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    lineRemainder e (filteredPressureOperator (fun q ↦ (outputMultiplier N q : ℂ))
      (outputModes N) u x e) =
      complexRealPartEuclidean (WithLp.ofLp
        (-tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
          lowInputField N J e u x)) := by
  rw [transverse_pressure_eq_real_reconstruction]
  have h := congrArg (fun v : C3 ↦ complexRealPartEuclidean (WithLp.ofLp v))
    (tiltPolynomial_eq_tail_add_low N hN J e he u hu hu1 hr hd x)
  simpa only [vectorPolynomial_eq_coefficientReconstruction, coefficientVec, WithLp.ofLp_toLp] using h

theorem jointTilt_eq_high_input (N : ℝ) (hN : 0 < N) (J : ℕ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    let chi := fun q ↦ (outputMultiplier N q : ℂ)
    let modes := outputModes N
    let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
    let e := topVector (spatialStrain modes (filteredVelocity chi u) x)
    let W := spatialSpin modes (filteredVelocity chi u) x
    jointTilt chi modes modes u x =
      lineRemainder e (-(W (W e)) + rawSubgridOperator chi modes u x e +
        transportOperator chi modes modes u x e) -
      complexRealPartEuclidean (WithLp.ofLp
        (-tailOperator N hN J e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
          lowInputField N J e u x)) := by
  have hconv (q : Wavevector) (i : Fin 3) : Summable (fun k ↦ outputFiber q u k i) :=
    ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).prod_factor q).of_norm_bounded
      (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
        (fourierMoment_nonneg _ _) (fun _ ↦ le_rfl) q k i)
  have hs (q : Wavevector) (hq : q ∉ outputModes N) : (outputMultiplier N q : ℂ) = 0 := by
    rw [outputMultiplier_eq_zero_of_not_mem N hN q hq, Complex.ofReal_zero]
  dsimp only
  rw [jointTilt_eq_pressure_kernel _ u 1 (norm_outputMultiplier_complex_le N)
    (outputModes N) (outputModes N) hs hd hconv x,
    ← transverse_filteredPressure_eq_sum,
    transverse_pressure_eq_tail_add_low N hN J _ (topVector_norm _) u hu
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) hr hd x]

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputJointSource
