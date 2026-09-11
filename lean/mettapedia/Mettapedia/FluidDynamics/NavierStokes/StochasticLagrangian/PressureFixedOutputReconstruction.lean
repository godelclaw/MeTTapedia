import Mettapedia.Analysis.UnitTorusFourierUniqueness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputPhysical
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeArbitraryDataBlocks

/-!
# Exact pointwise reconstruction of fixed-output pressure

The low-pass output support lies in a concrete finite lattice box, while
the input data may have infinitely many nonzero coefficients. Fourier
uniqueness reconstructs the actual continuous kernel action on that box.
The resulting spatial pressure identity has no output filter outside the
kernel action; the complementary input sector remains explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureFixedOutputAction PressureFixedOutputPhysical
open PressureDyadicPhysicalIdentification PressureTwoInputReconstruction PancakeArbitraryDataBlocks
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative PancakeBlockReality
open GaussianRootOperatorBudget FourierPressureTiltEnergy LocalPressureCommutator
open PancakeAnisotropyDepletion PancakeTransverseEnergyFreezing
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

def outputModes (N : ℝ) : Finset Wavevector := wavevectorBox ⌈N / 64⌉₊

theorem mem_outputModes_of_norm_le (N : ℝ) (q : Wavevector) (hq : ‖realFrequency q‖ ≤ N / 64) :
    q ∈ outputModes N := by
  rw [outputModes, mem_wavevectorBox_iff]
  intro i
  have hi := (PiLp.norm_apply_le (realFrequency q) i).trans (hq.trans (Nat.le_ceil (N / 64)))
  change ‖(q i : ℝ)‖ ≤ (⌈N / 64⌉₊ : ℝ) at hi
  rw [Real.norm_eq_abs] at hi
  exact_mod_cast hi

theorem outputMultiplier_eq_zero_of_not_mem (N : ℝ) (hN : 0 < N)
    (q : Wavevector) (hq : q ∉ outputModes N) : outputMultiplier N q = 0 := by
  apply outputMultiplier_eq_zero N hN
  by_contra hn
  exact hq (mem_outputModes_of_norm_le N q (le_of_lt (lt_of_not_ge hn)))

theorem mFourierCoeff_operator_eq_zero_of_not_mem (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (a b : Wavevector → C3)
    (ha : Summable (fun k ↦ ‖a k‖)) (hb : Summable (fun k ↦ ‖b k‖))
    (q : Wavevector) (hq : q ∉ outputModes N) :
    UnitAddTorus.mFourierCoeff (operator N hN j e (fullFourierField id a) (fullFourierField id b)) q = 0 := by
  rw [mFourierCoeff_operator N hN j e he a b ha hb q,
    outputMultiplier_eq_zero_of_not_mem N hN q hq]
  simp

theorem operator_eq_vectorPolynomial (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (a b : Wavevector → C3)
    (ha : Summable (fun k ↦ ‖a k‖)) (hb : Summable (fun k ↦ ‖b k‖)) (x : T3) :
    operator N hN j e (fullFourierField id a) (fullFourierField id b) x =
      vectorPolynomial (outputModes N) (fun q ↦ UnitAddTorus.mFourierCoeff
        (operator N hN j e (fullFourierField id a) (fullFourierField id b)) q) x := by
  have h := eq_polynomial (operator N hN j e (fullFourierField id a) (fullFourierField id b))
    (outputModes N) (mFourierCoeff_operator_eq_zero_of_not_mem N hN j e he a b ha hb)
  simpa only [polynomial_apply, vectorPolynomial] using congrArg (fun f : C(T3, C3) ↦ f x) h

theorem operator_vorticity_eq_vectorPolynomial (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (x : T3) :
    operator N hN j e (complexVorticityField u hu1) (complexVorticityField u hu1) x =
      vectorPolynomial (outputModes N) (fun q ↦ UnitAddTorus.mFourierCoeff
        (operator N hN j e (complexVorticityField u hu1) (complexVorticityField u hu1)) q) x := by
  rw [complexVorticityField_eq_fullFourierField u hu hu1 hr]
  exact operator_eq_vectorPolynomial N hN j e he _ _
    (PhysicalPressurePair.summable_norm_fourierCurl u hu)
    (PhysicalPressurePair.summable_norm_fourierCurl u hu) x

def complementField (N : ℝ) (j : ℕ) (e : R3) (u : FourierVelocity) (x : T3) : C3 :=
  vectorPolynomial (outputModes N) (fun q ↦ (outputMultiplier N q : ℂ) •
    complementaryTiltCoefficient (inputScale N j) e u q) x

theorem tiltPolynomial_eq (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    vectorPolynomial (outputModes N)
      (fun q ↦ coefficientVec (tiltCoefficient (fun q ↦ (outputMultiplier N q : ℂ)) u e q)) x =
      -operator N hN j e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
        complementField N j e u x := by
  rw [operator_vorticity_eq_vectorPolynomial N hN j e he u hu hu1 hr x]
  simp only [complementField, vectorPolynomial]
  simp_rw [tiltCoefficient_eq_operator_add_complement N hN j e he u hu hu1 hr hd,
    smul_sub, smul_neg]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem transverse_pressure_eq (N : ℝ) (hN : 0 < N) (j : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (x : T3) :
    lineRemainder e (filteredPressureOperator (fun q ↦ (outputMultiplier N q : ℂ))
      (outputModes N) u x e) =
      complexRealPartEuclidean (WithLp.ofLp
        (-operator N hN j e (complexVorticityField u hu1) (complexVorticityField u hu1) x -
          complementField N j e u x)) := by
  rw [transverse_pressure_eq_real_reconstruction]
  have h := congrArg (fun v : C3 ↦ complexRealPartEuclidean (WithLp.ofLp v))
    (tiltPolynomial_eq N hN j e he u hu hu1 hr hd x)
  simpa only [vectorPolynomial_eq_coefficientReconstruction, coefficientVec, WithLp.ofLp_toLp] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureFixedOutputReconstruction
