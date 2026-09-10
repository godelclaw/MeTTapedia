import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RealFourierLocalizationEnergy
import Mettapedia.Analysis.FiniteMultiplierLocalization

/-!
# Factoring real pressure tilt through the Laplacian-pressure coefficient

Real symmetrization is performed on the scalar pressure trace before
localization. The tilt symbol is real and even, so it commutes exactly
with this symmetrization. The scalar trace energy is bounded by the
existing physical pressure-Hessian coefficient energy, with no dimension
factor and no coefficient-reality hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakePeriodicCoherentSplit
open FourierPressureCommutator FourierPressureTiltEnergy PressureTiltSymbol
open PancakeRealFourierProjection Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def complexifyVector (v : R3) : C3 := coefficientVec (fun i ↦ (v i : ℂ))

theorem norm_complexifyVector (v : R3) : ‖complexifyVector v‖ = ‖v‖ := by
  have h : ‖complexifyVector v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [complexifyVector, coefficientVec, PiLp.toLp_apply, Complex.norm_real]
  nlinarith only [h, norm_nonneg (complexifyVector v), norm_nonneg v]

theorem complexifyVector_sub (v w : R3) : complexifyVector (v - w) = complexifyVector v - complexifyVector w := by
  ext i
  simp [complexifyVector, coefficientVec]

theorem realFrequency_neg (q : Wavevector) : realFrequency (-q) = -realFrequency q := by
  ext i
  simp [realFrequency]

theorem realFrequency_add (p q : Wavevector) : realFrequency (p + q) = realFrequency p + realFrequency q := by
  ext i
  simp [realFrequency]

def complexTiltSymbol (e : R3) (q : Wavevector) : C3 := complexifyVector (tiltSymbol e (realFrequency q))

theorem complexTiltSymbol_neg (e : R3) (q : Wavevector) : complexTiltSymbol e (-q) = complexTiltSymbol e q := by
  simp only [complexTiltSymbol, realFrequency_neg, tiltSymbol_neg]

def traceAmplitude (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) : ℂ :=
  pressureAmplitude chi u q * (‖realFrequency q‖ ^ 2 : ℝ)

def realTraceAmplitude (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) : ℂ :=
  (traceAmplitude chi u q + conj (traceAmplitude chi u (-q))) / 2

theorem coefficientVec_tiltCoefficient_eq (chi : Wavevector → ℂ) (u : FourierVelocity) (e : R3) (q : Wavevector) :
    coefficientVec (tiltCoefficient chi u e q) = traceAmplitude chi u q • complexTiltSymbol e q := by
  have h := norm_sq_smul_tiltSymbol e (realFrequency q)
  ext i
  have hi := congrArg (fun v : R3 ↦ v i) h
  change ‖realFrequency q‖ ^ 2 * tiltSymbol e (realFrequency q) i =
    ⟪realFrequency q, e⟫ * PancakeAnisotropyDepletion.lineRemainder e (realFrequency q) i at hi
  simp only [coefficientVec, tiltCoefficient, traceAmplitude, complexTiltSymbol, complexifyVector,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_assoc, ← Complex.ofReal_mul, hi]

theorem realSymmetric_tiltCoefficient_eq (chi : Wavevector → ℂ) (u : FourierVelocity)
    (e : R3) (q : Wavevector) :
    coefficientVec (realSymmetricCoeff (tiltCoefficient chi u e) q) =
      realTraceAmplitude chi u q • complexTiltSymbol e q := by
  have hq := coefficientVec_tiltCoefficient_eq chi u e q
  have hn := coefficientVec_tiltCoefficient_eq chi u e (-q)
  rw [complexTiltSymbol_neg] at hn
  ext i
  have hqi := congrArg (fun v : C3 ↦ v i) hq
  have hni := congrArg (fun v : C3 ↦ v i) hn
  change tiltCoefficient chi u e q i = traceAmplitude chi u q * complexTiltSymbol e q i at hqi
  change tiltCoefficient chi u e (-q) i = traceAmplitude chi u (-q) * complexTiltSymbol e q i at hni
  simp only [coefficientVec, realSymmetricCoeff, PiLp.toLp_apply, hqi, hni,
    realTraceAmplitude, PiLp.smul_apply, smul_eq_mul, map_mul, complexTiltSymbol,
    complexifyVector, coefficientVec, PiLp.toLp_apply, Complex.conj_ofReal]
  ring

theorem scalarEnergy_traceAmplitude (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity) :
    scalarEnergy outputs (traceAmplitude chi u) = hessianEnergy chi outputs u := by
  unfold scalarEnergy hessianEnergy
  apply Finset.sum_congr rfl
  intro q _
  simp only [traceAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖realFrequency q‖), mul_pow]
  ring

theorem norm_realTraceAmplitude_sq_le (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) :
    ‖realTraceAmplitude chi u q‖ ^ 2 ≤
      (‖traceAmplitude chi u q‖ ^ 2 + ‖traceAmplitude chi u (-q)‖ ^ 2) / 2 := by
  have h := norm_add_le (traceAmplitude chi u q) (conj (traceAmplitude chi u (-q)))
  rw [Complex.norm_conj] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  unfold realTraceAmplitude
  rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  nlinarith only [hs, sq_nonneg (‖traceAmplitude chi u q‖ - ‖traceAmplitude chi u (-q)‖)]

theorem scalarEnergy_realTraceAmplitude_le (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    scalarEnergy outputs (realTraceAmplitude chi u) ≤ hessianEnergy chi outputs u := by
  have hn : (∑ q ∈ outputs, ‖traceAmplitude chi u (-q)‖ ^ 2) =
      ∑ q ∈ outputs, ‖traceAmplitude chi u q‖ ^ 2 := by
    apply Finset.sum_bij (fun q _ ↦ -q) (fun q hq ↦ (hs q).mpr hq)
      (fun a _ b _ hab ↦ by simpa using congrArg Neg.neg hab)
      (fun b hb ↦ ⟨-b, (hs b).mpr hb, by simp⟩)
    intro q _
    rfl
  have h := Finset.sum_le_sum (fun q (_ : q ∈ outputs) ↦ norm_realTraceAmplitude_sq_le chi u q)
  rw [← Finset.sum_div, Finset.sum_add_distrib, hn] at h
  rw [← scalarEnergy_traceAmplitude chi outputs u]
  unfold scalarEnergy
  linarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol
