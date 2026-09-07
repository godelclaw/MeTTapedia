import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSummableOutputTail
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightVariationCutoff

/-!
# A uniform spatial tail bound for actual finite pair reconstructions

The Fourier coefficients are collected from their input pairs. Their real
exterior reconstruction is bounded by a summable output tail independently
of the finite input set and output enumeration. This is consistency for a
fixed summable majorant, not a nonlinear a priori estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeExteriorReconstructionTail

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeTransverseEnergyFreezing PancakeFrequencyProjectorCommutator
open PancakeWeightVariationCutoff PancakeLowDiffusionBudget PancakeSummableOutputTail

local notation "T3" => UnitAddTorus (Fin 3)

def pairOutputCoeff (pairs : Finset (Wavevector × Wavevector))
    (F : Wavevector × Wavevector → VelocityCoefficient) (q : Wavevector) : VelocityCoefficient :=
  ∑ p ∈ pairs, if p.1 + p.2 = q then F p else 0

theorem norm_realPart_le_coefficientVec (v : VelocityCoefficient) :
    ‖complexRealPartEuclidean v‖ ≤ ‖coefficientVec v‖ := by
  nlinarith [norm_realPart_sq_le v, norm_nonneg (complexRealPartEuclidean v), norm_nonneg (coefficientVec v)]

theorem norm_real_reconstruction_le_sum (outputs : Finset Wavevector) (a : FourierVelocity) (x : T3) :
    ‖complexRealPartEuclidean (finiteFourierReconstruction outputs a x)‖ ≤
      ∑ q ∈ outputs, ‖coefficientVec (a q)‖ :=
  (norm_realPart_le_coefficientVec _).trans (norm_coefficientReconstruction_le_sum outputs a x)

theorem norm_pairOutputCoeff_le (pairs : Finset (Wavevector × Wavevector))
    (F : Wavevector × Wavevector → VelocityCoefficient) (H : Wavevector × Wavevector → ℝ)
    (hF : ∀ p ∈ pairs, ‖coefficientVec (F p)‖ ≤ H p) (q : Wavevector) :
    ‖coefficientVec (pairOutputCoeff pairs F q)‖ ≤ ∑ p ∈ pairs, if p.1 + p.2 = q then H p else 0 := by
  simp only [pairOutputCoeff, coefficientVec, WithLp.toLp_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  split_ifs with h
  · exact hF p hp
  · simp

theorem sum_collected_majorant (pairs : Finset (Wavevector × Wavevector))
    (outputs : Finset Wavevector) (H : Wavevector × Wavevector → ℝ) :
    (∑ q ∈ outputs, ∑ p ∈ pairs, if p.1 + p.2 = q then H p else 0) =
      ∑ p ∈ pairs, if p.1 + p.2 ∈ outputs then H p else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp [eq_comm]

theorem norm_exterior_reconstruction_le_outputTail
    (M outputs : Finset Wavevector) (pairs : Finset (Wavevector × Wavevector))
    (F : Wavevector × Wavevector → VelocityCoefficient) (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H)
    (hF : ∀ p ∈ pairs, ‖coefficientVec (F p)‖ ≤ H p) (x : T3) :
    ‖complexRealPartEuclidean (finiteFourierReconstruction (outputs \ M) (pairOutputCoeff pairs F) x)‖ ≤
      outputTail H M := by
  apply (norm_real_reconstruction_le_sum (outputs \ M) _ x).trans
  calc
    _ ≤ ∑ q ∈ outputs \ M, ∑ p ∈ pairs, if p.1 + p.2 = q then H p else 0 :=
      Finset.sum_le_sum (fun q _ ↦ norm_pairOutputCoeff_le pairs F H hF q)
    _ = ∑ p ∈ pairs, if p.1 + p.2 ∈ outputs \ M then H p else 0 := sum_collected_majorant pairs _ H
    _ ≤ ∑ p ∈ pairs, if p.1 + p.2 ∈ M then 0 else H p := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hm : p.1 + p.2 ∈ M
      · simp [Finset.mem_sdiff, hm]
      · by_cases ho : p.1 + p.2 ∈ outputs <;> simp [Finset.mem_sdiff, hm, ho, hH p]
    _ ≤ _ := finite_exterior_sum_le_outputTail H hH hSum M pairs

theorem exists_uniform_exterior_reconstruction_lt
    (F : Wavevector × Wavevector → VelocityCoefficient) (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (hF : ∀ p, ‖coefficientVec (F p)‖ ≤ H p)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M →
      ∀ (outputs : Finset Wavevector) (pairs : Finset (Wavevector × Wavevector)) (x : T3),
        ‖complexRealPartEuclidean (finiteFourierReconstruction (outputs \ M) (pairOutputCoeff pairs F) x)‖ < epsilon := by
  obtain ⟨core, hc⟩ := exists_outputTail_lt H hH hSum epsilon hepsilon
  exact ⟨core, fun M hM outputs pairs x ↦
    (norm_exterior_reconstruction_le_outputTail M outputs pairs F H hH hSum (fun p _ ↦ hF p) x).trans_lt (hc M hM)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeExteriorReconstructionTail
