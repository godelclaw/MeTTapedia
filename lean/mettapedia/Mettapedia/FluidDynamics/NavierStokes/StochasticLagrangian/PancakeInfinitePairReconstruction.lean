import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInteractionTruncationTail
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeExteriorReconstructionTail
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# An actual infinite real Fourier interaction field

The field is the absolutely convergent sum of the physical Fourier pair
waves. Collecting retained pairs gives the existing finite reconstruction,
and the omitted-interaction majorant bounds their difference uniformly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePairReconstruction

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFrequencyProjectorCommutator PancakeExteriorReconstructionTail
open PancakeInteractionTruncationTail
open PancakeTransverseEnergyFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def realPairWave (F : Wavevector × Wavevector → VelocityCoefficient)
    (p : Wavevector × Wavevector) (x : T3) : R3 :=
  complexRealPartEuclideanCLM (UnitAddTorus.mFourier (p.1 + p.2) x • F p)

def infinitePairField (F : Wavevector × Wavevector → VelocityCoefficient) (x : T3) : R3 :=
  ∑' p : Wavevector × Wavevector, realPairWave F p x

theorem norm_realPairWave_le (F : Wavevector × Wavevector → VelocityCoefficient)
    (p : Wavevector × Wavevector) (x : T3) :
    ‖realPairWave F p x‖ ≤ ‖coefficientVec (F p)‖ := by
  change ‖complexRealPartEuclidean (UnitAddTorus.mFourier (p.1 + p.2) x • F p)‖ ≤ _
  apply (norm_realPart_le_coefficientVec _).trans
  change ‖UnitAddTorus.mFourier (p.1 + p.2) x • coefficientVec (F p)‖ ≤ _
  rw [norm_smul]
  have h := (UnitAddTorus.mFourier (p.1 + p.2)).norm_coe_le_norm x
  rw [UnitAddTorus.mFourier_norm] at h
  nlinarith [norm_nonneg (coefficientVec (F p))]

theorem continuous_realPairWave (F : Wavevector × Wavevector → VelocityCoefficient)
    (p : Wavevector × Wavevector) : Continuous (realPairWave F p) :=
  complexRealPartEuclideanCLM.continuous.comp
    ((UnitAddTorus.mFourier (p.1 + p.2)).continuous.smul continuous_const)

theorem summable_realPairWave (F : Wavevector × Wavevector → VelocityCoefficient)
    (H : Wavevector × Wavevector → ℝ) (hSum : Summable H)
    (hF : ∀ p, ‖coefficientVec (F p)‖ ≤ H p) (x : T3) :
    Summable (fun p ↦ realPairWave F p x) :=
  hSum.of_norm_bounded (fun p ↦ (norm_realPairWave_le F p x).trans (hF p))

theorem continuous_infinitePairField (F : Wavevector × Wavevector → VelocityCoefficient)
    (H : Wavevector × Wavevector → ℝ) (hSum : Summable H)
    (hF : ∀ p, ‖coefficientVec (F p)‖ ≤ H p) : Continuous (infinitePairField F) :=
  continuous_tsum (continuous_realPairWave F) hSum
    (fun p x ↦ (norm_realPairWave_le F p x).trans (hF p))

theorem finite_reconstruction_eq_retainedPairSum (M : Finset Wavevector)
    (F : Wavevector × Wavevector → VelocityCoefficient) (x : T3) :
    complexRealPartEuclideanCLM
      (finiteFourierReconstruction M (pairOutputCoeff (M ×ˢ M) F) x) =
        ∑ p ∈ retainedPairs M, realPairWave F p x := by
  classical
  have h : finiteFourierReconstruction M (pairOutputCoeff (M ×ˢ M) F) x =
      ∑ p ∈ retainedPairs M, UnitAddTorus.mFourier (p.1 + p.2) x • F p := by
    simp only [finiteFourierReconstruction, pairOutputCoeff, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [retainedPairs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp [smul_ite, eq_comm]
  rw [h, map_sum]
  rfl

theorem norm_infinitePairField_sub_retained_le (F : Wavevector × Wavevector → VelocityCoefficient)
    (H : Wavevector × Wavevector → ℝ) (hSum : Summable H)
    (hF : ∀ p, ‖coefficientVec (F p)‖ ≤ H p) (M : Finset Wavevector) (x : T3) :
    ‖infinitePairField F x - complexRealPartEuclideanCLM
      (finiteFourierReconstruction M (pairOutputCoeff (M ×ˢ M) F) x)‖ ≤ interactionTail H M := by
  rw [finite_reconstruction_eq_retainedPairSum]
  exact norm_tsum_sub_finite_le_tail (fun p ↦ realPairWave F p x) H hSum
    (fun p ↦ (norm_realPairWave_le F p x).trans (hF p)) M

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePairReconstruction
