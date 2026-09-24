import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxSeriesBudget

/-!
# Auxiliary heat flow of the actual Fourier velocity

The heat multiplier preserves transverse reality and decreases absolute
Fourier moments. Its commutator with the full nonlinear velocity RHS is
the already constructed all-input subgrid force, including its pressure
correction. This auxiliary heat parameter is not physical NS time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatFlow

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics LocalFilteredVorticity
open FourierVorticityPairDynamics FourierStretchingInteractionDynamics
open PancakeCurlOutputTail PancakeInfiniteVelocityEnvelope
open PancakeCoefficientLimitEquation PancakeBlockReality
open PancakeSobolevFiberEnvelope

def multiplier (ν σ : ℝ) (k : Wavevector) : ℝ := Real.exp (-modeDamping ν k * σ)

def coefficients (ν σ : ℝ) (u : FourierVelocity) : FourierVelocity :=
  filteredVelocity (fun k ↦ (multiplier ν σ k : ℂ)) u

theorem multiplier_pos (ν σ : ℝ) (k : Wavevector) : 0 < multiplier ν σ k := Real.exp_pos _

theorem multiplier_le_one {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (k : Wavevector) :
    multiplier ν σ k ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h : 0 ≤ modeDamping ν k := by unfold modeDamping; positivity
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) hσ

theorem multiplier_neg (ν σ : ℝ) (k : Wavevector) : multiplier ν σ (-k) = multiplier ν σ k := by
  have h : frequencyVec (-k) = -frequencyVec k := by
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  simp only [multiplier, modeDamping, h, norm_neg]

theorem coefficients_transverse (ν σ : ℝ) (u : FourierVelocity)
    (hu : ∀ k, modeDot k (u k) = 0) (k : Wavevector) :
    modeDot k (coefficients ν σ u k) = 0 := filteredVelocity_transverse _ _ k (hu k)

theorem coefficients_reality (ν σ : ℝ) (u : FourierVelocity)
    (hu : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) :
    coefficients ν σ u (-k) = coefficientConjugate (coefficients ν σ u k) := by
  ext i
  simp [coefficients, filteredVelocity, multiplier_neg, hu, coefficientConjugate]

theorem fourierCurl_coefficients (ν σ : ℝ) (u : FourierVelocity) :
    fourierCurl (coefficients ν σ u) = coefficients ν σ (fourierCurl u) :=
  fourierCurl_filteredVelocity _ _

theorem norm_coefficients_le {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (k : Wavevector) : ‖coefficients ν σ u k‖ ≤ ‖u k‖ := by
  change ‖(multiplier ν σ k : ℂ) • u k‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (multiplier_pos ν σ k).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_le_one hν hσ k)

theorem fourierMoment_coefficients_le {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (m : ℕ) (k : Wavevector) :
    fourierMoment m (coefficients ν σ u) k ≤ fourierMoment m u k := by
  have h : ‖coefficientVec (coefficients ν σ u k)‖ ≤ ‖coefficientVec (u k)‖ := by
    change ‖(multiplier ν σ k : ℂ) • coefficientVec (u k)‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (multiplier_pos ν σ k).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplier_le_one hν hσ k)
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem summable_fourierMoment_coefficients {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (m : ℕ) (hu : Summable (fourierMoment m u)) :
    Summable (fourierMoment m (coefficients ν σ u)) :=
  hu.of_nonneg_of_le (fourierMoment_nonneg _ _) (fourierMoment_coefficients_le hν hσ u m)

/-- The actual nonlinear discrepancy between smoothing and evolution. -/
def nonlinearCommutator (ν σ : ℝ) (u : FourierVelocity) : FourierVelocity :=
  coefficients ν σ (infiniteVelocityRHS 0 u) - infiniteVelocityRHS 0 (coefficients ν σ u)

theorem nonlinearCommutator_eq_subgridForce {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    nonlinearCommutator ν σ u =
      InfiniteFilteredEquation.subgridForce (fun k ↦ (multiplier ν σ k : ℂ)) u := by
  have hg := fourierMoment_nonneg 2 u
  have hf (q : Wavevector) (i : Fin 3) : Summable (fun k ↦ outputFiber q u k i) :=
    ((summable_pairEnvelope (fourierMoment 2 u) hg hu).prod_factor q).of_norm_bounded
      (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u) hg (fun _ ↦ le_rfl) q k i)
  funext q
  have h := InfiniteFilteredEquation.filtered_infiniteVelocityRHS
    (fun k ↦ (multiplier ν σ k : ℂ)) u 1 (fun k ↦ by
      simpa only [Complex.norm_real, Real.norm_of_nonneg (multiplier_pos ν σ k).le] using
        multiplier_le_one hν hσ k) 0 q (hf q)
  change coefficients ν σ (infiniteVelocityRHS 0 u) q -
    infiniteVelocityRHS 0 (coefficients ν σ u) q = _
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatFlow
