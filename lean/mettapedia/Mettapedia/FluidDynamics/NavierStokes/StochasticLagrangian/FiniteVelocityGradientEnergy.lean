import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransport

/-!
# Finite-output velocity gradients controlled by full kinetic energy

Cauchy--Schwarz bounds every retained velocity-gradient entry using the
full input kinetic energy and an explicit squared derivative weight of
the filter. No gradient bound on the unresolved velocity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVelocityGradientEnergy

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments
open PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy
open PancakeConcreteSmoothCellCutoff
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open InfiniteFourierDiffusion InfiniteConvectionEnergy FourierFiniteSupport FiniteAngularTransport

local notation "T3" => UnitAddTorus (Fin 3)

def derivativeWeight (χ : Wavevector → ℂ) (q : Wavevector) : ℝ :=
  (2 * Real.pi) * ‖frequencyVec q‖ * ‖χ q‖

def derivativeCutoffWeight (P : Finset Wavevector) (χ : Wavevector → ℂ) : ℝ :=
  ∑ q ∈ P, derivativeWeight χ q ^ 2

def derivativeAmplitude (P : Finset Wavevector) (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  ∑ q ∈ P, derivativeWeight χ q * ‖coefficientVec (u q)‖

theorem derivativeCutoffWeight_nonneg (P : Finset Wavevector) (χ : Wavevector → ℂ) :
    0 ≤ derivativeCutoffWeight P χ := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem derivativeAmplitude_nonneg (P : Finset Wavevector) (χ : Wavevector → ℂ) (u : FourierVelocity) :
    0 ≤ derivativeAmplitude P χ u := by
  unfold derivativeAmplitude derivativeWeight
  positivity

theorem abs_velocityDerivative_le_amplitude (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hχ : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity) (j k : Fin 3) (x : T3) :
    |velocityDerivative (filteredVelocity χ u) j k x| ≤ derivativeAmplitude P χ u := by
  have hs (q : Wavevector) (hq : q ∉ P) : indexedDerivativeCoeff id j (filteredVelocity χ u) q = 0 := by
    simp [indexedDerivativeCoeff, filteredVelocity, hχ q hq]
  change |(fullFourierField id (indexedDerivativeCoeff id j (filteredVelocity χ u)) x k).re| ≤ _
  rw [fullFourierField_eq_sum P _ hs]
  calc
    _ ≤ ‖(∑ q ∈ P, UnitAddTorus.mFourier q x • indexedDerivativeCoeff id j (filteredVelocity χ u) q) k‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖∑ q ∈ P, UnitAddTorus.mFourier q x • indexedDerivativeCoeff id j (filteredVelocity χ u) q‖ :=
      norm_le_pi_norm _ k
    _ ≤ ∑ q ∈ P, ‖UnitAddTorus.mFourier q x • indexedDerivativeCoeff id j (filteredVelocity χ u) q‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      simp only [norm_smul, norm_mFourier_apply, one_mul, indexedDerivativeCoeff,
        filteredVelocity, id_eq, norm_mul, norm_derivativePhase, derivativeWeight]
      calc
        _ ≤ (2 * Real.pi) * ‖frequencyVec q‖ * (‖χ q‖ * ‖coefficientVec (u q)‖) := by
          gcongr
          · exact norm_frequency_coordinate_le q j
          · exact norm_coefficient_sup_le_euclidean _
        _ = _ := by ring

theorem derivativeAmplitude_sq_le (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) :
    derivativeAmplitude P χ u ^ 2 ≤ derivativeCutoffWeight P χ * kineticEnergy u := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P (derivativeWeight χ) (fun q ↦ ‖coefficientVec (u q)‖)
  exact h.trans (mul_le_mul_of_nonneg_left
    (hu.sum_le_tsum P (fun _ _ ↦ sq_nonneg _)) (derivativeCutoffWeight_nonneg P χ))

theorem abs_velocityDerivative_le_sqrt_energy (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hχ : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖ ^ 2)) (E : ℝ) (hE : kineticEnergy u ≤ E)
    (j k : Fin 3) (x : T3) :
    |velocityDerivative (filteredVelocity χ u) j k x| ≤ Real.sqrt (derivativeCutoffWeight P χ * E) := by
  have hb := derivativeAmplitude_sq_le P χ u hu
  have hnE : 0 ≤ E := (LocalKineticEnergy.kineticEnergy_nonneg u).trans hE
  have hc := mul_le_mul_of_nonneg_left hE (derivativeCutoffWeight_nonneg P χ)
  have hsq := Real.sq_sqrt (mul_nonneg (derivativeCutoffWeight_nonneg P χ) hnE)
  have hp := Real.sqrt_nonneg (derivativeCutoffWeight P χ * E)
  apply (abs_velocityDerivative_le_amplitude P χ hχ u j k x).trans
  nlinarith only [hb, hc, hsq, hp]

end Mettapedia.FluidDynamics.NavierStokes.FiniteVelocityGradientEnergy
