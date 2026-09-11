import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBilinearLocalization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PhysicalPressurePair

/-!
# Physical pressure localization with a first-derivative patch cost

On actual Fourier curl inputs, the inverse source frequency is paid by
the velocity coefficient. The derivative phase then cancels against the
normalization of the patch's physical gradient energy. The remaining
velocity and receiver Fourier l1 norms are explicit, not dynamically
bounded by this spatial estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeZeroModeCurlBridge
open PancakeCurlOutputTail PancakeIncomingLowSourceEnergy PancakeFourierPressureStrain
open ComplexPressureConvolution FourierPressureTraceSymbol PhysicalPressurePair
open PancakeFiniteFourierLocalization PressureBilinearLocalization FourierCoordinateDerivatives
open FourierEllipticProductEnergy Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def physicalCommutatorCost (P K : Finset Wavevector) (u v : FourierVelocity) : ℝ :=
  144 * (∑ p ∈ P, ‖coefficientVec (u p)‖) ^ 2 * (∑ k ∈ K, ‖coefficientVec (v k)‖) ^ 2

theorem physicalCommutatorCost_nonneg (P K : Finset Wavevector) (u v : FourierVelocity) :
    0 ≤ physicalCommutatorCost P K u v := by unfold physicalCommutatorCost; positivity

theorem norm_curl_div_frequency_le (u : FourierVelocity) (p : Wavevector) :
    ‖coefficientVec (fourierCurl u p)‖ / ‖frequencyVec p‖ ≤
      ‖unitTorusDerivativePhase‖ * ‖coefficientVec (u p)‖ := by
  by_cases hp : frequencyVec p = 0
  · rw [hp, norm_zero, div_zero]
    positivity
  apply (div_le_iff₀ (norm_pos_iff.mpr hp)).mpr
  have h := norm_fourierCurl_le u p
  rw [norm_derivativePhase]
  nlinarith only [h]

theorem commutator_energy_fourierCurl_le (e : R3) (he : ‖e‖ = 1)
    (A P K Q : Finset Wavevector) (c : Wavevector → ℂ) (u v : FourierVelocity)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, ∀ a ∈ A, p + k + a ∈ Q) :
    (∑ q ∈ Q, ‖PressureBilinearLocalization.commutatorCoefficient e A P K c (fourierCurl u) v q‖ ^ 2) ≤
      physicalCommutatorCost P K u v * (‖unitTorusDerivativePhase‖ ^ 2 * coordinateEnergy A c) := by
  have h := PressureBilinearLocalization.commutator_energy_le e he A P K Q c (fourierCurl u) v (fourierCurl_zero u) hQ
  have hs : (∑ p ∈ P, ‖coefficientVec (fourierCurl u p)‖ / ‖frequencyVec p‖) ≤
      ‖unitTorusDerivativePhase‖ * ∑ p ∈ P, ‖coefficientVec (u p)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ ↦ norm_curl_div_frequency_le u p)
  have hG : 0 ≤ coordinateEnergy A c := by unfold coordinateEnergy scalarEnergy; positivity
  have hn : 0 ≤ ∑ p ∈ P, ‖coefficientVec (fourierCurl u p)‖ / ‖frequencyVec p‖ :=
    Finset.sum_nonneg (fun _ _ ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ hn hs 2
  have hm := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 144)
      (sq_nonneg (∑ k ∈ K, ‖coefficientVec (v k)‖))) hG)
  unfold physicalCommutatorCost
  nlinarith only [h, hm]

theorem commutator_energy_le_physical_gradient (e : R3) (he : ‖e‖ = 1)
    (A P K Q : Finset Wavevector) (c : Wavevector → ℂ) (u v : FourierVelocity)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, ∀ a ∈ A, p + k + a ∈ Q) :
    (∑ q ∈ Q, ‖PressureBilinearLocalization.commutatorCoefficient e A P K c (fourierCurl u) v q‖ ^ 2) ≤
      physicalCommutatorCost P K u v *
        (∑ j : Fin 3, ∫ x : T3, ‖polynomialDerivative A c j x‖ ^ 2) := by
  simp only [integral_polynomialDerivative_sq, ← Finset.mul_sum]
  exact commutator_energy_fourierCurl_le e he A P K Q c u v hQ

theorem sum_commutator_energy_fourierCurl_le {ι : Type*} [Fintype ι]
    (e : ι → R3) (he : ∀ i, ‖e i‖ = 1) (A Q : ι → Finset Wavevector)
    (P K : Finset Wavevector) (c : ι → Wavevector → ℂ) (u v : FourierVelocity)
    (hQ : ∀ i, ∀ p ∈ P, ∀ k ∈ K, ∀ a ∈ A i, p + k + a ∈ Q i) :
    (∑ i, ∑ q ∈ Q i,
      ‖PressureBilinearLocalization.commutatorCoefficient (e i) (A i) P K (c i) (fourierCurl u) v q‖ ^ 2) ≤
      physicalCommutatorCost P K u v * (‖unitTorusDerivativePhase‖ ^ 2 * ∑ i, coordinateEnergy (A i) (c i)) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    commutator_energy_fourierCurl_le (e i) (he i) (A i) P K (Q i) (c i) u v (hQ i))
  simpa only [← Finset.mul_sum] using h

/-- The localized physical pressure has the sign fixed by the actual
pressure Hessian, not by a convention for the model pair kernel. -/
theorem physical_pressure_localization_identity (e : R3) (A M : Finset Wavevector)
    (c : Wavevector → ℂ) (u : FourierVelocity) (hu : ∀ k ∈ M, modeDot k (u k) = 0) (q : Wavevector) :
    vectorConvolution A (finiteCutoffOutputModes M M) c
        (fun r ↦ (pressureHessianCoeff M u r).trace • complexTiltSymbol e r) q +
      localizedSource e A M M c (fourierCurl u) (fourierCurl u) q =
        -PressureBilinearLocalization.commutatorCoefficient e A M M c (fourierCurl u) (fourierCurl u) q := by
  have h : vectorConvolution A (finiteCutoffOutputModes M M) c
      (fun r ↦ (pressureHessianCoeff M u r).trace • complexTiltSymbol e r) q =
      -localizedOutput e A M M c (fourierCurl u) (fourierCurl u) q := by
    simp only [vectorConvolution, localizedOutput, pressureHessian_tilt_eq_pairConvolution e M u hu,
      smul_neg, Finset.sum_neg_distrib]
  rw [h, ← localizedOutput_sub_localizedSource]
  abel

end Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization
