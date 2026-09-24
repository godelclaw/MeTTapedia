import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxSevenInputHeat
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxPolarization

/-!
# Actual all-input expansion of the heat-commutator work

The convection fiber is summed before insertion into the constructed
variation operator. This identifies each seven-input term with the
original infinite Fourier commutator, not a surrogate rate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSevenInputExpansion

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeSobolevFiberEnvelope PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakeFilteredStrainDynamics PancakeHigherDerivativeMoments
open PancakeCoefficientLimitEquation PancakeInfiniteVelocityEnvelope PancakeBlockReality
open PeriodicGradientFluxTriple FourierHeatFlow InfiniteFilteredEquation
open ExchangedFluxModeDynamics ExchangedFluxAdjoint ExchangedFluxAdjointPairing
open ExchangedFluxHeatRepresentation ExchangedFluxHeatAdjoint ExchangedFluxPolarization
open ExchangedFluxVariation ExchangedFluxAdjointSeries LongitudinalGradientFlux
open ExchangedFluxSevenInputHeat

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def convectionInputCLM (q : Wavevector) : VelocityCoefficient →L[ℂ] C3 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm.toContinuousLinearMap.comp
    ((-unitTorusDerivativePhase) • (lerayLinear q).toContinuousLinearMap)

theorem convectionInputCLM_apply (q : Wavevector) (v : VelocityCoefficient) :
    convectionInputCLM q v = coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • v)) := by
  change coefficientVec ((-unitTorusDerivativePhase) • lerayMode q v) = _
  rw [lerayMode_smul]

def heatAtom (ν σ : ℝ) (u : FourierVelocity) (q k : Wavevector) : C3 :=
  (multiplier ν σ q - multiplier ν σ k * multiplier ν σ (q - k)) •
    coefficientVec (convectionAtom u k (q - k))

theorem hasSum_heatAtom {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    HasSum (heatAtom ν σ u q) (coefficientVec (nonlinearCommutator ν σ u q)) := by
  let chi : Wavevector → ℂ := fun k ↦ (multiplier ν σ k : ℂ)
  have hchi (k : Wavevector) : ‖chi k‖ ≤ 1 := by
    simpa only [chi, Complex.norm_real, Real.norm_of_nonneg (multiplier_pos ν σ k).le] using
      multiplier_le_one hν hσ k
  have hf (i : Fin 3) : Summable (fun k ↦ outputFiber q u k i) :=
    ((summable_pairEnvelope (fourierMoment 2 u) (fourierMoment_nonneg 2 u) hu).prod_factor q).of_norm_bounded
      (fun k ↦ norm_outputFiber_le_momentEnvelope u (fourierMoment 2 u)
        (fourierMoment_nonneg 2 u) (fun _ ↦ le_rfl) q k i)
  have hs (i : Fin 3) := summable_subgridConvection chi u 1 hchi q i (hf i)
  have hv : HasSum (fun k ↦ (chi q - chi k * chi (q - k)) • outputFiber q u k)
      (subgridConvection chi u q) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [HasSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      InfiniteFilteredEquation.subgridConvection] using (hs i).hasSum
  have hh := (convectionInputCLM q).hasSum hv
  rw [convectionInputCLM_apply, ← subgridForce, ← nonlinearCommutator_eq_subgridForce hν hσ u hu] at hh
  convert hh using 1
  funext k
  simp only [heatAtom, convectionAtom, add_sub_cancel, map_smul, convectionInputCLM_apply,
    chi, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  rfl

theorem insertion_commutator_eq_tsum (inner : Bool) {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (q m n : Wavevector) (p : TripleIndex) :
    ⟪insertionSlot inner (coefficients ν σ u) q m n
      (coefficientVec (nonlinearCommutator ν σ u q)), mode (coefficients ν σ u) p⟫ =
      ∑' k, heatInteraction inner ν σ u k (q - k) m n p := by
  have h := (insertionSlot inner (coefficients ν σ u) q m n).hasSum
    (hasSum_heatAtom hν hσ u hu q)
  have hi := (innerSL ℝ (mode (coefficients ν σ u) p)).hasSum h
  simpa only [innerSL_apply_apply, real_inner_comm, heatInteraction, heatAtom, add_sub_cancel]
    using hi.tsum_eq.symm

theorem insertion_projectedFlux_eq_neg_tsum (inner : Bool) {ν σ : ℝ}
    (hν : 0 ≤ ν) (hσ : 0 ≤ σ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q m n : Wavevector) :
    ⟪insertionSlot inner (coefficients ν σ u) q m n
      (coefficientVec (nonlinearCommutator ν σ u q)), projectedFlux 0 (coefficients ν σ u)⟫ =
      -(∑' p : TripleIndex, ∑' k, heatInteraction inner ν σ u k (q - k) m n p) := by
  have hu' := summable_fourierMoment_coefficients hν hσ u 1
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)
  rw [← neg_tsum_mode_eq_projectedFlux _ hu'
    (coefficients_transverse ν σ u hd) (coefficients_reality ν σ u hr), inner_neg_right]
  congr 1
  rw [show ⟪insertionSlot inner (coefficients ν σ u) q m n
      (coefficientVec (nonlinearCommutator ν σ u q)), ∑' p, mode (coefficients ν σ u) p⟫ =
      ∑' p, ⟪insertionSlot inner (coefficients ν σ u) q m n
        (coefficientVec (nonlinearCommutator ν σ u q)), mode (coefficients ν σ u) p⟫ from
    (innerSL ℝ _).map_tsum (summable_norm_mode _ hu').of_norm]
  exact tsum_congr (fun p ↦ insertion_commutator_eq_tsum inner hν hσ u hu q m n p)

/-- All seven input legs, with the complete outer and inner slot multiplicities. -/
def sevenInputWork (ν σ : ℝ) (u : FourierVelocity) (q : Wavevector) : ℝ :=
  (∑' mn : Wavevector × Wavevector, ∑' p : TripleIndex, ∑' k,
    heatInteraction false ν σ u k (q - k) mn.1 mn.2 p) +
  2 * (∑' mn : Wavevector × Wavevector, ∑' p : TripleIndex, ∑' k,
    heatInteraction true ν σ u k (q - k) mn.1 mn.2 p)

theorem coefficientPairing_eq_sevenInputWork {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) :
    ⟪coefficientVec (nonlinearCommutator ν σ u q), heatCoefficientTest ν σ u q⟫ =
      sevenInputWork ν σ u q := by
  have hu' := summable_fourierMoment_coefficients hν hσ u 1
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)
  rw [heatCoefficientTest, coefficientTest, inner_sub_right, inner_neg_right, real_inner_smul_right,
    ← outer_pairing_sum _ (nonlinearCommutator ν σ u) hu',
    ← left_pairing_sum _ (nonlinearCommutator ν σ u) hu']
  have ho (mn : Wavevector × Wavevector) :
      ⟪mixedMode (nonlinearCommutator ν σ u) (coefficients ν σ u) (coefficients ν σ u) (q, mn),
        projectedFlux 0 (coefficients ν σ u)⟫ =
      -(∑' p : TripleIndex, ∑' k, heatInteraction false ν σ u k (q - k) mn.1 mn.2 p) := by
    simpa only [insertionSlot, Bool.false_eq_true, ↓reduceIte, outerSlot_apply] using
      insertion_projectedFlux_eq_neg_tsum false hν hσ u hu hd hr q mn.1 mn.2
  have hl (mn : Wavevector × Wavevector) :
      ⟪mixedMode (coefficients ν σ u) (nonlinearCommutator ν σ u) (coefficients ν σ u) (mn.1, (q, mn.2)),
        projectedFlux 0 (coefficients ν σ u)⟫ =
      -(∑' p : TripleIndex, ∑' k, heatInteraction true ν σ u k (q - k) mn.1 mn.2 p) := by
    simpa only [insertionSlot, ↓reduceIte, leftSlot_apply] using
      insertion_projectedFlux_eq_neg_tsum true hν hσ u hu hd hr q mn.1 mn.2
  simp only [ho, hl, tsum_neg, neg_neg, mul_neg, sub_neg_eq_add, sevenInputWork]

/-- The full infinite commutator work is exactly this nested seven-input series. -/
theorem inner_commutatorVariation_eq_sevenInputWork {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    ⟪fluxVariation (coefficients ν σ u) (nonlinearCommutator ν σ u),
      projectedFlux 0 (coefficients ν σ u)⟫ = ∑' q, sevenInputWork ν σ u q := by
  rw [inner_commutatorVariation_eq_tsum hν hσ u hu]
  exact tsum_congr (coefficientPairing_eq_sevenInputWork hν hσ u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hd hr)

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxSevenInputExpansion
