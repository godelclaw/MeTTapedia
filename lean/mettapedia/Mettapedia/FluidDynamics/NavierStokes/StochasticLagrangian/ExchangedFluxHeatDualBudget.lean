import Mettapedia.Analysis.WeightedInnerProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxHeatAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorScaleBudget

/-!
# Explicit all-scale dual cost of the actual heat test

The negative-order commutator square integral is paid by initial kinetic
energy. Weighted Young bounds its coefficient pairing by that paid term
plus the positive-order square integral of the constructed test. The latter
is an extended nonnegative quantity: finiteness is not assumed or proved.
The absolute-value bound is separate from the exact signed time identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatDualBudget

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity InfiniteConvectionEnergy
open FourierHeatFlow FourierHeatCommutatorTime FourierHeatCommutatorParameter
open FourierHeatCommutatorScaleBudget ExchangedFluxHeatAdjoint PancakeLatticeDecayEnvelope

def commutatorSquareIntegral (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) : ℝ≥0∞ :=
  ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖coefficientVec (nonlinearCommutator ν σ (u τ) q)‖ ^ 2)

def testSquareIntegral (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) (q : Wavevector) : ℝ≥0∞ :=
  ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖heatCoefficientTest ν σ (u τ) q‖ ^ 2)

def negativeCommutatorCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' q, ENNReal.ofReal (1 / (1 + ‖frequencyVec q‖) ^ 2) * commutatorSquareIntegral ν u t q

/-- This is the explicit remaining norm cost; it is permitted to be infinite. -/
def positiveTestCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' q, ENNReal.ofReal ((1 + ‖frequencyVec q‖) ^ 2) * testSquareIntegral ν u t q

def absolutePairingCost (ν : ℝ) (u : ℝ → FourierVelocity) (t : ℝ) : ℝ≥0∞ :=
  ∑' q, ∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (2 * |⟪coefficientVec (nonlinearCommutator ν σ (u τ) q),
      heatCoefficientTest ν σ (u τ) q⟫|)

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)

include hg hsg hu

theorem lintegral_commutator_sq_eq {σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
    (∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2)) =
      ENNReal.ofReal (accumulatedCoefficient ν s.coefficients σ t q) := by
  have hi : IntervalIntegrable (fun τ ↦
      ‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2) volume 0 t :=
    ((continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ q).mono
      (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  rw [accumulatedCoefficient, intervalIntegral.integral_of_le ht.1,
    ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun _ ↦ sq_nonneg _))]

theorem commutatorSquareIntegral_eq (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
    commutatorSquareIntegral ν s.coefficients t q =
      ENNReal.ofReal (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrableOn_accumulatedCoefficient s g hg hsg hu hν q t ht)
    (ae_of_all _ (fun σ ↦ accumulatedCoefficient_nonneg _ _ σ _ ht.1 q))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  exact lintegral_commutator_sq_eq s g hg hsg hu hν hσ.le t ht q

theorem negativeCommutatorCost_eq (hν : 0 < ν) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    negativeCommutatorCost ν s.coefficients t =
      ENNReal.ofReal (∑' q : Wavevector, (1 / (1 + ‖frequencyVec q‖) ^ 2) *
        (∫ σ : ℝ in Set.Ioi 0, accumulatedCoefficient ν s.coefficients σ t q)) := by
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun q ↦ mul_nonneg (by positivity) (integral_nonneg
      (fun σ ↦ accumulatedCoefficient_nonneg _ _ σ _ ht.1 q)))
    (summable_weighted_integral s g hg hsg hu hν t ht)]
  apply tsum_congr
  intro q
  rw [ENNReal.ofReal_mul (by positivity), commutatorSquareIntegral_eq s g hg hsg hu hν t ht q]

theorem negativeCommutatorCost_le_initial (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    negativeCommutatorCost ν s.coefficients t ≤
      ENNReal.ofReal ((2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) *
        ∑' q, latticeDecayWeight q) := by
  rw [negativeCommutatorCost_eq s g hg hsg hu hν t ht]
  exact ENNReal.ofReal_le_ofReal (tsum_weighted_integral_le_initial s g hg hsg hu hν t ht)

theorem coefficientPairingCost_le (hν : 0 < ν) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (q : Wavevector) {a : ℝ} (ha : 0 < a) :
    (∫⁻ σ : ℝ in Set.Ioi 0, ∫⁻ τ : ℝ in Set.Ioc 0 t,
      ENNReal.ofReal (2 * |⟪coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q),
        heatCoefficientTest ν σ (s.coefficients τ) q⟫|)) ≤
    ENNReal.ofReal a * commutatorSquareIntegral ν s.coefficients t q +
      ENNReal.ofReal a⁻¹ * testSquareIntegral ν s.coefficients t q := by
  let c := fun σ ↦ ∫⁻ τ : ℝ in Set.Ioc 0 t,
    ENNReal.ofReal (‖coefficientVec (nonlinearCommutator ν σ (s.coefficients τ) q)‖ ^ 2)
  have hc : AEMeasurable c (volume.restrict (Set.Ioi 0)) := by
    have hm : AEMeasurable (fun σ ↦ ENNReal.ofReal
        (accumulatedCoefficient ν s.coefficients σ t q)) (volume.restrict (Set.Ioi 0)) :=
      (((continuousOn_integral_norm_commutator_sq s g hg hsg hu hν.le q t ht).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi).aemeasurable.ennreal_ofReal
    apply hm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact (lintegral_commutator_sq_eq s g hg hsg hu hν hσ.le t ht q).symm
  calc
    _ ≤ ∫⁻ σ : ℝ in Set.Ioi 0, ENNReal.ofReal a * c σ + ENNReal.ofReal a⁻¹ *
        (∫⁻ τ : ℝ in Set.Ioc 0 t, ENNReal.ofReal (‖heatCoefficientTest ν σ (s.coefficients τ) q‖ ^ 2)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      apply Mettapedia.Analysis.WeightedInnerProduct.lintegral_two_mul_abs_inner_le _ _ ha
      exact (((continuousOn_norm_commutator_sq s g hg hsg hu hν.le hσ.le q).mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))).aestronglyMeasurable
          measurableSet_Ioc).aemeasurable.ennreal_ofReal
    _ = _ := by
      rw [lintegral_add_left' (hc.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

/-- The accumulated pairing has exactly one unpaid positive-order test cost. -/
theorem absolutePairingCost_le (hν : 0 < ν) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal ε * negativeCommutatorCost ν s.coefficients t +
      ENNReal.ofReal ε⁻¹ * positiveTestCost ν s.coefficients t := by
  have hi (q : Wavevector) : (ε * (1 / (1 + ‖frequencyVec q‖) ^ 2))⁻¹ =
      ε⁻¹ * (1 + ‖frequencyVec q‖) ^ 2 := by
    field_simp
  have hq (q : Wavevector) := coefficientPairingCost_le s g hg hsg hu hν t ht q
    (by positivity : 0 < ε * (1 / (1 + ‖frequencyVec q‖) ^ 2))
  simp only [hi, ENNReal.ofReal_mul hε.le, ENNReal.ofReal_mul (inv_nonneg.mpr hε.le),
    mul_assoc] at hq
  have h := ENNReal.tsum_le_tsum hq
  simpa only [absolutePairingCost, negativeCommutatorCost, positiveTestCost,
    ENNReal.tsum_add, ENNReal.tsum_mul_left] using h

/-- Initial kinetic energy pays the commutator term, not the test-field term. -/
theorem absolutePairingCost_le_initial_add_test (hν : 0 < ν)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    absolutePairingCost ν s.coefficients t ≤
      ENNReal.ofReal ε * ENNReal.ofReal
        ((2 * kineticEnergy u₀ ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) * ∑' q, latticeDecayWeight q) +
      ENNReal.ofReal ε⁻¹ * positiveTestCost ν s.coefficients t :=
  (absolutePairingCost_le s g hg hsg hu hν t ht hε).trans
    (add_le_add (mul_le_mul_right (negativeCommutatorCost_le_initial s g hg hsg hu hν t ht) _) le_rfl)

open scoped ComplexConjugate
open Mettapedia.Analysis PancakeHigherLocalVelocity PancakeContinuousCoordinateJet
open PancakeArbitraryDataBlocks PancakeHigherDerivativeMoments PancakePeriodicVorticityEquation
open ExchangedFluxSeriesBudget LongitudinalGradientFlux

omit hg hsg hu in
/-- The signed balance and the dual bound hold for the same constructed physical solution. -/
theorem exists_physical_local_adjoint_balance (ν : ℝ) (hν : 0 < ν)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (fullGramEnergy ν (s.coefficients t) +
            (∫ τ in (0 : ℝ)..t, ‖projectedFlux 0 (s.coefficients τ)‖ ^ 2) =
          fullGramEnergy ν (torusFourierVelocity f) +
            2 * (∫ τ in (0 : ℝ)..t, ∫ σ : ℝ in Set.Ioi 0,
              coefficientWorkDensity ν σ (s.coefficients τ))) ∧
          (∀ ε > (0 : ℝ), absolutePairingCost ν s.coefficients t ≤
            ENNReal.ofReal ε * ENNReal.ofReal
              ((2 * kineticEnergy (torusFourierVelocity f) ^ 2 / (ν ^ 2 * (2 * Real.pi) ^ 2)) *
                ∑' q, latticeDecayWeight q) +
            ENNReal.ofReal ε⁻¹ * positiveTestCost ν s.coefficients t) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hsg, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  have hu2 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q :=
    fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  refine ⟨T, hT, B, hB, s, fun t ht ↦ ⟨?_, ?_⟩⟩
  · exact full_coefficient_gram_energy_identity s hν hB g hg hsg hu t ht
  · exact fun ε hε ↦ absolutePairingCost_le_initial_add_test s g hg hsg hu2 hν t ht hε

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxHeatDualBudget
