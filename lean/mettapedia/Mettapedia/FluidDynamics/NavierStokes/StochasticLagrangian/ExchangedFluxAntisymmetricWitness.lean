import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxCoefficientFormula
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteLocalSolution

/-!
# A genuine coefficient pair with a surviving antisymmetric channel

The finite Fourier field is transverse, real, and mean zero. Its two
exchanged inner tests have opposite nonzero values. Consequently their
common-test channel vanishes, although their heat-integrated sum does not.
This is a coefficient-level obstruction, not a regularity counterexample
or a sign assertion for the complete nonlinear work.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAntisymmetricWitness

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakePeriodicVorticityEquation PancakeCurlOutputTail
open PeriodicGradientFluxSymbol PeriodicGradientFluxTriple
open ExchangedFluxModeDynamics ExchangedFluxSevenInputHeat ExchangedFluxInputExchange
open ExchangedFluxCoefficientFormula FourierVorticityPairDynamics FourierStretchingInteractionDynamics
open FourierHeatCommutatorKernel FourierHeatCommutatorReflection

def lowInput : Wavevector := ![1, 0, 0]
def highInput : Wavevector := ![2, 4, 0]
def companion : Wavevector := ![0, 1, 1]
def axisY : Wavevector := ![0, 1, 0]
def axisZ : Wavevector := ![0, 0, 1]
def target : TripleIndex := (lowInput, (axisY, axisZ))

def modes : Finset Wavevector :=
  {lowInput, -lowInput, highInput, -highInput, companion, -companion, axisY, -axisY, axisZ, -axisZ}

def raw (q : Wavevector) : VelocityCoefficient :=
  if q = lowInput then ![0, 1, 0]
  else if q = -lowInput then ![0, -1, 0]
  else if q = highInput then ![0, 0, 1]
  else if q = -highInput then ![0, 0, -1]
  else if q = companion then ![1, 1, -1]
  else if q = -companion then ![-1, -1, 1]
  else if q = axisY then ![1, 0, 1]
  else if q = -axisY then ![-1, 0, -1]
  else if q = axisZ then ![1, 1, 0]
  else if q = -axisZ then ![-1, -1, 0]
  else 0

/-- Normalize by `2π` so all vorticity coefficient calculations are rational. -/
def velocity (q : Wavevector) : VelocityCoefficient := (-unitTorusDerivativePhase⁻¹) • raw q

theorem raw_eq_zero_of_not_mem (q : Wavevector) (hq : q ∉ modes) : raw q = 0 := by
  unfold raw
  split_ifs <;> simp_all [modes]

theorem raw_transverse (q : Wavevector) : modeDot q (raw q) = 0 := by
  unfold raw
  split_ifs <;> simp_all [modeDot, lowInput, highInput, companion, axisY, axisZ, Fin.sum_univ_three]

theorem velocity_transverse (q : Wavevector) : modeDot q (velocity q) = 0 := by
  rw [velocity, modeDot_smul, raw_transverse, mul_zero]

theorem modes_neg_closed (q : Wavevector) : -q ∈ modes ↔ q ∈ modes := by
  simp only [modes, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg, neg_neg]
  tauto

theorem raw_neg (q : Wavevector) : raw (-q) = -raw q := by
  by_cases hq : q ∈ modes
  · simp only [modes, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;> subst q <;>
      ext i <;> fin_cases i <;>
      norm_num [raw, lowInput, highInput, companion, axisY, axisZ, funext_iff, Fin.forall_fin_succ]
  · rw [raw_eq_zero_of_not_mem q hq,
      raw_eq_zero_of_not_mem (-q) (by simpa only [modes_neg_closed] using hq), neg_zero]

theorem raw_conjugate (q : Wavevector) : coefficientConjugate (raw q) = raw q := by
  unfold raw
  split_ifs <;> ext i <;> fin_cases i <;> norm_num [coefficientConjugate]

theorem velocity_reality (q : Wavevector) : velocity (-q) = coefficientConjugate (velocity q) := by
  have hs : conj (-unitTorusDerivativePhase⁻¹) = -(-unitTorusDerivativePhase⁻¹) := by
    simp [unitTorusDerivativePhase, mul_inv_rev, map_ofNat]
  ext i
  simp only [velocity, raw_neg, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    coefficientConjugate, map_mul, hs]
  have hr := congrFun (raw_conjugate q) i
  change conj (raw q i) = raw q i at hr
  rw [hr]
  ring

theorem velocity_zero : velocity 0 = 0 := by
  have hz : (0 : Wavevector) ∉ modes := by
    norm_num [modes, lowInput, highInput, companion, axisY, axisZ, funext_iff, Fin.forall_fin_succ]
  simp [velocity, raw_eq_zero_of_not_mem 0 hz]

theorem velocity_eq_zero_of_not_mem (q : Wavevector) (hq : q ∉ modes) : velocity q = 0 := by
  simp [velocity, raw_eq_zero_of_not_mem q hq]

theorem summable_fourierMoment (s : ℕ) : Summable (fourierMoment s velocity) :=
  FourierFiniteSupport.summable_fourierMoment modes velocity velocity_eq_zero_of_not_mem s

theorem curl_velocity (q : Wavevector) :
    fourierCurl velocity q = -coefficientCross (wavevectorCoefficient q) (raw q) := by
  rw [fourierCurl, velocity, coefficientCross_smul_right, smul_smul]
  have hs : unitTorusDerivativePhase * (-unitTorusDerivativePhase⁻¹) = -1 := by
    simp [unitTorusDerivativePhase_ne_zero]
  rw [hs, neg_one_smul]

theorem curlConvection_velocity (k l : Wavevector) :
    curlConvectionAtom velocity k l = (-modeDot (k + l) (raw k)) •
      coefficientCross (wavevectorCoefficient (k + l)) (raw l) := by
  rw [curlConvectionAtom_eq]
  simp only [velocity, modeDot_smul, coefficientCross_smul_right, smul_smul]
  congr 1
  field_simp [unitTorusDerivativePhase_ne_zero]

theorem inner_tests :
    interactionTest true velocity lowInput highInput (-highInput) companion target = 4 / 3 ∧
    interactionTest true velocity lowInput (-highInput) highInput companion target = -(4 / 3) := by
  constructor <;> rw [interactionTest_eq_coefficients]
  all_goals
    simp only [interactionTensor, insertionTensor, ↓reduceIte, curlConvection_velocity, curl_velocity]
    norm_num [projectedCoeff, contraction, tensorCoeff, pairCross, curl_velocity,
      outputFrequency, target, tripleFrequency,
      differenceCLM_apply, differenceCLM, lerayLinear, lerayMode, modeDot, modeSquare,
      lowInput, highInput, companion, axisY, axisZ, raw, coefficientCross, wavevectorCoefficient,
      Fin.sum_univ_three, funext_iff, Fin.forall_fin_succ, Matrix.cons_val_two,
      Complex.mul_re, Complex.mul_im]

def viscosity : ℝ := ((2 * Real.pi) ^ 2)⁻¹

theorem viscosity_pos : 0 < viscosity := by unfold viscosity; positivity

theorem modeDamping_viscosity (q : Wavevector) :
    modeDamping viscosity q = ∑ i : Fin 3, (q i : ℝ) ^ 2 := by
  rw [modeDamping, viscosity, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 2 ≠ 0),
    one_mul, norm_frequencyVec_sq]

theorem remaining_damping :
    remainingDamping viscosity (-highInput) companion target = 25 ∧
    remainingDamping viscosity highInput companion target = 25 := by
  norm_num [remainingDamping, pairDamping, interactionDamping, modeDamping_viscosity,
    target, lowInput, highInput, companion, axisY, axisZ, Fin.sum_univ_three, Matrix.cons_val_two]

theorem center_and_shifts :
    totalDamping viscosity lowInput highInput (-highInput) companion target = 46 ∧
    outputShift viscosity lowInput highInput = 4 ∧
    outputShift viscosity lowInput (-highInput) = -4 := by
  norm_num [totalDamping, remainingDamping, pairDamping, interactionDamping,
    outputShift, rateDefect, modeDamping_viscosity, target,
    lowInput, highInput, companion, axisY, axisZ, Fin.sum_univ_three, Matrix.cons_val_two]

theorem separated_inputs :
    ‖frequencyVec lowInput‖ ≤ ‖frequencyVec highInput‖ / 4 ∧
    ‖frequencyVec lowInput‖ ≤ ‖frequencyVec (-highInput)‖ / 4 := by
  have hk : ‖frequencyVec lowInput‖ ^ 2 = 1 := (norm_frequencyVec_sq lowInput).trans (by
    norm_num [lowInput, Fin.sum_univ_three, Matrix.cons_val_two])
  have hl : ‖frequencyVec highInput‖ ^ 2 = 20 := (norm_frequencyVec_sq highInput).trans (by
    norm_num [highInput, Fin.sum_univ_three, Matrix.cons_val_two])
  have hm : ‖frequencyVec (-highInput)‖ ^ 2 = 20 := (norm_frequencyVec_sq (-highInput)).trans (by
    norm_num [highInput, Fin.sum_univ_three, Matrix.cons_val_two])
  have hk1 : ‖frequencyVec lowInput‖ = 1 := by nlinarith [norm_nonneg (frequencyVec lowInput)]
  rw [hk1]
  constructor <;> nlinarith [norm_nonneg (frequencyVec highInput),
    norm_nonneg (frequencyVec (-highInput))]

theorem integrated_inner_pair :
    (∫ σ : ℝ in Set.Ioi 0,
      heatInteraction true viscosity σ velocity lowInput highInput (-highInput) companion target) +
    (∫ σ : ℝ in Set.Ioi 0,
      heatInteraction true viscosity σ velocity lowInput (-highInput) highInput companion target) =
      -(8 / 1575) := by
  rw [integral_heatInteraction_eq_defect true viscosity_pos.le _ _ _ _ _ _
      (by rw [remaining_damping.1]; norm_num),
    integral_heatInteraction_eq_defect true viscosity_pos.le _ _ _ _ _ _
      (by rw [remaining_damping.2]; norm_num),
    ← totalDamping_exchange viscosity lowInput highInput (-highInput) companion target,
    center_and_shifts.1, center_and_shifts.2.1, center_and_shifts.2.2, inner_tests.1, inner_tests.2]
  norm_num [Mettapedia.Analysis.BalancedResolvent.defect]

/-- No multiplier on the common-test sum can pay this genuine coefficient pair. -/
theorem not_common_test_bound (C : ℝ) :
    ¬ |(∫ σ : ℝ in Set.Ioi 0,
        heatInteraction true viscosity σ velocity lowInput highInput (-highInput) companion target) +
      (∫ σ : ℝ in Set.Ioi 0,
        heatInteraction true viscosity σ velocity lowInput (-highInput) highInput companion target)| ≤
      C * |interactionTest true velocity lowInput highInput (-highInput) companion target +
        interactionTest true velocity lowInput (-highInput) highInput companion target| := by
  rw [integrated_inner_pair, inner_tests.1, inner_tests.2]
  norm_num

theorem neg_velocity_transverse (q : Wavevector) : modeDot q ((-velocity) q) = 0 := by
  change modeDot q (-velocity q) = 0
  simp only [modeDot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  change -(modeDot q (velocity q)) = 0
  rw [velocity_transverse, neg_zero]

theorem neg_velocity_reality (q : Wavevector) :
    (-velocity) (-q) = coefficientConjugate ((-velocity) q) := by
  simp only [Pi.neg_apply, coefficientConjugate_neg, velocity_reality]

theorem positive_integrated_inner_pair :
    (∫ σ : ℝ in Set.Ioi 0,
      heatInteraction true viscosity σ (-velocity) lowInput highInput (-highInput) companion target) +
    (∫ σ : ℝ in Set.Ioi 0,
      heatInteraction true viscosity σ (-velocity) lowInput (-highInput) highInput companion target) =
      8 / 1575 := by
  simp only [heatInteraction_neg, integral_neg]
  linarith [integrated_inner_pair]

/-- The same failure holds for a signed upper bound, not only for its absolute value. -/
theorem not_upper_common_test_bound (C : ℝ) :
    ¬ ((∫ σ : ℝ in Set.Ioi 0,
        heatInteraction true viscosity σ (-velocity) lowInput highInput (-highInput) companion target) +
      (∫ σ : ℝ in Set.Ioi 0,
        heatInteraction true viscosity σ (-velocity) lowInput (-highInput) highInput companion target)) ≤
      C * |interactionTest true (-velocity) lowInput highInput (-highInput) companion target +
        interactionTest true (-velocity) lowInput (-highInput) highInput companion target| := by
  rw [positive_integrated_inner_pair, interactionTest_neg, interactionTest_neg, inner_tests.1, inner_tests.2]
  norm_num

/-- The positive pair occurs at the initial time of an actual unforced NS solution. -/
theorem exists_local_positive_pair :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : PancakeLocalInfiniteVelocity.LocalInfiniteVelocitySolution viscosity (-velocity) T B,
        (∫ σ : ℝ in Set.Ioi 0,
          heatInteraction true viscosity σ (s.coefficients 0)
            lowInput highInput (-highInput) companion target) +
        (∫ σ : ℝ in Set.Ioi 0,
          heatInteraction true viscosity σ (s.coefficients 0)
            lowInput (-highInput) highInput companion target) = 8 / 1575 ∧
        interactionTest true (s.coefficients 0) lowInput highInput (-highInput) companion target +
          interactionTest true (s.coefficients 0) lowInput (-highInput) highInput companion target = 0 := by
  obtain ⟨T, hT, B, hB, s, _⟩ := FourierFiniteLocalSolution.exists_localMomentEnvelope
    modes (-velocity) (fun q hq ↦ by simp [velocity_eq_zero_of_not_mem q hq])
    modes_neg_closed neg_velocity_reality neg_velocity_transverse
    (by simp [velocity_zero]) viscosity viscosity_pos 3
  refine ⟨T, hT, B, hB, s, ?_, ?_⟩
  · rw [s.initial]
    exact positive_integrated_inner_pair
  · rw [s.initial, interactionTest_neg, interactionTest_neg, inner_tests.1, inner_tests.2]
    ring

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAntisymmetricWitness
