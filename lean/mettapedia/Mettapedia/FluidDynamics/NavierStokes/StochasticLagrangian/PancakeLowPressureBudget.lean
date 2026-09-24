import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierPressureStrain

/-!
# Low-output pressure from kinetic energy

Incompressibility transfers both pressure derivatives to the output mode.
The convolution fiber contains each source and receiver at most once, so
its amplitude is bounded by kinetic energy with no source-cardinality loss.
Low-output pressure Hessians are therefore controlled even when their
inputs have arbitrarily high retained frequencies.

All cutoff dependence is retained explicitly. No uniform bound as the
pressure output cutoff tends to infinity is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLowPressureBudget

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeFourierPressureStrain
open PancakeFrequencyProjectorCommutator PancakeSignedTransportEnergy PancakeIncomingLowSourceEnergy
open PancakeViscousMisalignmentAbsorption

def interactionPairs (modes : Finset Wavevector) (q : Wavevector) :
    Finset (Wavevector × Wavevector) := (modes ×ˢ modes).filter (fun p ↦ p.1 + p.2 = q)

theorem convectionConvolution_eq_pairSum (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    convectionConvolution modes u q =
      ∑ p ∈ interactionPairs modes q, orderedConvection p.1 p.2 u := by
  simp [interactionPairs, Finset.sum_filter, Finset.sum_product, convectionConvolution]

theorem modeDot_sum {ι : Type*} (s : Finset ι) (q : Wavevector)
    (f : ι → VelocityCoefficient) : modeDot q (∑ i ∈ s, f i) = ∑ i ∈ s, modeDot q (f i) := by
  simp only [modeDot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Both dot products in the pressure numerator use the output frequency.
This is the cancellation that avoids a high-input derivative loss. -/
theorem pressure_numerator_output_pair (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    modeDot q (convectionConvolution modes u q) =
      ∑ p ∈ interactionPairs modes q, modeDot q (u p.1) * modeDot q (u p.2) := by
  rw [convectionConvolution_eq_pairSum, modeDot_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := Finset.mem_filter.mp hp
  have hfirst := (Finset.mem_product.mp hm.1).1
  have hd : modeDot q (u p.1) = modeDot p.2 (u p.1) := by
    rw [← hm.2, modeDot_add_wavevector, hu p.1 hfirst, zero_add]
  rw [orderedConvection, modeDot_smul, hd]

theorem sum_pair_first_energy_le (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    (∑ p ∈ interactionPairs modes q, coefficientEnergy (u p.1)) ≤ fullEnergy modes u := by
  classical
  have hinj : Set.InjOn Prod.fst (interactionPairs modes q : Set (Wavevector × Wavevector)) := by
    intro p hp r hr he
    have hpq := (Finset.mem_filter.mp hp).2
    have hrq := (Finset.mem_filter.mp hr).2
    apply Prod.ext he
    rw [he] at hpq
    exact add_left_cancel (hpq.trans hrq.symm)
  have hsub : (interactionPairs modes q).image Prod.fst ⊆ modes := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have him : (∑ k ∈ (interactionPairs modes q).image Prod.fst, coefficientEnergy (u k)) =
      ∑ p ∈ interactionPairs modes q, coefficientEnergy (u p.1) := Finset.sum_image hinj
  rw [← him]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ ↦ by rw [← norm_coefficientVec_sq]; positivity)

theorem sum_pair_second_energy_le (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    (∑ p ∈ interactionPairs modes q, coefficientEnergy (u p.2)) ≤ fullEnergy modes u := by
  have he : (∑ p ∈ interactionPairs modes q, coefficientEnergy (u p.2)) =
      ∑ p ∈ interactionPairs modes q, coefficientEnergy (u p.1) := by
    apply Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector)
    · intro p
      simp [interactionPairs, add_comm, and_comm]
    · intros
      rfl
  rw [he]
  exact sum_pair_first_energy_le modes u q

/-- A convolution fiber is bounded by the full kinetic energy, without
counting the source support. -/
theorem sum_pair_norm_product_le_energy (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    (∑ p ∈ interactionPairs modes q,
      ‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖) ≤ fullEnergy modes u := by
  have hp := Finset.sum_le_sum (s := interactionPairs modes q)
    (f := fun p ↦ 2 * (‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖))
    (g := fun p ↦ coefficientEnergy (u p.1) + coefficientEnergy (u p.2)) (by
      intro p _
      rw [← norm_coefficientVec_sq, ← norm_coefficientVec_sq]
      nlinarith [sq_nonneg (‖coefficientVec (u p.1)‖ - ‖coefficientVec (u p.2)‖)])
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hp
  linarith [sum_pair_first_energy_le modes u q, sum_pair_second_energy_le modes u q]

theorem norm_modeDot_le (q : Wavevector) (v : VelocityCoefficient) :
    ‖modeDot q v‖ ≤ ‖frequencyVec q‖ * ‖coefficientVec v‖ := by
  rw [← inner_frequencyVec]
  exact norm_inner_le_norm _ _

theorem norm_pressure_numerator_le (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    ‖modeDot q (convectionConvolution modes u q)‖ ≤
      ‖frequencyVec q‖ ^ 2 * fullEnergy modes u := by
  rw [pressure_numerator_output_pair modes u q hu]
  calc
    _ ≤ ∑ p ∈ interactionPairs modes q, ‖modeDot q (u p.1) * modeDot q (u p.2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ interactionPairs modes q,
        ‖frequencyVec q‖ ^ 2 * (‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul]
      calc
        _ ≤ (‖frequencyVec q‖ * ‖coefficientVec (u p.1)‖) *
            (‖frequencyVec q‖ * ‖coefficientVec (u p.2)‖) := by
          gcongr <;> exact norm_modeDot_le q _
        _ = _ := by ring
    _ = ‖frequencyVec q‖ ^ 2 * (∑ p ∈ interactionPairs modes q,
        ‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pair_norm_product_le_energy modes u q) (sq_nonneg _)

/-- Every physical pressure coefficient is bounded by kinetic energy.
The constant is exactly one and is independent of all retained frequencies. -/
theorem norm_pressureCoeff_le_kineticEnergy (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    ‖pressureCoeff modes u q‖ ≤ fullEnergy modes u := by
  by_cases hq : q = 0
  · subst q
    rw [pressureCoeff_zero, norm_zero]
    exact fullEnergy_nonneg _ _
  · have hf := norm_pos_iff.mpr (frequencyVec_ne_zero hq)
    have hp := congrArg norm (pressureCoeff_poisson modes u q)
    rw [norm_mul, norm_neg, norm_modeSquare] at hp
    have hn := norm_pressure_numerator_le modes u q hu
    rw [← hp] at hn
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hf)).mp hn

local notation "C3" => EuclideanSpace ℂ (Fin 3)

/-- The physical pressure-Hessian coefficient as an operator on amplitudes. -/
def pressureHessianOperator (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) : C3 →L[ℂ] C3 :=
  (unitTorusDerivativePhase ^ 2 * pressureCoeff modes u q) •
    InnerProductSpace.rankOne ℂ (frequencyVec q) (frequencyVec q)

theorem pressureHessianOperator_apply (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (v : VelocityCoefficient) (i : Fin 3) :
    pressureHessianOperator modes u q (coefficientVec v) i =
      ∑ j : Fin 3, pressureHessianCoeff modes u q i j * v j := by
  simp only [pressureHessianOperator, smul_apply, InnerProductSpace.rankOne_apply,
    inner_frequencyVec]
  change (unitTorusDerivativePhase ^ 2 * pressureCoeff modes u q) *
    (modeDot q v * (q i : ℂ)) = _
  simp only [pressureHessianCoeff, modeDot, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_pressureHessianOperator (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    ‖pressureHessianOperator modes u q‖ =
      (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * ‖pressureCoeff modes u q‖ := by
  simp only [pressureHessianOperator, norm_smul, norm_mul, norm_pow,
    norm_derivativePhase, InnerProductSpace.norm_rankOne]
  ring

theorem norm_pressureHessianOperator_le (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    ‖pressureHessianOperator modes u q‖ ≤
      (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * fullEnergy modes u := by
  rw [norm_pressureHessianOperator]
  exact mul_le_mul_of_nonneg_left (norm_pressureCoeff_le_kineticEnergy modes u q hu)
    (by positivity)

def pressureHessianAmplitude (outputs modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∑ q ∈ outputs, ‖pressureHessianOperator modes u q‖

def pressureCutoffWeight (outputs : Finset Wavevector) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ q ∈ outputs, ‖frequencyVec q‖ ^ 2

theorem pressureCutoffWeight_nonneg (outputs : Finset Wavevector) :
    0 ≤ pressureCutoffWeight outputs := by unfold pressureCutoffWeight; positivity

theorem pressureHessianAmplitude_le_kineticEnergy (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    pressureHessianAmplitude outputs modes u ≤ pressureCutoffWeight outputs * fullEnergy modes u := by
  calc
    _ ≤ ∑ q ∈ outputs, (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * fullEnergy modes u :=
      Finset.sum_le_sum (fun q _ ↦ norm_pressureHessianOperator_le modes u q hu)
    _ = _ := by simp [pressureCutoffWeight, Finset.mul_sum, Finset.sum_mul]

/-- The reconstructed low-output pressure Hessian; all source frequencies
of the physical pressure remain in its coefficients. -/
def pressureHessianField (outputs modes : Finset Wavevector) (u : FourierVelocity)
    (x : UnitAddTorus (Fin 3)) : C3 →L[ℂ] C3 :=
  ∑ q ∈ outputs, UnitAddTorus.mFourier q x • pressureHessianOperator modes u q

theorem norm_pressureHessianField_le_amplitude (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (x : UnitAddTorus (Fin 3)) :
    ‖pressureHessianField outputs modes u x‖ ≤ pressureHessianAmplitude outputs modes u := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_smul]
  have h := (UnitAddTorus.mFourier q).norm_coe_le_norm x
  rw [UnitAddTorus.mFourier_norm] at h
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (one_mul _)

/-- Spatially uniform low-pressure bound, independent of source cutoff and
source cardinality. The displayed output weight is not discarded. -/
theorem norm_pressureHessianField_le_kineticEnergy (outputs modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ k ∈ modes, modeDot k (u k) = 0)
    (x : UnitAddTorus (Fin 3)) :
    ‖pressureHessianField outputs modes u x‖ ≤ pressureCutoffWeight outputs * fullEnergy modes u :=
  (norm_pressureHessianField_le_amplitude outputs modes u x).trans
    (pressureHessianAmplitude_le_kineticEnergy outputs modes u hu)

theorem continuousOn_pressureCoeff (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (q : Wavevector) (domain : Set ℝ)
    (hu : ∀ k ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t k i) domain) :
    ContinuousOn (fun t ↦ pressureCoeff modes (u t) q) domain := by
  unfold pressureCoeff
  apply ContinuousOn.div_const
  apply ContinuousOn.neg
  unfold modeDot
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_const.mul
  simp only [convectionConvolution, Finset.sum_apply]
  apply continuousOn_finsetSum
  intro k hk
  apply continuousOn_finsetSum
  intro l hl
  by_cases hkl : k + l = q
  · simp only [hkl, ite_true, orderedConvection, Pi.smul_apply, smul_eq_mul]
    apply ContinuousOn.mul _ (hu l hl i)
    unfold modeDot
    apply continuousOn_finsetSum
    intro j _
    exact continuousOn_const.mul (hu k hk j)
  · simp only [hkl, ite_false, Pi.zero_apply]
    exact continuousOn_const

theorem continuousOn_pressureHessianAmplitude (outputs modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (domain : Set ℝ)
    (hu : ∀ k ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t k i) domain) :
    ContinuousOn (fun t ↦ pressureHessianAmplitude outputs modes (u t)) domain := by
  unfold pressureHessianAmplitude
  apply continuousOn_finsetSum
  intro q _
  simp_rw [norm_pressureHessianOperator]
  exact continuousOn_const.mul (continuousOn_pressureCoeff modes u q domain hu).norm

def lowPressureCost (outputs modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * pressureHessianAmplitude outputs modes u * fullEnergy modes (fourierCurl u)

/-- A sufficient pressure-anisotropy envelope times receiver enstrophy. -/
theorem lowPressureCost_le (outputs modes : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    lowPressureCost outputs modes u ≤
      2 * pressureCutoffWeight outputs * fullEnergy modes u * fullEnergy modes (fourierCurl u) := by
  unfold lowPressureCost
  have h := pressureHessianAmplitude_le_kineticEnergy outputs modes u hu
  have he := fullEnergy_nonneg modes (fourierCurl u)
  nlinarith

/-- The low-output pressure cost is paid by the actual physical velocity
energy identity. No pressure regularity or separate enstrophy budget is an
input. The output cutoff weight remains explicit. -/
theorem lowPressureCost_integral_of_velocityRHS
    (outputs modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ)
    (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = PancakeBlockReality.coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, lowPressureCost outputs modes (u t)) ≤
      pressureCutoffWeight outputs * fullEnergy modes (u 0) ^ 2 / nu := by
  have hc := continuousOn_coefficients_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hP := continuousOn_pressureHessianAmplitude outputs modes u (Set.Icc 0 T) hc
  have hO := continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hCI : IntervalIntegrable (fun t ↦ lowPressureCost outputs modes (u t))
      MeasureTheory.volume 0 T := ContinuousOn.intervalIntegrable_of_Icc hT
    ((continuousOn_const.mul hP).mul hO)
  have hOI : IntervalIntegrable (fun t ↦ fullEnergy modes (fourierCurl (u t)))
      MeasureTheory.volume 0 T := ContinuousOn.intervalIntegrable_of_Icc hT hO
  have hU := kineticEnergy_le_initial_on modes u nu T hnu.le hs hr hu he
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) T, lowPressureCost outputs modes (u t) ≤
      (2 * pressureCutoffWeight outputs * fullEnergy modes (u 0)) *
        fullEnergy modes (fourierCurl (u t)) := by
    intro t ht
    apply (lowPressureCost_le outputs modes (u t) (hu t ht)).trans
    gcongr
    · exact fullEnergy_nonneg _ _
    · exact mul_nonneg (by norm_num) (pressureCutoffWeight_nonneg outputs)
    · exact hU t ht
  have hm := intervalIntegral.integral_mono_on hT hCI (hOI.const_mul _) hp
  rw [intervalIntegral.integral_const_mul] at hm
  have hE := enstrophy_integral_le_initial modes u nu T hT hs hr hu he
  have hU0 := fullEnergy_nonneg modes (u 0)
  have hC0 := pressureCutoffWeight_nonneg outputs
  apply hm.trans
  apply (le_div_iff₀ hnu).mpr
  have := mul_le_mul_of_nonneg_left hE (mul_nonneg hC0 hU0)
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeLowPressureBudget
