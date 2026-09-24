import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity

/-!
# Summable all-output velocity envelopes

A common second absolute Fourier moment controls the entire infinite
velocity RHS. Convection is paid by the discrete convolution of the
summable envelope, and viscosity by the envelope itself.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteVelocityEnvelope

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeSobolevFiberEnvelope PancakeCoefficientLimitEquation
open PancakeFixedOutputVelocityBound PancakeLowPressureBudget PancakeIndexedFourierMoments
open PancakePhysicalSixthDecay PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy

def convolutionEnvelope (g : Wavevector → ℝ) (q : Wavevector) : ℝ :=
  ∑' k, g k * g (q-k)

theorem summable_pairEnvelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) :
    Summable (fun p : Wavevector × Wavevector ↦ g p.2 * g (p.1-p.2)) := by
  apply (hSum.mul_of_nonneg hSum hg hg).comp_injective
    (i := fun p : Wavevector × Wavevector ↦ (p.2, p.1-p.2))
  rintro ⟨q, k⟩ ⟨r, l⟩ h
  have hkl : k = l := congrArg Prod.fst h
  have hqr : q-k = r-l := congrArg Prod.snd h
  subst l
  have hqr' : q = r := sub_left_inj.mp hqr
  subst r
  rfl

theorem summable_convolutionEnvelope (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) : Summable (convolutionEnvelope g) :=
  (summable_pairEnvelope g hg hSum).prod

theorem convolutionEnvelope_nonneg (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (q : Wavevector) : 0 ≤ convolutionEnvelope g q :=
  tsum_nonneg (fun k ↦ mul_nonneg (hg k) (hg (q-k)))

theorem norm_outputFiber_le_momentEnvelope (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (q k : Wavevector) (i : Fin 3) :
    ‖outputFiber q u k i‖ ≤ g k * g (q-k) := by
  have hf : ‖frequencyVec q‖ ≤
      (1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q-k)‖) := by
    have hq : q = k + (q-k) := by abel
    conv_lhs => rw [hq, frequencyVec_add]
    nlinarith [norm_add_le (frequencyVec k) (frequencyVec (q-k)),
      mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (frequencyVec (q-k)))]
  calc
    _ ≤ ‖frequencyVec q‖ * ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖ := by
      rw [outputFiber, norm_mul]
      exact mul_le_mul (norm_modeDot_le q (u k))
        (PiLp.norm_apply_le (coefficientVec (u (q-k))) i) (norm_nonneg _) (by positivity)
    _ ≤ ((1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q-k)‖)) *
        ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖ := by gcongr
    _ = fourierMoment 1 u k * fourierMoment 1 u (q-k) := by
      simp only [fourierMoment, pow_one]
      ring
    _ ≤ _ := mul_le_mul ((firstMoment_le_second u k).trans (hu k))
      ((firstMoment_le_second u (q-k)).trans (hu (q-k))) (fourierMoment_nonneg _ _ _) (hg k)

theorem norm_infiniteConvection_component_le (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hSum : Summable g) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (q : Wavevector) (i : Fin 3) :
    ‖infiniteConvection u q i‖ ≤ convolutionEnvelope g q := by
  have hs := (summable_pairEnvelope g hg hSum).prod_factor q
  have hn := hs.of_nonneg_of_le (fun k ↦ norm_nonneg (outputFiber q u k i))
    (fun k ↦ norm_outputFiber_le_momentEnvelope u g hg hu q k i)
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum
    (fun k ↦ norm_outputFiber_le_momentEnvelope u g hg hu q k i) hs)

theorem norm_infiniteConvection_le (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hSum : Summable g) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (q : Wavevector) :
    ‖coefficientVec (infiniteConvection u q)‖ ≤ 3 * convolutionEnvelope g q :=
  norm_coefficientVec_le_three _ _ (convolutionEnvelope_nonneg g hg q)
    (norm_infiniteConvection_component_le u g hg hSum hu q)

def velocityEnvelope (nu : ℝ) (g : Wavevector → ℝ) (q : Wavevector) : ℝ :=
  3 * (2 * Real.pi) * convolutionEnvelope g q + |nu| * (2 * Real.pi)^2 * g q

theorem velocityEnvelope_nonneg (nu : ℝ) (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (q : Wavevector) : 0 ≤ velocityEnvelope nu g q := by
  unfold velocityEnvelope
  positivity [convolutionEnvelope_nonneg g hg q, hg q]

theorem summable_velocityEnvelope (nu : ℝ) (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hSum : Summable g) : Summable (velocityEnvelope nu g) :=
  ((summable_convolutionEnvelope g hg hSum).mul_left (3 * (2 * Real.pi))).add
    (hSum.mul_left (|nu| * (2 * Real.pi)^2))

theorem norm_infiniteVelocityRHS_le (nu : ℝ) (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hSum : Summable g) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (q : Wavevector) :
    ‖coefficientVec (infiniteVelocityRHS nu u q)‖ ≤ velocityEnvelope nu g q := by
  change ‖coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q)) +
    coefficientVec (unitTorusViscousVorticityCoeff nu u q)‖ ≤ _
  apply (norm_add_le _ _).trans
  unfold velocityEnvelope
  apply add_le_add
  · apply (norm_lerayMode_le q _).trans
    change ‖(-unitTorusDerivativePhase) • coefficientVec (infiniteConvection u q)‖ ≤ _
    rw [norm_smul, norm_neg, norm_derivativePhase]
    calc
      _ ≤ (2 * Real.pi) * (3 * convolutionEnvelope g q) :=
        mul_le_mul_of_nonneg_left (norm_infiniteConvection_le u g hg hSum hu q) (by positivity)
      _ = _ := by ring
  · rw [norm_viscousCoefficient]
    have hr : ‖frequencyVec q‖^2 * ‖coefficientVec (u q)‖ ≤ fourierMoment 2 u q := by
      unfold fourierMoment
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hr.trans (hu q)) (by positivity : 0 ≤ |nu| * (2 * Real.pi)^2)

theorem summable_norm_infiniteVelocityRHS (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) :
    Summable (fun q ↦ ‖infiniteVelocityRHS nu u q‖) :=
  (summable_velocityEnvelope nu g hg hSum).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun q ↦ (norm_coefficient_sup_le_euclidean _).trans
      (norm_infiniteVelocityRHS_le nu u g hg hSum hu q))

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteVelocityEnvelope
