import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalPressureEquation

/-!
# The actual Hessian of the infinite pressure

A second input moment also pays an output derivative of convection.
Consequently the pressure has ordinary continuous mixed second derivatives.
The bounds use the same local envelope as the velocity-pressure equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressureHessian

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteVelocityEnvelope PancakeSobolevFiberEnvelope PancakeCoefficientLimitEquation
open PancakeCurlOutputTail PancakeIndexedFourierMoments PancakeLowPressureBudget
open PancakePhysicalSixthDecay PancakeInfinitePressureCoefficients PancakeInfiniteSpatialPressure
open PancakeInfiniteFourierDerivative PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)

theorem norm_frequency_mul_outputFiber_le (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hu : ∀ k, fourierMoment 2 u k ≤ g k)
    (q k : Wavevector) (i : Fin 3) :
    ‖frequencyVec q‖ * ‖outputFiber q u k i‖ ≤ g k * g (q-k) := by
  have hf : ‖frequencyVec q‖ ≤
      (1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q-k)‖) := by
    have hq : q = k + (q-k) := by abel
    conv_lhs => rw [hq, frequencyVec_add]
    nlinarith [norm_add_le (frequencyVec k) (frequencyVec (q-k)),
      mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (frequencyVec (q-k)))]
  calc
    _ ≤ ‖frequencyVec q‖ * (‖frequencyVec q‖ *
        ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [outputFiber, norm_mul]
      exact mul_le_mul (norm_modeDot_le q (u k))
        (PiLp.norm_apply_le (coefficientVec (u (q-k))) i) (norm_nonneg _) (by positivity)
    _ ≤ ((1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q-k)‖)) *
        (((1 + ‖frequencyVec k‖) * (1 + ‖frequencyVec (q-k)‖)) *
          ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖) := by gcongr
    _ = fourierMoment 2 u k * fourierMoment 2 u (q-k) := by
      unfold fourierMoment
      ring
    _ ≤ _ := mul_le_mul (hu k) (hu (q-k)) (fourierMoment_nonneg _ _ _) (hg k)

theorem norm_frequency_mul_infiniteConvection_component_le (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (q : Wavevector) (i : Fin 3) :
    ‖frequencyVec q‖ * ‖infiniteConvection u q i‖ ≤ convolutionEnvelope g q := by
  have hs := (summable_pairEnvelope g hg hSum).prod_factor q
  have hn := hs.of_nonneg_of_le (fun k ↦ norm_nonneg (outputFiber q u k i))
    (fun k ↦ norm_outputFiber_le_momentEnvelope u g hg hu q k i)
  calc
    _ ≤ ‖frequencyVec q‖ * ∑' k, ‖outputFiber q u k i‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn) (norm_nonneg _)
    _ = ∑' k, ‖frequencyVec q‖ * ‖outputFiber q u k i‖ := (tsum_mul_left).symm
    _ ≤ _ := (hn.mul_left _).tsum_le_tsum
      (norm_frequency_mul_outputFiber_le u g hg hu q · i) hs

theorem norm_frequency_mul_infiniteConvection_le (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ k, fourierMoment 2 u k ≤ g k) (q : Wavevector) :
    ‖frequencyVec q‖ * ‖coefficientVec (infiniteConvection u q)‖ ≤
      3 * convolutionEnvelope g q := by
  have h := norm_coefficientVec_le_three
    ((‖frequencyVec q‖ : ℂ) • infiniteConvection u q) _
    (convolutionEnvelope_nonneg g hg q) (fun i ↦ by
      simpa only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using
          norm_frequency_mul_infiniteConvection_component_le u g hg hSum hu q i)
  change ‖(‖frequencyVec q‖ : ℂ) • coefficientVec (infiniteConvection u q)‖ ≤ _ at h
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using h

theorem summable_frequency_norm_infiniteConvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ ‖frequencyVec q‖ * ‖coefficientVec (infiniteConvection u q)‖) :=
  ((summable_convolutionEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).mul_left 3).of_nonneg_of_le (fun _ ↦ by positivity)
      (norm_frequency_mul_infiniteConvection_le u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))

theorem norm_infinitePressureSecondDerivative_le (u : FourierVelocity)
    (i j : Fin 3) (q : Wavevector) :
    ‖indexedDerivativeCoeff id j (indexedDerivativeCoeff id i (infinitePressureCoeff u)) q‖ ≤
      (2 * Real.pi)^2 * (‖frequencyVec q‖ * ‖coefficientVec (infiniteConvection u q)‖) := by
  simp only [indexedDerivativeCoeff, norm_smul, norm_mul, id_eq, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi) * ‖frequencyVec q‖ *
        ((2 * Real.pi) * ‖frequencyVec q‖ * ‖infinitePressureCoeff u q‖) := by
      gcongr <;> exact norm_frequency_coordinate_le _ _
    _ = (2 * Real.pi)^2 * (‖frequencyVec q‖ *
        (‖frequencyVec q‖ * ‖infinitePressureCoeff u q‖)) := by ring
    _ ≤ _ := by
      gcongr
      exact norm_frequency_mul_pressure_le u q

theorem summable_norm_infinitePressureSecondDerivative (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (i j : Fin 3) :
    Summable (fun q ↦
      ‖indexedDerivativeCoeff id j (indexedDerivativeCoeff id i (infinitePressureCoeff u)) q‖) :=
  ((summable_frequency_norm_infiniteConvection u hu).mul_left ((2 * Real.pi)^2)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (norm_infinitePressureSecondDerivative_le u i j)

theorem scalarCoordinateDerivative2_spatialPressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (i j : Fin 3) (x : T3) :
    scalarCoordinateDerivative (fun y ↦ scalarCoordinateDerivative (spatialPressure u) i y) j x =
      fullFourierField id
        (indexedDerivativeCoeff id j (indexedDerivativeCoeff id i (infinitePressureCoeff u))) x := by
  simp only [spatialPressure,
    scalarCoordinateDerivative_fullFourierField _ (summable_norm_infinitePressure u hu) i
      (summable_norm_infinitePressureDerivative u hu i)]
  exact scalarCoordinateDerivative_fullFourierField _
    (summable_norm_infinitePressureDerivative u hu i) j
    (summable_norm_infinitePressureSecondDerivative u hu i j) x

def spatialHessian (f : T3 → ℂ) (x : T3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j ↦ scalarCoordinateDerivative (fun y ↦ scalarCoordinateDerivative f i y) j x

theorem continuous_spatialHessian_pressure (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Continuous (spatialHessian (spatialPressure u)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun x ↦
    scalarCoordinateDerivative (fun y ↦ scalarCoordinateDerivative (spatialPressure u) i y) j x)
  simp only [scalarCoordinateDerivative2_spatialPressure u hu]
  exact (fullFourierField id _).continuous

theorem spatialHessian_pressure_symmetric (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (x : T3) :
    (spatialHessian (spatialPressure u) x).transpose = spatialHessian (spatialPressure u) x := by
  ext i j
  simp only [Matrix.transpose_apply, spatialHessian, scalarCoordinateDerivative2_spatialPressure u hu]
  congr 2
  funext q
  simp only [indexedDerivativeCoeff, smul_eq_mul]
  ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfinitePressureHessian
