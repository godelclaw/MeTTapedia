import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteConvectionEnergy

/-!
# Kinetic cancellation for the actual infinite convection

The velocity transport matrix is skew-Hermitian by reality and
incompressibility. An absolute first Fourier moment justifies the double
sum and its exchange; cancellation is performed before any energy estimate.
No closed evolution of a finite truncation is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteKineticCancellation

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeSignedTransportEnergy
open PancakeBlockReality PancakeCurlOutputTail PancakeLowPressureBudget
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope PancakeIndexedFourierMoments
open PancakeIncomingLowSourceEnergy
open InfiniteConvectionEnergy

/-- All-input negative advection written with the advected mode as index. -/
def transportMatrix (u : FourierVelocity) (q l : Wavevector) : ℂ :=
  -unitTorusDerivativePhase * modeDot l (u (q-l))

theorem transportMatrix_skew (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (q l : Wavevector) :
    transportMatrix u l q = -conj (transportMatrix u q l) := by
  have hn : l-q = -(q-l) := by abel
  have he : modeDot q (u (q-l)) = modeDot l (u (q-l)) := by
    have h := hd (q-l)
    rw [modeDot_sub_left, sub_eq_zero] at h
    exact h
  simp only [transportMatrix, hn, hr, modeDot_conjugate, he]
  simp [unitTorusDerivativePhase, map_ofNat]

def transportFlux (u : FourierVelocity) (q l : Wavevector) : ℝ :=
  (coefficientHermitian (u q) (transportMatrix u q l • u l)).re

theorem transportFlux_antisymmetric (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (q l : Wavevector) :
    transportFlux u l q = -transportFlux u q l := by
  unfold transportFlux
  rw [transportMatrix_skew u hr hd]
  exact hermitian_neg_conj_smul_swap _ _ _

theorem amplitude_le_firstMoment (u : FourierVelocity) (q : Wavevector) :
    ‖coefficientVec (u q)‖ ≤ fourierMoment 1 u q := by
  simp only [fourierMoment, pow_one]
  nlinarith [norm_nonneg (frequencyVec q), norm_nonneg (coefficientVec (u q))]

theorem summable_amplitude (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun q ↦ ‖coefficientVec (u q)‖) :=
  hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (amplitude_le_firstMoment u)

def amplitudeMass (u : FourierVelocity) : ℝ := ∑' q, ‖coefficientVec (u q)‖

theorem amplitudeMass_nonneg (u : FourierVelocity) : 0 ≤ amplitudeMass u :=
  tsum_nonneg (fun _ ↦ norm_nonneg _)

theorem amplitude_le_mass (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (q : Wavevector) : ‖coefficientVec (u q)‖ ≤ amplitudeMass u :=
  (summable_amplitude u hu).le_tsum q (fun _ _ ↦ norm_nonneg _)

theorem norm_transportCoefficient_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (q l : Wavevector) :
    ‖coefficientVec (transportMatrix u q l • u l)‖ ≤
      (2 * Real.pi) * amplitudeMass u * fourierMoment 1 u l := by
  change ‖transportMatrix u q l • coefficientVec (u l)‖ ≤ _
  rw [norm_smul, transportMatrix, norm_mul, norm_neg, norm_derivativePhase]
  calc
    _ ≤ ((2 * Real.pi) * (‖frequencyVec l‖ * amplitudeMass u)) * ‖coefficientVec (u l)‖ := by
      gcongr
      exact (norm_modeDot_le l _).trans
        (mul_le_mul_of_nonneg_left (amplitude_le_mass u hu (q-l)) (norm_nonneg _))
    _ ≤ _ := by
      simp only [fourierMoment, pow_one]
      nlinarith [mul_nonneg (amplitudeMass_nonneg u) (norm_nonneg (coefficientVec (u l))),
        Real.pi_pos]

theorem summable_transportCoefficient (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (q : Wavevector) :
    Summable (fun l ↦ transportMatrix u q l • u l) :=
  (hu.mul_left ((2 * Real.pi) * amplitudeMass u)).of_norm_bounded
    (fun l ↦ (norm_coefficient_sup_le_euclidean _).trans (norm_transportCoefficient_le u hu q l))

theorem abs_transportFlux_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (q l : Wavevector) :
    |transportFlux u q l| ≤ ((2 * Real.pi) * amplitudeMass u) *
      (‖coefficientVec (u q)‖ * fourierMoment 1 u l) := by
  apply (abs_hermitian_re_le _ _).trans
  calc
    _ ≤ ‖coefficientVec (u q)‖ *
        ((2 * Real.pi) * amplitudeMass u * fourierMoment 1 u l) :=
      mul_le_mul_of_nonneg_left (norm_transportCoefficient_le u hu q l) (norm_nonneg _)
    _ = _ := by ring

theorem summable_transportFlux (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Summable (fun p : Wavevector × Wavevector ↦ transportFlux u p.1 p.2) := by
  apply (((summable_amplitude u hu).mul_of_nonneg hu
    (fun _ ↦ norm_nonneg _) (fourierMoment_nonneg _ _)).mul_left
      ((2 * Real.pi) * amplitudeMass u)).of_norm_bounded
  intro p
  exact abs_transportFlux_le u hu p.1 p.2

/-- Absolute convergence permits exchange of the two energy slots. -/
theorem tsum_transportFlux_zero (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) : (∑' q, ∑' l, transportFlux u q l) = 0 := by
  have hs := summable_transportFlux u hu
  have he : (∑' p : Wavevector × Wavevector, transportFlux u p.1 p.2) =
      -(∑' p : Wavevector × Wavevector, transportFlux u p.1 p.2) := by
    calc
      _ = ∑' p : Wavevector × Wavevector, transportFlux u p.2 p.1 :=
        ((Equiv.prodComm Wavevector Wavevector).tsum_eq _).symm
      _ = _ := by
        rw [← tsum_neg]
        exact tsum_congr (fun p ↦ transportFlux_antisymmetric u hr hd p.1 p.2)
  rw [← hs.tsum_prod]
  linarith

private def outputComplement (q : Wavevector) : Wavevector ≃ Wavevector where
  toFun k := q-k
  invFun k := q-k
  left_inv k := by ext i; simp only [Pi.sub_apply]; ring
  right_inv k := by ext i; simp only [Pi.sub_apply]; ring

theorem negative_infiniteConvection_eq_transportSum (u : FourierVelocity)
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) :
    (-unitTorusDerivativePhase) • infiniteConvection u q =
      fun i ↦ ∑' l, (transportMatrix u q l • u l) i := by
  ext i
  simp only [infiniteConvection, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  rw [← (outputComplement q).tsum_eq]
  apply tsum_congr
  intro l
  have he : q-(q-l) = l := by ext j; simp only [Pi.sub_apply]; ring
  have hdq : modeDot q (u (q-l)) = modeDot l (u (q-l)) := by
    have h := hd (q-l)
    rw [modeDot_sub_left, sub_eq_zero] at h
    exact h
  change -unitTorusDerivativePhase * outputFiber q u (q-l) i = _
  simp only [outputFiber, he, hdq, transportMatrix, mul_assoc]

theorem coefficientHermitian_tsum_right {ι : Type*} (v : VelocityCoefficient)
    (w : ι → VelocityCoefficient) (hw : Summable w) :
    coefficientHermitian v (fun i ↦ ∑' k, w k i) = ∑' k, coefficientHermitian v (w k) := by
  simp only [coefficientHermitian, ← tsum_mul_left]
  exact (Summable.tsum_finsetSum
    (fun i _ ↦ (Pi.summable.mp hw i).mul_left (conj (v i)))).symm

theorem real_hermitian_negativeConvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) :
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • infiniteConvection u q)).re =
      ∑' l, transportFlux u q l := by
  have hc : Summable (fun l ↦ coefficientHermitian (u q) (transportMatrix u q l • u l)) := by
    change Summable (fun l ↦ ∑ i : Fin 3, conj (u q i) * (transportMatrix u q l • u l) i)
    exact summable_sum
      (fun i _ ↦ (Pi.summable.mp (summable_transportCoefficient u hu q) i).mul_left (conj (u q i)))
  rw [negative_infiniteConvection_eq_transportSum u hd q,
    coefficientHermitian_tsum_right _ _ (summable_transportCoefficient u hu q)]
  rw [Complex.re_tsum hc]
  rfl

/-- The convection of the actual infinite equation does no kinetic work. -/
theorem infiniteConvection_kinetic_cancellation (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    (∑' q, (coefficientHermitian (u q)
      ((-unitTorusDerivativePhase) • infiniteConvection u q)).re) = 0 := by
  simp_rw [real_hermitian_negativeConvection u hu hd]
  exact tsum_transportFlux_zero u hu hr hd

theorem summable_coefficientEnergy (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖coefficientVec (u q)‖)) :
    Summable (fun q ↦ coefficientEnergy (u q)) := by
  apply (hu.mul_left (amplitudeMass u)).of_nonneg_of_le
    (fun q ↦ by rw [← norm_coefficientVec_sq]; positivity)
  intro q
  rw [← norm_coefficientVec_sq, pow_two]
  exact mul_le_mul_of_nonneg_right (hu.le_tsum q (fun _ _ ↦ norm_nonneg _)) (norm_nonneg _)

theorem kineticEnergy_eq_tsum_coefficientEnergy (u : FourierVelocity) :
    kineticEnergy u = ∑' q, coefficientEnergy (u q) := by
  simp only [kineticEnergy, norm_coefficientVec_sq]

theorem summable_curlEnergy (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ coefficientEnergy (fourierCurl u q)) :=
  summable_coefficientEnergy _ (summable_amplitude _ (summable_firstMoment_curl u hu))

/-- Pointwise pressure projection and the signed viscous identity leave
only transport and curl dissipation in the actual coefficient energy rate. -/
theorem real_hermitian_infiniteVelocityRHS (u : FourierVelocity) (nu : ℝ)
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) :
    (coefficientHermitian (u q) (infiniteVelocityRHS nu u q)).re =
      (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • infiniteConvection u q)).re -
        nu * coefficientEnergy (fourierCurl u q) := by
  rw [infiniteVelocityRHS, hermitian_add_right, hermitian_leray_right q _ _ (hd q),
    Complex.add_re, viscous_energy_pair, fourierCurl_energy q u (hd q), ← norm_frequencyVec_sq]
  ring

/-- Exact kinetic balance of the infinite velocity vector field. -/
theorem infiniteVelocityRHS_kinetic_balance (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) :
    2 * (∑' q, (coefficientHermitian (u q) (infiniteVelocityRHS nu u q)).re) =
      -2 * nu * kineticEnergy (fourierCurl u) := by
  have hu1 := summable_firstMoment_of_second u hu
  have hc : Summable (fun q ↦ (coefficientHermitian (u q)
      ((-unitTorusDerivativePhase) • infiniteConvection u q)).re) := by
    simp_rw [real_hermitian_negativeConvection u hu1 hd]
    exact (summable_transportFlux u hu1).prod
  simp_rw [real_hermitian_infiniteVelocityRHS u nu hd]
  rw [hc.tsum_sub ((summable_curlEnergy u hu).mul_left nu),
    infiniteConvection_kinetic_cancellation u hu1 hr hd, tsum_mul_left,
    ← kineticEnergy_eq_tsum_coefficientEnergy]
  ring

end Mettapedia.FluidDynamics.NavierStokes.InfiniteKineticCancellation
