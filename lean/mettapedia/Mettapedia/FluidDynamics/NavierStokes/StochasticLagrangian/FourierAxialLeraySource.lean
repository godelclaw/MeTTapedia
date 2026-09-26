import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierBeltWeightedPolarization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation
import Mettapedia.Analysis.FiniteConvolutionEnergy

/-!
# Axial pressure production and transport

The axial component of the physical Leray-projected convection separates
into a pressure source and transport of existing axial velocity. Both
pressure derivatives use the output frequency, by the existing pressure
identity. The resulting bounds retain cancellation at zero output and
the actual unit-torus derivative phase. No geometric persistence or
physical-time budget is assumed to follow from these finite estimates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierAxialLeraySource

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
  PancakeFourierPressureStrain PancakeLowPressureBudget PancakeFrequencyProjectorCommutator
  PancakeIncomingLowSourceEnergy FourierSingleConeStretch FourierBeltPolarization
  FourierPancakePairDepletion FourierVorticitySource InfiniteFilteredEquation
  PancakeCoefficientLimitEquation PancakeViscousMisalignmentAbsorption FourierBeltKernel
  PancakeCurlOutputTail

theorem coefficientDot_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → VelocityCoefficient) (a : VelocityCoefficient) :
    coefficientDot (∑ i ∈ s, f i) a = ∑ i ∈ s, coefficientDot (f i) a := by
  simp only [coefficientDot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem coefficientDot_add_left (a b c : VelocityCoefficient) :
    coefficientDot (a + b) c = coefficientDot a c + coefficientDot b c := by
  simp only [coefficientDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The projection identity also holds at the zero mode, with the usual division convention. -/
theorem axial_lerayMode (n : Fin 3 → ℝ) (q : Wavevector) (v : VelocityCoefficient) :
    coefficientDot (lerayMode q v) (axisCoefficient n) =
      coefficientDot v (axisCoefficient n) -
        modeDot q (axisCoefficient n) * modeDot q v / modeSquare q := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, hq]
  · simp [lerayMode, hq, coefficientDot, modeDot, Fin.sum_univ_three]
    ring

/-- Axial pressure force, using the existing scalar pressure coefficient. -/
def axialPressureSource (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) : ℂ :=
  -unitTorusDerivativePhase * modeDot q (axisCoefficient n) * pressureCoeff P u q

/-- Transport of the axial velocity already present in the inputs. -/
def axialTransportSource (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) : ℂ :=
  -unitTorusDerivativePhase * coefficientDot (convectionConvolution P u q) (axisCoefficient n)

/-- The split applies to the actual projected nonlinear coefficient, including its phase. -/
theorem axial_projected_convection (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    coefficientDot (lerayMode q ((-unitTorusDerivativePhase) • convectionConvolution P u q))
        (axisCoefficient n) = axialPressureSource n P u q + axialTransportSource n P u q := by
  rw [lerayMode_smul, coefficientDot_smul_left, axial_lerayMode]
  unfold axialPressureSource axialTransportSource pressureCoeff
  ring

def axialPressurePair (n : Fin 3 → ℝ) (q : Wavevector)
    (a b : VelocityCoefficient) : ℂ :=
  unitTorusDerivativePhase * modeDot q (axisCoefficient n) *
    (modeDot q a * modeDot q b / modeSquare q)

def axialTransportPair (n : Fin 3 → ℝ) (q : Wavevector)
    (a b : VelocityCoefficient) : ℂ :=
  -unitTorusDerivativePhase * modeDot q a * coefficientDot b (axisCoefficient n)

/-- Both pressure derivatives are transferred to the output by incompressibility. -/
theorem axialPressureSource_eq_pairs (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    axialPressureSource n P u q =
      ∑ p ∈ interactionPairs P q, axialPressurePair n q (u p.1) (u p.2) := by
  rw [axialPressureSource, pressureCoeff, pressure_numerator_output_pair P u q hu]
  simp only [axialPressurePair, ← Finset.mul_sum, ← Finset.sum_div]
  ring

theorem axialTransportSource_eq_pairs (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    axialTransportSource n P u q =
      ∑ p ∈ interactionPairs P q, axialTransportPair n q (u p.1) (u p.2) := by
  rw [axialTransportSource, convectionConvolution_eq_pairSum, coefficientDot_sum_left,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hm := Finset.mem_filter.mp hp
  have hd : modeDot q (u p.1) = modeDot p.2 (u p.1) := by
    rw [← hm.2, modeDot_add_wavevector, hu p.1 (Finset.mem_product.mp hm.1).1, zero_add]
  rw [orderedConvection, coefficientDot_smul_left, axialTransportPair, hd]
  ring

/-- The pressure pair has an axial output factor and no inverse-frequency singularity. -/
theorem norm_axialPressurePair_le (n : Fin 3 → ℝ) (q : Wavevector)
    (a b : VelocityCoefficient) :
    ‖axialPressurePair n q a b‖ ≤
      2 * Real.pi * ‖modeDot q (axisCoefficient n)‖ * ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  by_cases hq : q = 0
  · subst q
    simp [axialPressurePair, modeDot]
  · have hqnorm := norm_pos_iff.mpr (frequencyVec_ne_zero hq)
    simp only [axialPressurePair, norm_mul, norm_div, norm_derivativePhase, norm_modeSquare]
    calc
      _ ≤ (2 * Real.pi) * ‖modeDot q (axisCoefficient n)‖ *
          ((‖frequencyVec q‖ * ‖coefficientVec a‖) *
            (‖frequencyVec q‖ * ‖coefficientVec b‖) / ‖frequencyVec q‖ ^ 2) := by
        gcongr <;> exact norm_modeDot_le q _
      _ = _ := by field_simp

theorem norm_axialTransportPair_le (n : Fin 3 → ℝ) (q : Wavevector)
    (a b : VelocityCoefficient) :
    ‖axialTransportPair n q a b‖ ≤
      2 * Real.pi * ‖frequencyVec q‖ * ‖coefficientVec a‖ *
        ‖coefficientDot b (axisCoefficient n)‖ := by
  simp only [axialTransportPair, norm_mul, norm_neg, norm_derivativePhase]
  calc
    _ ≤ (2 * Real.pi) * (‖frequencyVec q‖ * ‖coefficientVec a‖) *
        ‖coefficientDot b (axisCoefficient n)‖ := by
      gcongr
      exact norm_modeDot_le q a
    _ = _ := by ring

/-- All outputs are permitted, including zero and outputs outside the input shell. -/
theorem norm_axialPressureSource_le_pairs (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    ‖axialPressureSource n P u q‖ ≤ 2 * Real.pi * ‖modeDot q (axisCoefficient n)‖ *
      ∑ p ∈ interactionPairs P q, ‖coefficientVec (u p.1)‖ * ‖coefficientVec (u p.2)‖ := by
  rw [axialPressureSource_eq_pairs n P u q hu, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  simpa only [mul_assoc] using norm_axialPressurePair_le n q (u p.1) (u p.2)

theorem norm_axialTransportSource_le_pairs (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    ‖axialTransportSource n P u q‖ ≤ 2 * Real.pi * ‖frequencyVec q‖ *
      ∑ p ∈ interactionPairs P q, ‖coefficientVec (u p.1)‖ *
        ‖coefficientDot (u p.2) (axisCoefficient n)‖ := by
  rw [axialTransportSource_eq_pairs n P u q hu, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  simpa only [mul_assoc] using norm_axialTransportPair_le n q (u p.1) (u p.2)

/-- The existing kinetic-energy pressure bound retains the axial output factor. -/
theorem norm_axialPressureSource_le_energy (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    ‖axialPressureSource n P u q‖ ≤
      2 * Real.pi * ‖modeDot q (axisCoefficient n)‖ * fullEnergy P u := by
  simpa only [axialPressureSource, norm_mul, norm_neg, norm_derivativePhase] using
    mul_le_mul_of_nonneg_left (norm_pressureCoeff_le_kineticEnergy P u q hu)
      (by positivity : 0 ≤ 2 * Real.pi * ‖modeDot q (axisCoefficient n)‖)

/-- The existing finite Young inequality bounds the energy of all axial pressure outputs. -/
theorem sum_axialPressureSource_sq_le (n : Fin 3 → ℝ) (P Q : Finset Wavevector)
    (u : FourierVelocity) (W : ℝ) (hW : 0 ≤ W)
    (hu : ∀ k ∈ P, modeDot k (u k) = 0)
    (hwidth : ∀ p ∈ P, ∀ r ∈ P, ‖modeDot (p + r) (axisCoefficient n)‖ ≤ W)
    (hQ : ∀ p ∈ P, ∀ r ∈ P, p + r ∈ Q) :
    (∑ q ∈ Q, ‖axialPressureSource n P u q‖ ^ 2) ≤
      (2 * Real.pi * W) ^ 2 * (∑ p ∈ P, ‖coefficientVec (u p)‖) ^ 2 * fullEnergy P u := by
  have h := Mettapedia.Analysis.FiniteConvolutionEnergy.sum_norm_sq_le P P Q
    (fun p ↦ (2 * Real.pi * W) * ‖coefficientVec (u p)‖)
    (fun r ↦ ‖coefficientVec (u r)‖)
    (fun p r ↦ axialPressurePair n (p + r) (u p) (u r))
    (fun _ _ ↦ by positivity) (fun p hp r hr ↦ by
      exact (norm_axialPressurePair_le n (p + r) (u p) (u r)).trans
        (by gcongr; exact hwidth p hp r hr)) hQ
  have he : ∀ q, (∑ pr ∈ P ×ˢ P with pr.1 + pr.2 = q,
      axialPressurePair n (pr.1 + pr.2) (u pr.1) (u pr.2)) = axialPressureSource n P u q := by
    intro q
    rw [axialPressureSource_eq_pairs n P u q hu]
    refine Finset.sum_congr rfl fun pr hpr ↦ ?_
    rw [(Finset.mem_filter.mp hpr).2]
  simp only [he, ← Finset.mul_sum, mul_pow, norm_coefficientVec_sq] at h
  simpa only [fullEnergy, mul_pow, mul_assoc] using h

/-- Transport depends on the axial input energy rather than the full receiver energy. -/
theorem sum_axialTransportSource_sq_le (n : Fin 3 → ℝ) (P Q : Finset Wavevector)
    (u : FourierVelocity) (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ k ∈ P, modeDot k (u k) = 0)
    (hradius : ∀ p ∈ P, ∀ r ∈ P, ‖frequencyVec (p + r)‖ ≤ R)
    (hQ : ∀ p ∈ P, ∀ r ∈ P, p + r ∈ Q) :
    (∑ q ∈ Q, ‖axialTransportSource n P u q‖ ^ 2) ≤
      (2 * Real.pi * R) ^ 2 * (∑ p ∈ P, ‖coefficientVec (u p)‖) ^ 2 *
        ∑ r ∈ P, ‖coefficientDot (u r) (axisCoefficient n)‖ ^ 2 := by
  have h := Mettapedia.Analysis.FiniteConvolutionEnergy.sum_norm_sq_le P P Q
    (fun p ↦ (2 * Real.pi * R) * ‖coefficientVec (u p)‖)
    (fun r ↦ ‖coefficientDot (u r) (axisCoefficient n)‖)
    (fun p r ↦ axialTransportPair n (p + r) (u p) (u r))
    (fun _ _ ↦ by positivity) (fun p hp r hr ↦ by
      exact (norm_axialTransportPair_le n (p + r) (u p) (u r)).trans
        (by gcongr; exact hradius p hp r hr)) hQ
  have he : ∀ q, (∑ pr ∈ P ×ˢ P with pr.1 + pr.2 = q,
      axialTransportPair n (pr.1 + pr.2) (u pr.1) (u pr.2)) = axialTransportSource n P u q := by
    intro q
    rw [axialTransportSource_eq_pairs n P u q hu]
    refine Finset.sum_congr rfl fun pr hpr ↦ ?_
    rw [(Finset.mem_filter.mp hpr).2]
  simpa only [he, ← Finset.mul_sum, mul_pow, mul_assoc] using h

/-- Belt sums lie in a thin slab even when their direction is outside the input belt. -/
theorem belt_pair_output_bounds (n : Fin 3 → ℝ) (N : ℕ) (hN : 0 < N)
    (p r : Wavevector) (hp : InBeltShell N n p) (hr : InBeltShell N n r) :
    ‖modeDot (p + r) (axisCoefficient n)‖ ≤ 4 * N ∧
      ‖frequencyVec (p + r)‖ ≤ 4 * (N : ℝ) ^ 2 := by
  constructor
  · rw [← coefficientDot_wavevector_right, axis_mode_dot_norm]
    have h := (InBeltShell.inSlab hN hp).add (InBeltShell.inSlab hN hr)
    change |∑ i : Fin 3, ((p + r) i : ℝ) * n i| ≤ _ at h
    convert h using 1
    push_cast
    ring
  · calc
      _ ≤ ‖frequencyVec p‖ + ‖frequencyVec r‖ := by
        rw [frequencyVec_add]
        exact norm_add_le _ _
      _ ≤ _ := by linarith [hp.2.1, hr.2.1]

/-- All pressure outputs of one belt retain the slab factor `N` rather than `N²`. -/
theorem sum_belt_pressureSource_sq_le (n : Fin 3 → ℝ) (N : ℕ) (hN : 0 < N)
    (P Q : Finset Wavevector) (u : FourierVelocity)
    (hP : ∀ k ∈ P, InBeltShell N n k) (hu : ∀ k ∈ P, modeDot k (u k) = 0)
    (hQ : ∀ p ∈ P, ∀ r ∈ P, p + r ∈ Q) :
    (∑ q ∈ Q, ‖axialPressureSource n P u q‖ ^ 2) ≤
      (8 * Real.pi * N) ^ 2 * (∑ p ∈ P, ‖coefficientVec (u p)‖) ^ 2 * fullEnergy P u := by
  have h := sum_axialPressureSource_sq_le n P Q u (4 * N) (by positivity) hu
    (fun p hp r hr ↦ (belt_pair_output_bounds n N hN p r (hP p hp) (hP r hr)).1) hQ
  convert h using 1; ring

/-- The transport estimate instead carries the output radius and the existing axial energy. -/
theorem sum_belt_transportSource_sq_le (n : Fin 3 → ℝ) (N : ℕ) (hN : 0 < N)
    (P Q : Finset Wavevector) (u : FourierVelocity)
    (hP : ∀ k ∈ P, InBeltShell N n k) (hu : ∀ k ∈ P, modeDot k (u k) = 0)
    (hQ : ∀ p ∈ P, ∀ r ∈ P, p + r ∈ Q) :
    (∑ q ∈ Q, ‖axialTransportSource n P u q‖ ^ 2) ≤
      (8 * Real.pi * (N : ℝ) ^ 2) ^ 2 * (∑ p ∈ P, ‖coefficientVec (u p)‖) ^ 2 *
        ∑ r ∈ P, ‖coefficientDot (u r) (axisCoefficient n)‖ ^ 2 := by
  have h := sum_axialTransportSource_sq_le n P Q u (4 * (N : ℝ) ^ 2) (by positivity) hu
    (fun p hp r hr ↦ (belt_pair_output_bounds n N hN p r (hP p hp) (hP r hr)).2) hQ
  convert h using 1; ring

/-- The exact finite equation retains the signed viscous term. -/
theorem axial_velocityRHS (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (ν : ℝ) (q : Wavevector)
    (hP : ∀ k ∈ P, frequencyVec k ≠ 0) (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    coefficientDot (velocityRHS P u ν q) (axisCoefficient n) =
      axialPressureSource n P u q + axialTransportSource n P u q +
        ((ν : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) *
          coefficientDot (u q) (axisCoefficient n) := by
  rw [velocityRHS, finiteTransport_fourierCurl_eq P u hP hu, coefficientDot_add_left,
    axial_projected_convection, unitTorusViscousVorticityCoeff, coefficientDot_smul_left]

/-- Finite support identifies this with the actual infinite unforced vector field. -/
theorem axial_infiniteVelocityRHS (n : Fin 3 → ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (ν : ℝ) (q : Wavevector)
    (hs : ∀ k, k ∉ P → u k = 0) (hP : ∀ k ∈ P, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ P, modeDot k (u k) = 0) :
    coefficientDot (infiniteVelocityRHS ν u q) (axisCoefficient n) =
      axialPressureSource n P u q + axialTransportSource n P u q +
        ((ν : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) *
          coefficientDot (u q) (axisCoefficient n) := by
  rw [infiniteVelocityRHS_eq_finite P u hs hP hu]
  exact axial_velocityRHS n P u ν q hP hu

end Mettapedia.FluidDynamics.NavierStokes.FourierAxialLeraySource
