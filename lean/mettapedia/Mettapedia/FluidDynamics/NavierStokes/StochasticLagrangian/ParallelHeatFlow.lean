import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalInfiniteVelocity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCurlOutputTail
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Parallel heat flows solve the infinite Fourier Navier–Stokes equation

A velocity of the form `u = (0, 0, θ(x₀, x₁))` has zero nonlinear advection.
The cancellation holds for every interaction in the full infinite convolution,
not just for a retained Galerkin system. Each mode therefore evolves by its
ordinary heat multiplier. These exact solutions provide tests for proposed
signed-correlation estimates; they are not a general regularity theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakeBlockReality PancakeSobolevFiberEnvelope
open PancakeCoefficientLimitEquation PancakePeriodicVorticityEquation
open PancakeLocalInfiniteVelocity PancakeSobolevVelocityRate PancakeSobolevWeights

/-- A scalar Fourier coefficient in the third velocity component. -/
def vertical (c : ℂ) : VelocityCoefficient := fun i ↦ if i = 2 then c else 0

@[simp] theorem vertical_zero : vertical 0 = 0 := by
  ext i
  simp [vertical]

@[simp] theorem modeDot_vertical (q : Wavevector) (c : ℂ) :
    modeDot q (vertical c) = (q 2 : ℂ) * c := by
  simp [modeDot, vertical]

@[simp] theorem vertical_conj (c : ℂ) :
    vertical (conj c) = coefficientConjugate (vertical c) := by
  ext i
  by_cases hi : i = 2 <;> simp [vertical, coefficientConjugate, hi]

/-- Horizontal frequency support: no variation along the velocity direction. -/
def IsHorizontal (a : Wavevector → ℂ) : Prop := ∀ q, q 2 ≠ 0 → a q = 0

theorem transverse {a : Wavevector → ℂ} (ha : IsHorizontal a) (q : Wavevector) :
    modeDot q (vertical (a q)) = 0 := by
  by_cases hq : q 2 = 0
  · simp [hq]
  · simp [ha q hq, modeDot]

/-- Every nonlinear interaction vanishes before any infinite summation. -/
theorem outputFiber_eq_zero {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (q k : Wavevector) (i : Fin 3) :
    outputFiber q (fun l ↦ vertical (a l)) k i = 0 := by
  by_cases hk : k 2 = 0
  · by_cases hl : (q - k) 2 = 0
    · have hq : q 2 = 0 := by simpa [hk] using hl
      simp [outputFiber, hq]
    · simp [outputFiber, ha (q - k) hl]
  · simp [outputFiber, ha k hk, modeDot]

theorem infiniteConvection_eq_zero {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (q : Wavevector) : infiniteConvection (fun k ↦ vertical (a k)) q = 0 := by
  ext i
  simp [infiniteConvection, outputFiber_eq_zero ha]

theorem infiniteVelocityRHS_eq_viscous {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (ν : ℝ) (q : Wavevector) :
    infiniteVelocityRHS ν (fun k ↦ vertical (a k)) q =
      unitTorusViscousVorticityCoeff ν (fun k ↦ vertical (a k)) q := by
  ext i
  by_cases hq : modeSquare q = 0 <;>
    simp [infiniteVelocityRHS, infiniteConvection_eq_zero ha, lerayMode, modeDot, hq]

/-- The unit-torus heat decay rate, with the `2π` factors explicit. -/
def decayRate (ν : ℝ) (q : Wavevector) : ℝ :=
  ν * (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (q i : ℝ) ^ 2

theorem decayRate_nonneg {ν : ℝ} (hν : 0 ≤ ν) (q : Wavevector) :
    0 ≤ decayRate ν q :=
  mul_nonneg (mul_nonneg hν (sq_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

@[simp] theorem decayRate_neg (ν : ℝ) (q : Wavevector) :
    decayRate ν (-q) = decayRate ν q := by
  simp [decayRate]

theorem viscous_symbol (ν : ℝ) (q : Wavevector) :
    (ν : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q =
      (-decayRate ν q : ℝ) := by
  have hs : modeSquare q = ((∑ i : Fin 3, (q i : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp [modeSquare, sq, Complex.ofReal_sum]
  rw [hs]
  simp [decayRate, unitTorusDerivativePhase, mul_pow, Complex.I_sq]

/-- The full coefficient field, defined at every real time. -/
def coefficients (ν : ℝ) (a : Wavevector → ℂ) (t : ℝ) : FourierVelocity :=
  fun q ↦ vertical ((Real.exp (-decayRate ν q * t) : ℂ) * a q)

@[simp] theorem coefficients_initial (ν : ℝ) (a : Wavevector → ℂ) :
    coefficients ν a 0 = fun q ↦ vertical (a q) := by
  ext q i
  simp [coefficients]

theorem coefficients_horizontal {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (ν t : ℝ) : IsHorizontal (fun q ↦ (Real.exp (-decayRate ν q * t) : ℂ) * a q) := by
  intro q hq
  simp [ha q hq]

theorem coefficients_transverse {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (ν t : ℝ) (q : Wavevector) : modeDot q (coefficients ν a t q) = 0 :=
  transverse (coefficients_horizontal ha ν t) q

theorem coefficients_reality {a : Wavevector → ℂ}
    (ha : ∀ q, a (-q) = conj (a q)) (ν t : ℝ) (q : Wavevector) :
    coefficients ν a t (-q) = coefficientConjugate (coefficients ν a t q) := by
  rw [coefficients, decayRate_neg, ha]
  simpa only [coefficients, map_mul, Complex.conj_ofReal] using
    vertical_conj ((Real.exp (-decayRate ν q * t) : ℂ) * a q)

theorem coefficients_zero {a : Wavevector → ℂ} (ha : a 0 = 0) (ν t : ℝ) :
    coefficients ν a t 0 = 0 := by
  simp [coefficients, ha]

/-- The actual infinite Navier–Stokes equation, at every real time. -/
theorem hasDerivAt_coefficients {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (ν t : ℝ) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ coefficients ν a τ q i)
      (infiniteVelocityRHS ν (coefficients ν a t) q i) t := by
  rw [show coefficients ν a t =
    (fun k ↦ vertical ((Real.exp (-decayRate ν k * t) : ℂ) * a k)) from rfl,
    infiniteVelocityRHS_eq_viscous (coefficients_horizontal ha ν t)]
  simp only [unitTorusViscousVorticityCoeff, viscous_symbol, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = 2
  · have hd := (((hasDerivAt_id t).const_mul (-decayRate ν q)).exp.ofReal_comp).mul_const (a q)
    simpa [coefficients, vertical, hi, mul_comm, mul_left_comm, mul_assoc] using hd
  · simpa [coefficients, vertical, hi] using (hasDerivAt_const t (0 : ℂ))

theorem continuous_coefficients {a : Wavevector → ℂ} (ha : IsHorizontal a)
    (ν : ℝ) (q : Wavevector) (i : Fin 3) :
    Continuous (fun t ↦ coefficients ν a t q i) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_coefficients ha ν t q i).continuousAt

theorem exp_decay_le_one {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (q : Wavevector) :
    Real.exp (-decayRate ν q * t) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (decayRate_nonneg hν q)) ht)

theorem coefficients_eq_smul (ν t : ℝ) (a : Wavevector → ℂ) (q : Wavevector) :
    coefficients ν a t q = (Real.exp (-decayRate ν q * t) : ℂ) • vertical (a q) := by
  ext i
  by_cases hi : i = 2 <;> simp [coefficients, vertical, hi]

@[simp] theorem coefficientEnergy_vertical (c : ℂ) :
    coefficientEnergy (vertical c) = Complex.normSq c := by
  simp [coefficientEnergy, vertical, Fin.sum_univ_three]

theorem coefficientEnergy_le_initial {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Wavevector → ℂ) (q : Wavevector) :
    coefficientEnergy (coefficients ν a t q) ≤ coefficientEnergy (vertical (a q)) := by
  simp only [coefficients, coefficientEnergy_vertical, Complex.normSq_mul, Complex.normSq_ofReal]
  have he := exp_decay_le_one hν ht q
  have hp := (Real.exp_pos (-decayRate ν q * t)).le
  have hsq : Real.exp (-decayRate ν q * t) * Real.exp (-decayRate ν q * t) ≤ 1 := by
    nlinarith
  simpa using mul_le_mul_of_nonneg_right hsq (Complex.normSq_nonneg (a q))

/-- A finite initial bound, independent of the time horizon. -/
def initialSobolevEnergy (a : Wavevector →₀ ℂ) : ℝ :=
  sobolevEnergy a.support (fun q ↦ vertical (a q))

theorem sobolevEnergy_le_initial {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (a : Wavevector →₀ ℂ) (F : Finset Wavevector) :
    sobolevEnergy F (coefficients ν a t) ≤ initialSobolevEnergy a := by
  rw [sobolevEnergy_eq, initialSobolevEnergy, sobolevEnergy_eq]
  calc
    _ ≤ ∑ q ∈ F, weight q ^ 2 * coefficientEnergy (vertical (a q)) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (coefficientEnergy_le_initial hν ht a q) (sq_nonneg _)
    _ = ∑ q ∈ F ∩ a.support, weight q ^ 2 * coefficientEnergy (vertical (a q)) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro q _ hq
      have hz : a q = 0 := by
        by_contra hn
        exact hq (Finset.mem_inter.mpr ⟨‹q ∈ F›, Finsupp.mem_support_iff.mpr hn⟩)
      simp [hz, coefficientEnergy]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun q _ _ ↦ mul_nonneg (sq_nonneg _) (by
        rw [coefficientEnergy_vertical]
        exact Complex.normSq_nonneg _))

/-- A solution on any requested time interval, constructed from finite scalar data.
Its equation is the full infinite equation; finite support is only an input property. -/
def solution {ν : ℝ} (hν : 0 ≤ ν) (a : Wavevector →₀ ℂ)
    (ha : IsHorizontal a) (hr : ∀ q, a (-q) = conj (a q)) (hz : a 0 = 0) (T : ℝ) :
    LocalInfiniteVelocitySolution ν (fun q ↦ vertical (a q)) T (initialSobolevEnergy a) where
  coefficients := coefficients ν a
  continuous := continuous_coefficients ha ν
  initial := coefficients_initial ν a
  reality := coefficients_reality hr ν
  transverse := coefficients_transverse ha ν
  zero := coefficients_zero hz ν
  sobolev_bound := fun _ ht ↦ sobolevEnergy_le_initial hν ht.1 a
  equation := fun t _ q i ↦ hasDerivAt_coefficients ha ν t q i

open PancakeCurlOutputTail PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator

/-- Every absolute Fourier moment is bounded by its own initial value. -/
theorem fourierMoment_le_initial {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (m : ℕ) (a : Wavevector → ℂ) (q : Wavevector) :
    fourierMoment m (coefficients ν a t) q ≤ fourierMoment m (fun k ↦ vertical (a k)) q := by
  unfold fourierMoment
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [coefficients_eq_smul]
  change ‖(Real.exp (-decayRate ν q * t) : ℂ) • coefficientVec (vertical (a q))‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (exp_decay_le_one hν ht q)

theorem summable_initial_fourierMoment (m : ℕ) (a : Wavevector →₀ ℂ) :
    Summable (fourierMoment m (fun q ↦ vertical (a q))) := by
  apply summable_of_ne_finset_zero (s := a.support)
  intro q hq
  have hz : a q = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hq
  simp [fourierMoment, hz, coefficientVec]

/-- The common envelope required by the signed correlation balance is constructed,
not assumed, and works on the entire nonnegative time axis. -/
theorem exists_global_moment_envelope {ν : ℝ} (hν : 0 ≤ ν)
    (m : ℕ) (a : Wavevector →₀ ℂ) :
    ∃ g : Wavevector → ℝ, (∀ q, 0 ≤ g q) ∧ Summable g ∧
      ∀ t ≥ 0, ∀ q, fourierMoment m (coefficients ν a t) q ≤ g q :=
  ⟨fourierMoment m (fun q ↦ vertical (a q)), fourierMoment_nonneg _ _,
    summable_initial_fourierMoment m a, fun _ ht ↦ fourierMoment_le_initial hν ht m a⟩

end Mettapedia.FluidDynamics.NavierStokes.ParallelHeatFlow
