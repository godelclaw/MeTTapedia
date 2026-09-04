import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicCoherentSplit

/-!
# Complex periodic transfer of the coherent stretching estimate

This file moves the exact coherent pair estimate from rational test amplitudes
to the genuine complex Fourier coefficients of a periodic vorticity field.
It defines the actual complexified Biot--Savart strain symbol and proves that,
on lattice frequencies, it agrees with the cast of the rational symbol used
by the kinematic proof.  Complex phases then factor out bilinearly.

Consequently the aperture-gain estimate is valid for arbitrary complex scalar
amplitudes multiplying the actual periodic Leray directions `P_k e₀`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePeriodicComplexStretch

open scoped BigOperators Matrix ComplexConjugate
open PeriodicFourierTriad
open PancakeConeDirectionDichotomy
open PancakeCoherentPairEstimate
open PancakeCoherentWeightedTransfer
open PancakeConeLatticeCount
open PancakePeriodicCoherentSplit

/-- Integer wavevector cast as a complex coefficient vector. -/
def wavevectorCoefficient (k : Wavevector) : VelocityCoefficient :=
  fun i => (k i : ℂ)

/-- Coordinate cross product on complex Fourier coefficients. -/
def coefficientCross (u v : VelocityCoefficient) : VelocityCoefficient :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Complexified Biot--Savart amplitude, with the harmless Fourier phase
suppressed exactly as in the rational kinematic model. -/
def complexBiotSavartAmp (k : Wavevector) (w : VelocityCoefficient) :
    VelocityCoefficient :=
  (1 / modeSquare k) • coefficientCross (wavevectorCoefficient k) w

/-- Actual complex amplitude symbol of `S(u_source) w_receiver`, again with
the common Fourier phase suppressed. -/
def complexStretchAmp (k : Wavevector) (wSource wReceiver : VelocityCoefficient) :
    VelocityCoefficient :=
  let u := complexBiotSavartAmp k wSource
  (1 / 2 : ℂ) •
    (coefficientDot u wReceiver • wavevectorCoefficient k +
      modeDot k wReceiver • u)

/-- Coordinate `ℓ¹` norm of a complex Fourier coefficient. -/
def coefficientL1 (v : VelocityCoefficient) : ℝ :=
  ∑ i : Fin 3, ‖v i‖

theorem coefficientCross_smul_right (u v : VelocityCoefficient) (a : ℂ) :
    coefficientCross u (a • v) = a • coefficientCross u v := by
  ext i
  fin_cases i <;> norm_num [coefficientCross] <;> ring

theorem coefficientDot_smul_left (a : ℂ)
    (u v : VelocityCoefficient) :
    coefficientDot (a • u) v = a * coefficientDot u v := by
  simp only [coefficientDot, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coefficientDot_smul_right (a : ℂ)
    (u v : VelocityCoefficient) :
    coefficientDot u (a • v) = a * coefficientDot u v := by
  simp only [coefficientDot, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexBiotSavartAmp_smul (k : Wavevector)
    (w : VelocityCoefficient) (a : ℂ) :
    complexBiotSavartAmp k (a • w) = a • complexBiotSavartAmp k w := by
  unfold complexBiotSavartAmp
  rw [coefficientCross_smul_right]
  ext i
  simp only [Pi.smul_apply]
  ring

/-- The complex strain symbol is bilinear in source and receiver amplitudes. -/
theorem complexStretchAmp_smul_smul (k : Wavevector)
    (wSource wReceiver : VelocityCoefficient) (a b : ℂ) :
    complexStretchAmp k (a • wSource) (b • wReceiver) =
      (a * b) • complexStretchAmp k wSource wReceiver := by
  unfold complexStretchAmp
  rw [complexBiotSavartAmp_smul]
  dsimp only
  rw [coefficientDot_smul_left,
    coefficientDot_smul_right,
    PancakePeriodicCoherentSplit.modeDot_smul]
  ext i
  fin_cases i <;>
    simp only [Pi.smul_apply, Pi.add_apply] <;>
    ring

/-- The genuine complex periodic symbol agrees with the cast of the exact
rational symbol on coherent lattice directions. -/
theorem complexStretchAmp_periodicCoherent_eq_ratCast
    {N₁ N₂ : ℕ} {k₁ k₂ : Lattice3}
    (hk₁ : InSquarePancakeConeBall N₁ k₁)
    (hk₂ : InSquarePancakeConeBall N₂ k₂) :
    complexStretchAmp (latticeToWavevector k₁)
      (periodicCoherentMode (latticeToWavevector k₁))
      (periodicCoherentMode (latticeToWavevector k₂)) =
    ratVecToCoefficient
      (stretchAmp (toRatVec k₁) (coherentP (toRatVec k₁))
        (coherentP (toRatVec k₂))) := by
  rw [periodicCoherentMode_latticeToWavevector hk₁,
    periodicCoherentMode_latticeToWavevector hk₂]
  unfold complexStretchAmp complexBiotSavartAmp
  rw [modeSquare_latticeToWavevector]
  have hnorm : (latticeNormSq k₁ : ℂ) = (normSq (toRatVec k₁) : ℂ) := by
    rw [normSq_toRatVec]
    norm_cast
  rw [hnorm]
  ext i
  fin_cases i <;>
    simp only [coefficientCross, wavevectorCoefficient, coefficientDot, modeDot,
      latticeToWavevector, ratVecToCoefficient, stretchAmp, biotSavartAmp,
      PancakeConeDirectionDichotomy.cross,
      PancakeConeDirectionDichotomy.dot,
      PancakeConeDirectionDichotomy.smul,
      PancakeConeDirectionDichotomy.add, toRatVec, normSq,
      Fin.sum_univ_three, Pi.smul_apply, Pi.add_apply] <;>
    push_cast <;>
    field_simp [normSq_toRatVec_ne_zero hk₁] <;>
    ring

theorem coefficientL1_smul (a : ℂ) (v : VelocityCoefficient) :
    coefficientL1 (a • v) = ‖a‖ * coefficientL1 v := by
  unfold coefficientL1
  simp_rw [Pi.smul_apply, norm_smul]
  rw [Finset.mul_sum]

theorem coefficientL1_ratVecToCoefficient (v : Vec3) :
    coefficientL1 (ratVecToCoefficient v) = (l1Norm v : ℝ) := by
  obtain ⟨x, y, z⟩ := v
  simp only [coefficientL1, ratVecToCoefficient, l1Norm, Fin.sum_univ_three]
  push_cast
  have hx : ‖(x : ℂ)‖ = |(x : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hy : ‖(y : ℂ)‖ = |(y : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hz : ‖(z : ℂ)‖ = |(z : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hx, hy, hz]

/-- Real aperture constant obtained by casting the exact rational pair bound. -/
def periodicCoherentGain (N₁ N₂ : ℕ) : ℝ :=
  ((6 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) : ℚ) : ℝ)

theorem periodicCoherentGain_nonneg (N₁ N₂ : ℕ) :
    0 ≤ periodicCoherentGain N₁ N₂ := by
  unfold periodicCoherentGain
  positivity

/-- **Complex-amplitude coherent pair estimate on the periodic lattice.** -/
theorem coefficientL1_complexStretchAmp_coherent_le
    {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {k₁ k₂ : Lattice3}
    (hk₁ : InSquarePancakeConeBall N₁ k₁)
    (hk₂ : InSquarePancakeConeBall N₂ k₂)
    (a b : ℂ) :
    coefficientL1
      (complexStretchAmp (latticeToWavevector k₁)
        (a • periodicCoherentMode (latticeToWavevector k₁))
        (b • periodicCoherentMode (latticeToWavevector k₂))) ≤
      periodicCoherentGain N₁ N₂ * ‖a‖ * ‖b‖ := by
  rw [complexStretchAmp_smul_smul,
    complexStretchAmp_periodicCoherent_eq_ratCast hk₁ hk₂,
    coefficientL1_smul, coefficientL1_ratVecToCoefficient]
  have hrat := l1Norm_stretchAmp_coherentP_le
    (toRatVec k₁) (toRatVec k₂) (1 / (N₁ : ℚ)) (1 / (N₂ : ℚ)) 1 1
    (normSq_toRatVec_ne_zero hk₁) (normSq_toRatVec_ne_zero hk₂)
    (by positivity) (by positivity)
    (toRatVec_mem_cone hk₁) (toRatVec_mem_cone hk₂)
    (inv_nat_sq_le_quarter hN₁) (inv_nat_sq_le_quarter hN₂)
  norm_num at hrat
  have hreal :
      (l1Norm (stretchAmp (toRatVec k₁) (coherentP (toRatVec k₁))
        (coherentP (toRatVec k₂))) : ℝ) ≤
      periodicCoherentGain N₁ N₂ := by
    unfold periodicCoherentGain
    exact_mod_cast (show l1Norm (stretchAmp (toRatVec k₁)
      (coherentP (toRatVec k₁)) (coherentP (toRatVec k₂))) ≤
        6 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) by
      simpa [PancakeConeDirectionDichotomy.smul] using hrat)
  have hab : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖a * b‖ *
        (l1Norm (stretchAmp (toRatVec k₁) (coherentP (toRatVec k₁))
          (coherentP (toRatVec k₂))) : ℝ)
      = (l1Norm (stretchAmp (toRatVec k₁) (coherentP (toRatVec k₁))
          (coherentP (toRatVec k₂))) : ℝ) * (‖a‖ * ‖b‖) := by
          rw [norm_mul]
          ring
    _ ≤ periodicCoherentGain N₁ N₂ *
          (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hreal hab
    _ = periodicCoherentGain N₁ N₂ * ‖a‖ * ‖b‖ := by ring

/-- Coordinate `ℓ¹` triangle inequality for finite complex vector sums. -/
theorem coefficientL1_sum_le_sum_coefficientL1 {ι : Type*}
    (s : Finset ι) (f : ι → VelocityCoefficient) :
    coefficientL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientL1 (f i) := by
  have h0 := norm_sum_le s (fun i => f i 0)
  have h1 := norm_sum_le s (fun i => f i 1)
  have h2 := norm_sum_le s (fun i => f i 2)
  simp only [coefficientL1, Fin.sum_univ_three, Finset.sum_apply,
    Finset.sum_add_distrib] at h0 h1 h2 ⊢
  linarith

/-- **Cardinality-free complex convolution bound.**  The source pays its
actual complex Fourier `ℓ¹` mass. -/
theorem coefficientL1_sum_complexStretchAmp_coherent_le
    {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    (s : Finset Lattice3) (k₂ : Lattice3)
    (a : Lattice3 → ℂ) (b : ℂ)
    (hs : ∀ k ∈ s, InSquarePancakeConeBall N₁ k)
    (hk₂ : InSquarePancakeConeBall N₂ k₂) :
    coefficientL1 (∑ k ∈ s,
      complexStretchAmp (latticeToWavevector k)
        (a k • periodicCoherentMode (latticeToWavevector k))
        (b • periodicCoherentMode (latticeToWavevector k₂))) ≤
      periodicCoherentGain N₁ N₂ *
        (∑ k ∈ s, ‖a k‖) * ‖b‖ := by
  calc
    coefficientL1 (∑ k ∈ s,
        complexStretchAmp (latticeToWavevector k)
          (a k • periodicCoherentMode (latticeToWavevector k))
          (b • periodicCoherentMode (latticeToWavevector k₂)))
      ≤ ∑ k ∈ s, coefficientL1
          (complexStretchAmp (latticeToWavevector k)
            (a k • periodicCoherentMode (latticeToWavevector k))
            (b • periodicCoherentMode (latticeToWavevector k₂))) :=
        coefficientL1_sum_le_sum_coefficientL1 s _
    _ ≤ ∑ k ∈ s,
        periodicCoherentGain N₁ N₂ * ‖a k‖ * ‖b‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact coefficientL1_complexStretchAmp_coherent_le hN₁ hN₂
        (hs k hk) hk₂ (a k) b
    _ = periodicCoherentGain N₁ N₂ *
        (∑ k ∈ s, ‖a k‖) * ‖b‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Cauchy--Schwarz for complex amplitude mass on a finite mode set. -/
theorem sq_sum_complex_norm_le_card_mul_sum_norm_sq {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) :
    (∑ i ∈ s, ‖a i‖) ^ 2 ≤ s.card * ∑ i ∈ s, ‖a i‖ ^ 2 := by
  exact sq_sum_le_card_mul_sum_sq

/-- **Energy-facing square-dyadic estimate for actual complex Fourier
amplitudes.**  The exact pancake lattice count removes the abstract cardinality
premise. -/
theorem sq_coherentComplexConvolution_le_squareDyadicEnergy
    {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    (s : Finset Lattice3) (k₂ : Lattice3)
    (a : Lattice3 → ℂ) (b : ℂ)
    (hs : ∀ k ∈ s, InSquarePancakeConeBall N₁ k)
    (hk₂ : InSquarePancakeConeBall N₂ k₂) :
    coefficientL1 (∑ k ∈ s,
      complexStretchAmp (latticeToWavevector k)
        (a k • periodicCoherentMode (latticeToWavevector k))
        (b • periodicCoherentMode (latticeToWavevector k₂))) ^ 2 ≤
      periodicCoherentGain N₁ N₂ ^ 2 *
        ((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) *
        (∑ k ∈ s, ‖a k‖ ^ 2) * ‖b‖ ^ 2 := by
  have hlin := coefficientL1_sum_complexStretchAmp_coherent_le
    hN₁ hN₂ s k₂ a b hs hk₂
  have hcs := sq_sum_complex_norm_le_card_mul_sum_norm_sq s a
  have hcardNat := card_le_pancakeBox s hs
  have hcard : (s.card : ℝ) ≤
      (((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hlhs : 0 ≤ coefficientL1 (∑ k ∈ s,
      complexStretchAmp (latticeToWavevector k)
        (a k • periodicCoherentMode (latticeToWavevector k))
        (b • periodicCoherentMode (latticeToWavevector k₂))) := by
    unfold coefficientL1
    positivity
  have hmass : 0 ≤ ∑ k ∈ s, ‖a k‖ := by positivity
  have hb : 0 ≤ ‖b‖ := norm_nonneg _
  have hgain : 0 ≤ periodicCoherentGain N₁ N₂ :=
    periodicCoherentGain_nonneg N₁ N₂
  have hsquared := (sq_le_sq₀ hlhs
    (mul_nonneg (mul_nonneg hgain hmass) hb)).2 hlin
  calc
    coefficientL1 (∑ k ∈ s,
        complexStretchAmp (latticeToWavevector k)
          (a k • periodicCoherentMode (latticeToWavevector k))
          (b • periodicCoherentMode (latticeToWavevector k₂))) ^ 2
      ≤ (periodicCoherentGain N₁ N₂ *
          (∑ k ∈ s, ‖a k‖) * ‖b‖) ^ 2 := hsquared
    _ ≤ periodicCoherentGain N₁ N₂ ^ 2 *
          s.card * (∑ k ∈ s, ‖a k‖ ^ 2) * ‖b‖ ^ 2 := by
      have hscale : (0 : ℝ) ≤
          periodicCoherentGain N₁ N₂ ^ 2 *
            ‖b‖ ^ 2 := by positivity
      calc
        (periodicCoherentGain N₁ N₂ *
            (∑ k ∈ s, ‖a k‖) * ‖b‖) ^ 2 =
            (periodicCoherentGain N₁ N₂ ^ 2 *
              ‖b‖ ^ 2) * (∑ k ∈ s, ‖a k‖) ^ 2 := by ring
        _ ≤ (periodicCoherentGain N₁ N₂ ^ 2 *
              ‖b‖ ^ 2) * (s.card * ∑ k ∈ s, ‖a k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hscale
        _ = periodicCoherentGain N₁ N₂ ^ 2 *
            s.card * (∑ k ∈ s, ‖a k‖ ^ 2) * ‖b‖ ^ 2 := by ring
    _ ≤ periodicCoherentGain N₁ N₂ ^ 2 *
          (((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) : ℝ) *
          (∑ k ∈ s, ‖a k‖ ^ 2) * ‖b‖ ^ 2 := by
      have hfactor : (0 : ℝ) ≤
          periodicCoherentGain N₁ N₂ ^ 2 := by
        positivity
      have henergy : 0 ≤ ∑ k ∈ s, ‖a k‖ ^ 2 := by positivity
      have hb2 : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard hfactor) henergy) hb2

end PancakePeriodicComplexStretch
end NavierStokes
end FluidDynamics
end Mettapedia
