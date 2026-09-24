import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierHeatCommutatorKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy

/-!
# Kinetic and enstrophy bounds for the actual heat commutator

The same all-input commutator is bounded by kinetic energy and by heat
time times enstrophy. Multiplying the two bounds gives an energy-enstrophy
payer without a vorticity-gradient supremum. The output-frequency factor
is explicit and is not asserted to be summable over all outputs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorEnergy

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeGalerkinKineticEnergy
open PancakeIncomingLowSourceEnergy PancakeSignedTransportEnergy PancakeSobolevFiberEnvelope
open PancakeFixedOutputVelocityBound PancakePeriodicVorticityEquation
open InfiniteConvectionEnergy InfiniteFilteredEquation FourierHeatFlow FourierHeatCommutatorKernel
open FourierVorticityPairDynamics
open PancakeLowPressureBudget

theorem abs_multiplier_defect_le_one {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (k l : Wavevector) :
    |multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l| ≤ 1 := by
  have hq := multiplier_le_one hν hσ (k + l)
  have hq0 := (multiplier_pos ν σ (k + l)).le
  have hp0 := mul_nonneg (multiplier_pos ν σ k).le (multiplier_pos ν σ l).le
  have hp : multiplier ν σ k * multiplier ν σ l ≤ 1 :=
    mul_le_one₀ (multiplier_le_one hν hσ k) (multiplier_pos ν σ l).le (multiplier_le_one hν hσ l)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_frequency_contraction_le (k l : Wavevector) :
    |∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)| ≤ ‖frequencyVec k‖ * ‖frequencyVec l‖ := by
  have h := norm_modeDot_le k (wavevectorCoefficient l)
  have he : modeDot k (wavevectorCoefficient l) =
      ((∑ j : Fin 3, (k j : ℝ) * (l j : ℝ) : ℝ) : ℂ) := by
    simp [modeDot, wavevectorCoefficient]
  simpa only [he, Complex.norm_real, Real.norm_eq_abs, frequencyVec, coefficientVec,
    wavevectorCoefficient] using h

theorem abs_rateDefect_le {ν : ℝ} (hν : 0 ≤ ν) (k l : Wavevector) :
    |rateDefect ν k l| ≤ 2 * ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec l‖ := by
  rw [rateDefect_eq_frequency_contraction]
  have he : -2 * ν * (2 * Real.pi) ^ 2 * (∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) =
      -(2 * ν * (2 * Real.pi) ^ 2) * (∑ j : Fin 3, (k j : ℝ) * (l j : ℝ)) := by ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * ν * (2 * Real.pi) ^ 2)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (abs_frequency_contraction_le k l)
      (by positivity : 0 ≤ 2 * ν * (2 * Real.pi) ^ 2)

theorem abs_multiplier_defect_le_enstrophy_weight {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (k l : Wavevector) :
    |multiplier ν σ (k + l) - multiplier ν σ k * multiplier ν σ l| ≤
      (2 * ν * σ) * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec l‖ := by
  have hd : 0 ≤ modeDamping ν (k + l) := by unfold modeDamping; positivity
  have hs : 0 ≤ pairDamping ν k l := by unfold pairDamping modeDamping; positivity
  have he : Real.exp (-min (modeDamping ν (k + l)) (pairDamping ν k l) * σ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_min hd hs)) hσ)
  calc
    _ ≤ |rateDefect ν k l| * σ := (abs_multiplier_sub_le ν k l hσ).trans
      (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hσ) he)
    _ ≤ (2 * ν * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec l‖) * σ :=
      mul_le_mul_of_nonneg_right (abs_rateDefect_le hν k l) hσ
    _ = _ := by ring

theorem norm_fourierCurl_eq (u : FourierVelocity) (k : Wavevector)
    (hd : modeDot k (u k) = 0) :
    ‖coefficientVec (fourierCurl u k)‖ =
      (2 * Real.pi) * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := fourierCurl_energy k u hd
  simp only [← norm_coefficientVec_sq, mul_pow] at *
  exact h

theorem norm_weightedConvection_le_enstrophy (mask : Wavevector → ℂ) (u : FourierVelocity)
    (M : ℝ) (q : Wavevector)
    (hm : ∀ k, ‖mask k‖ ≤ M * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec (q-k)‖)
    (hM : 0 ≤ M) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖ ^ 2)) :
    ‖coefficientVec (weightedConvection mask u q)‖ ≤
      M * ‖frequencyVec q‖ * kineticEnergy (fourierCurl u) := by
  let F := fun k ↦ coefficientVec (fun i ↦ mask k * outputFiber q u k i)
  have hb (k : Wavevector) : ‖F k‖ ≤ M * ‖frequencyVec q‖ * pairMajorant (fourierCurl u) q k := by
    change ‖mask k • (modeDot q (u k) • coefficientVec (u (q-k)))‖ ≤ _
    rw [norm_smul, norm_smul]
    calc
      _ ≤ (M * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec (q-k)‖) *
          ((‖frequencyVec q‖ * ‖coefficientVec (u k)‖) * ‖coefficientVec (u (q-k))‖) := by
        gcongr
        · exact hm k
        · exact norm_modeDot_le q (u k)
      _ = M * ‖frequencyVec q‖ *
          (‖coefficientVec (fourierCurl u k)‖ * ‖coefficientVec (fourierCurl u (q-k))‖) := by
        rw [norm_fourierCurl_eq u k (hd k), norm_fourierCurl_eq u (q-k) (hd (q-k))]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_product_le_pairMajorant (fourierCurl u) q k)
        (mul_nonneg hM (norm_nonneg _))
  have hsum := (summable_pairMajorant (fourierCurl u) hu q).mul_left (M * ‖frequencyVec q‖)
  have hn := hsum.of_nonneg_of_le (fun k ↦ norm_nonneg (F k)) hb
  have hF : Summable F := hn.of_norm
  have he : coefficientVec (weightedConvection mask u q) = ∑' k, F k := by
    ext i
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 ↦ ℂ) i).map_tsum hF).symm
  rw [he]
  apply (norm_tsum_le_tsum_norm hn).trans
  calc
    _ ≤ ∑' k, M * ‖frequencyVec q‖ * pairMajorant (fourierCurl u) q k := hn.tsum_le_tsum hb hsum
    _ = _ := by rw [tsum_mul_left, tsum_pairMajorant (fourierCurl u) hu q]

theorem norm_heat_subgridForce_le_energy {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (subgridForce (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * kineticEnergy u := by
  have hm (k : Wavevector) :
      ‖(multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel] using abs_multiplier_defect_le_one hν hσ k (q-k)
  have hb := norm_weightedConvection_le _ u 1 hm hu q
  change ‖coefficientVec (subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
    1 * ‖frequencyVec q‖ * kineticEnergy u at hb
  change ‖coefficientVec (lerayMode q _)‖ ≤ _
  apply (norm_lerayMode_le q _).trans
  change ‖(-unitTorusDerivativePhase) • coefficientVec (subgridConvection _ u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)

theorem norm_heat_subgridForce_le_enstrophy {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (subgridForce (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * (2 * ν * σ) * kineticEnergy (fourierCurl u) := by
  have hm (k : Wavevector) :
      ‖(multiplier ν σ q : ℂ) - (multiplier ν σ k : ℂ) * (multiplier ν σ (q-k) : ℂ)‖ ≤
        (2 * ν * σ) * (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ * ‖frequencyVec (q-k)‖ := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [add_sub_cancel] using abs_multiplier_defect_le_enstrophy_weight hν hσ k (q-k)
  have hb := norm_weightedConvection_le_enstrophy _ u (2 * ν * σ) q hm (by positivity) hd hu
  change ‖coefficientVec (subgridConvection (fun k ↦ (multiplier ν σ k : ℂ)) u q)‖ ≤
    (2 * ν * σ) * ‖frequencyVec q‖ * kineticEnergy (fourierCurl u) at hb
  change ‖coefficientVec (lerayMode q _)‖ ≤ _
  apply (norm_lerayMode_le q _).trans
  change ‖(-unitTorusDerivativePhase) • coefficientVec (subgridConvection _ u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)).trans_eq (by ring)

/-- Interpolation of the two bounds supplies the actual energy-enstrophy payer. -/
theorem norm_nonlinearCommutator_sq_le {ν σ : ℝ} (hν : 0 ≤ ν) (hσ : 0 ≤ σ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) :
    ‖coefficientVec (nonlinearCommutator ν σ u q)‖ ^ 2 ≤
      (2 * ν * σ) * ((2 * Real.pi) * ‖frequencyVec q‖) ^ 2 *
        (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  have he : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_coefficientEnergy u
      (InfiniteKineticCancellation.summable_amplitude u
        (summable_firstMoment_of_second u hu))
  have hw : Summable (fun k ↦ ‖coefficientVec (fourierCurl u k)‖ ^ 2) := by
    simpa only [norm_coefficientVec_sq] using InfiniteKineticCancellation.summable_curlEnergy u hu
  rw [nonlinearCommutator_eq_subgridForce hν hσ u hu, pow_two]
  have h₁ := norm_heat_subgridForce_le_energy hν hσ u he q
  have h₂ := norm_heat_subgridForce_le_enstrophy hν hσ u hd hw q
  have h := mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  exact h.trans_eq (by ring)

end Mettapedia.FluidDynamics.NavierStokes.FourierHeatCommutatorEnergy
