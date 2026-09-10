import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation

/-!
# All-input convection fibers controlled by kinetic energy

Square-summable velocity coefficients control each fixed-output convolution
fiber, without an input cutoff or an absolute Fourier gradient sum. The
same estimate controls sharp-filter subgrid forcing at a retained output.
Its output-frequency factor is explicit; no bound uniform over all output
frequencies or over a singular time is inferred.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.InfiniteConvectionEnergy

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevFiberEnvelope PancakeLowPressureBudget PancakeCoefficientLimitEquation
open PancakeIncomingLowSourceEnergy PancakeGalerkinKineticEnergy InfiniteFilteredEquation
open PancakeFixedOutputVelocityBound PancakeInfinitePressureCoefficients
open PancakeLocalInfiniteVelocity PancakeSobolevWeights PancakeSobolevVelocityRate
open PancakeConcreteSmoothCellCutoff

/-- The squared velocity `L²` norm, with no factor of one half. -/
def kineticEnergy (u : FourierVelocity) : ℝ := ∑' k, ‖coefficientVec (u k)‖ ^ 2

def pairMajorant (u : FourierVelocity) (q k : Wavevector) : ℝ :=
  (‖coefficientVec (u k)‖ ^ 2 + ‖coefficientVec (u (q-k))‖ ^ 2) / 2

theorem norm_product_le_pairMajorant (u : FourierVelocity) (q k : Wavevector) :
    ‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖ ≤ pairMajorant u q k := by
  dsimp only [pairMajorant]
  nlinarith [sq_nonneg (‖coefficientVec (u k)‖ - ‖coefficientVec (u (q-k))‖)]

theorem summable_pairMajorant (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    Summable (pairMajorant u q) :=
  (hu.add (hu.comp_injective (fun _ _ h ↦ sub_right_injective h))).div_const 2

theorem tsum_pairMajorant (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    (∑' k, pairMajorant u q k) = kineticEnergy u := by
  let e : Wavevector ≃ Wavevector :=
    { toFun := fun k ↦ q-k
      invFun := fun k ↦ q-k
      left_inv := by intro k; ext i; simp only [Pi.sub_apply]; ring
      right_inv := by intro k; ext i; simp only [Pi.sub_apply]; ring }
  have hs : Summable (fun k ↦ ‖coefficientVec (u (q-k))‖ ^ 2) :=
    hu.comp_injective (fun _ _ h ↦ sub_right_injective h)
  have he : (∑' k, ‖coefficientVec (u (q-k))‖ ^ 2) = kineticEnergy u :=
    e.tsum_eq (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)
  simp only [pairMajorant, tsum_div_const, hu.tsum_add hs, he]
  change (kineticEnergy u + kineticEnergy u) / 2 = kineticEnergy u
  ring

/-- An arbitrary bounded mask on an all-input convolution fiber. -/
def weightedConvection (sigma : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ ∑' k, sigma k * outputFiber q u k i

/-- A fixed-output estimate with constant one and no input-cardinality loss.
The derivative is on the output frequency, not on either input frequency. -/
theorem norm_weightedConvection_le (sigma : Wavevector → ℂ) (u : FourierVelocity)
    (M : ℝ) (hsigma : ∀ k, ‖sigma k‖ ≤ M)
    (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (weightedConvection sigma u q)‖ ≤
      M * ‖frequencyVec q‖ * kineticEnergy u := by
  have hM : 0 ≤ M := (norm_nonneg (sigma 0)).trans (hsigma 0)
  let F := fun k ↦ coefficientVec (fun i ↦ sigma k * outputFiber q u k i)
  have hb (k : Wavevector) : ‖F k‖ ≤ M * ‖frequencyVec q‖ * pairMajorant u q k := by
    change ‖sigma k • (modeDot q (u k) • coefficientVec (u (q-k)))‖ ≤ _
    rw [norm_smul, norm_smul]
    calc
      _ ≤ M * ((‖frequencyVec q‖ * ‖coefficientVec (u k)‖) *
          ‖coefficientVec (u (q-k))‖) := by
        gcongr
        · exact hsigma k
        · exact norm_modeDot_le q (u k)
      _ = M * ‖frequencyVec q‖ *
          (‖coefficientVec (u k)‖ * ‖coefficientVec (u (q-k))‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_product_le_pairMajorant u q k) (by positivity)
  have hm := (summable_pairMajorant u hu q).mul_left (M * ‖frequencyVec q‖)
  have hn := hm.of_nonneg_of_le (fun k ↦ norm_nonneg (F k)) hb
  have hF : Summable F := hn.of_norm
  have he : coefficientVec (weightedConvection sigma u q) = ∑' k, F k := by
    ext i
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 ↦ ℂ) i).map_tsum hF).symm
  rw [he]
  apply (norm_tsum_le_tsum_norm hn).trans
  calc
    _ ≤ ∑' k, M * ‖frequencyVec q‖ * pairMajorant u q k := hn.tsum_le_tsum hb hm
    _ = _ := by rw [tsum_mul_left, tsum_pairMajorant u hu q]

theorem norm_infiniteConvection_le_kineticEnergy (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    ‖coefficientVec (infiniteConvection u q)‖ ≤ ‖frequencyVec q‖ * kineticEnergy u := by
  have he : weightedConvection (fun _ ↦ 1) u q = infiniteConvection u q := by
    ext i
    simp [weightedConvection, infiniteConvection]
  have h := norm_weightedConvection_le (fun _ ↦ 1) u 1 (fun _ ↦ by simp) hu q
  simpa only [he, one_mul] using h

/-- Both-high feedback is bounded, not discarded. The bound depends on the
retained output frequency but not on the unresolved input frequencies. -/
theorem norm_subgridForce_sharp_le_kineticEnergy (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2))
    (q : Wavevector) (hq : q ∈ modes) :
    ‖coefficientVec (subgridForce (sharpFilter modes) u q)‖ ≤
      (2 * Real.pi) * ‖frequencyVec q‖ * kineticEnergy u := by
  have hm (k : Wavevector) :
      ‖sharpFilter modes q - sharpFilter modes k * sharpFilter modes (q-k)‖ ≤ 1 := by
    by_cases hk : k ∈ modes <;> by_cases hl : q-k ∈ modes <;>
      simp [sharpFilter, hq, hk, hl]
  have hb := norm_weightedConvection_le
    (fun k ↦ sharpFilter modes q - sharpFilter modes k * sharpFilter modes (q-k)) u 1 hm hu q
  change ‖coefficientVec (InfiniteFilteredEquation.subgridConvection (sharpFilter modes) u q)‖ ≤
    1 * ‖frequencyVec q‖ * kineticEnergy u at hb
  change ‖coefficientVec (lerayMode q _)‖ ≤ _
  apply (norm_lerayMode_le q _).trans
  change ‖(-PancakePeriodicVorticityEquation.unitTorusDerivativePhase) •
    coefficientVec (InfiniteFilteredEquation.subgridConvection (sharpFilter modes) u q)‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase]
  simpa only [one_mul, mul_assoc]
    using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * Real.pi)

/-- The actual pressure coefficients have the same constant-one kinetic
bound as their finite predecessors, now with infinitely many input modes. -/
theorem norm_infinitePressureCoeff_le_kineticEnergy (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2)) (q : Wavevector) :
    ‖infinitePressureCoeff u q‖ ≤ kineticEnergy u := by
  by_cases hq : q = 0
  · subst q
    rw [infinitePressureCoeff_zero, norm_zero]
    exact tsum_nonneg (fun _ ↦ sq_nonneg _)
  · have h := (norm_frequency_mul_pressure_le u q).trans
      (norm_infiniteConvection_le_kineticEnergy u hu q)
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (frequencyVec_ne_zero hq))).mp h

/-- Square summability is a conclusion for the constructed local solution.
The bound here is its known local Sobolev bound, not a global initial-energy
estimate. -/
theorem local_kineticEnergy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun k ↦ ‖coefficientVec (s.coefficients t k)‖ ^ 2) ∧
      kineticEnergy (s.coefficients t) ≤ B := by
  have hs := s.summable_sobolev t ht
  have hb (k : Wavevector) : ‖coefficientVec (s.coefficients t k)‖ ^ 2 ≤
      (weight k * amplitude (s.coefficients t) k) ^ 2 := by
    have hw : 1 ≤ weight k := by
      dsimp only [weight]
      nlinarith [norm_nonneg (frequencyVec k), sq_nonneg ‖frequencyVec k‖]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) hw) 2
  have hk := hs.1.of_nonneg_of_le (fun _ ↦ sq_nonneg _) hb
  exact ⟨hk, (hk.tsum_le_tsum hb hs.1).trans hs.2⟩

/-- Spatially uniform control of the retained subgrid force. The entire
output-cutoff cost is visible in the sum of frequency lengths. -/
theorem norm_reconstructed_subgridForce_le_kineticEnergy (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fun k ↦ ‖coefficientVec (u k)‖ ^ 2))
    (x : UnitAddTorus (Fin 3)) :
    ‖coefficientVec (finiteFourierReconstruction modes (subgridForce (sharpFilter modes) u) x)‖ ≤
      (2 * Real.pi) * (∑ q ∈ modes, ‖frequencyVec q‖) * kineticEnergy u := by
  have he : coefficientVec (finiteFourierReconstruction modes (subgridForce (sharpFilter modes) u) x) =
      ∑ q ∈ modes, UnitAddTorus.mFourier q x •
        coefficientVec (subgridForce (sharpFilter modes) u q) := by
    simp only [finiteFourierReconstruction, coefficientVec, WithLp.toLp_sum, WithLp.toLp_smul]
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ modes, (2 * Real.pi) * ‖frequencyVec q‖ * kineticEnergy u := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_smul, norm_mFourier_apply, one_mul]
      exact norm_subgridForce_sharp_le_kineticEnergy modes u hu q hq
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Application to the actual local solution, with square summability
discharged internally. This retains the finite output-cutoff cost. -/
theorem norm_local_reconstructed_subgridForce_le {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (modes : Finset Wavevector) (x : UnitAddTorus (Fin 3)) :
    ‖coefficientVec (finiteFourierReconstruction modes
      (subgridForce (sharpFilter modes) (s.coefficients t)) x)‖ ≤
      (2 * Real.pi) * (∑ q ∈ modes, ‖frequencyVec q‖) * B := by
  have h := local_kineticEnergy s t ht
  exact (norm_reconstructed_subgridForce_le_kineticEnergy modes _ h.1 x).trans
    (mul_le_mul_of_nonneg_left h.2 (by positivity))

end Mettapedia.FluidDynamics.NavierStokes.InfiniteConvectionEnergy
