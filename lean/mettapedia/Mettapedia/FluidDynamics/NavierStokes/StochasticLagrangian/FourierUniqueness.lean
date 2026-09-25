import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierDyadicBlockContinuation

/-!
# Uniqueness of the Fourier solutions

Two tame solutions of order at least seven with the same data agree on their
common interval. Let `w = c - d`. The convection difference at output mode
`q` is

```text
∑ₖ (q · wₖ) c_{q-k} + (q · dₖ) w_{q-k},
```

so both terms carry the output factor `|q|`. On a finite output set `F` the
truncated dissipation of `w` absorbs them, and the finite Young inequality
`ℓ¹ * ℓ² → ℓ²` bounds what is left by the full energy of `w`. No nonlinear
cancellation is needed:

```text
∑_{q∈F} |w_q(t)|² ≤ κ ∫₀ᵗ ∑_q |w_q|²,   κ = 9 (‖c‖²_{ℓ¹} + ‖d‖²_{ℓ¹}) / ν.
```

Taking the supremum over `F` and applying Grönwall's inequality with zero
initial value gives `w = 0`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierUniqueness

open scoped BigOperators Topology ComplexConjugate
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeHigherLocalVelocity PancakeGalerkinKineticEnergy PancakeLocalInfiniteVelocity
open PancakeHigherDerivativeMoments PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeSignedTransportEnergy PancakeLowPressureBudget PancakeHigherSobolevWindow
open PancakePeriodicVorticityEquation PancakeIncomingLowSourceEnergy PancakeBlockReality
open FourierTameTriad FourierContinuation FourierTameContinuation
open FourierVorticitySupContinuation FourierDyadicBlockContinuation FourierInfiniteTameRate

section Young

/-- The finite Young inequality `ℓ¹ * ℓ² → ℓ²` on finite input and output
sets. -/
theorem sum_sq_conv_le_finite (F G : Finset Wavevector) (a b : Wavevector → ℝ)
    (hb : ∀ k, 0 ≤ b k) {A : ℝ} (hA : ∀ H : Finset Wavevector, ∑ j ∈ H, a j ^ 2 ≤ A) :
    ∑ q ∈ F, (∑ k ∈ G, b k * a (q - k)) ^ 2 ≤ (∑ k ∈ G, b k) ^ 2 * A := by
  have hCS : ∀ q, (∑ k ∈ G, b k * a (q - k)) ^ 2 ≤
      (∑ k ∈ G, b k) * ∑ k ∈ G, b k * a (q - k) ^ 2 := by
    intro q
    have h := Finset.sum_mul_sq_le_sq_mul_sq G (fun k ↦ Real.sqrt (b k))
      (fun k ↦ Real.sqrt (b k) * a (q - k))
    have e1 : ∀ k, Real.sqrt (b k) * (Real.sqrt (b k) * a (q - k)) = b k * a (q - k) :=
      fun k ↦ by rw [← mul_assoc, Real.mul_self_sqrt (hb k)]
    have e2 : ∀ k, Real.sqrt (b k) ^ 2 = b k := fun k ↦ Real.sq_sqrt (hb k)
    have e3 : ∀ k, (Real.sqrt (b k) * a (q - k)) ^ 2 = b k * a (q - k) ^ 2 :=
      fun k ↦ by rw [mul_pow, e2]
    simpa only [e1, e2, e3] using h
  have hshift : ∀ k, ∑ q ∈ F, a (q - k) ^ 2 ≤ A := by
    intro k
    have hinj : Set.InjOn (fun q ↦ q - k) F := fun x _ y _ h ↦ by simpa using h
    rw [← Finset.sum_image (f := fun j ↦ a j ^ 2) hinj]
    exact hA _
  have hB0 : 0 ≤ ∑ k ∈ G, b k := Finset.sum_nonneg fun k _ ↦ hb k
  calc ∑ q ∈ F, (∑ k ∈ G, b k * a (q - k)) ^ 2
      ≤ ∑ q ∈ F, (∑ k ∈ G, b k) * ∑ k ∈ G, b k * a (q - k) ^ 2 :=
        Finset.sum_le_sum fun q _ ↦ hCS q
    _ = (∑ k ∈ G, b k) * ∑ k ∈ G, b k * ∑ q ∈ F, a (q - k) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ (∑ k ∈ G, b k) * ∑ k ∈ G, b k * A :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hshift k) (hb k)) hB0
    _ = (∑ k ∈ G, b k) ^ 2 * A := by
        rw [← Finset.sum_mul]
        ring

/-- The Young inequality with an infinite input sum. -/
theorem sum_sq_tsum_conv_le (F : Finset Wavevector) (a b : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hbs : Summable b) {A : ℝ}
    (hA : ∀ H : Finset Wavevector, ∑ j ∈ H, a j ^ 2 ≤ A) :
    ∑ q ∈ F, (∑' k, b k * a (q - k)) ^ 2 ≤ (∑' k, b k) ^ 2 * A := by
  have hA0 : 0 ≤ A := le_trans (by simp) (hA ∅)
  have hbound : ∀ j, a j ≤ Real.sqrt A := fun j ↦ by
    have h := hA {j}
    rw [Finset.sum_singleton] at h
    exact Real.le_sqrt_of_sq_le h
  have hs : ∀ q, Summable (fun k ↦ b k * a (q - k)) := fun q ↦
    (hbs.mul_right (Real.sqrt A)).of_nonneg_of_le (fun k ↦ mul_nonneg (hb k) (ha _))
      (fun k ↦ mul_le_mul_of_nonneg_left (hbound _) (hb k))
  have ht : Tendsto (fun G : Finset Wavevector ↦ ∑ q ∈ F, (∑ k ∈ G, b k * a (q - k)) ^ 2)
      atTop (𝓝 (∑ q ∈ F, (∑' k, b k * a (q - k)) ^ 2)) := by
    refine tendsto_finsetSum _ fun q _ ↦ ?_
    have h : Tendsto (fun G : Finset Wavevector ↦ ∑ k ∈ G, b k * a (q - k)) atTop
        (𝓝 (∑' k, b k * a (q - k))) := by
      simpa only [HasSum, SummationFilter.unconditional] using (hs q).hasSum
    exact h.pow 2
  refine le_of_tendsto' ht fun G ↦ (sum_sq_conv_le_finite F G a b hb hA).trans ?_
  have hG : ∑ k ∈ G, b k ≤ ∑' k, b k := hbs.sum_le_tsum G fun k _ ↦ hb k
  have hG0 : 0 ≤ ∑ k ∈ G, b k := Finset.sum_nonneg fun k _ ↦ hb k
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG0 hG 2) hA0

end Young

section Mode

/-- The difference of two fields. -/
def diff (c d : FourierVelocity) : FourierVelocity := fun k ↦ c k - d k

theorem modeDot_sub (q : Wavevector) (v v' : VelocityCoefficient) :
    modeDot q (v - v') = modeDot q v - modeDot q v' := by
  simp only [modeDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem outputFiber_sub (q : Wavevector) (c d : FourierVelocity) (k : Wavevector) (i : Fin 3) :
    outputFiber q c k i - outputFiber q d k i =
      modeDot q (diff c d k) * c (q - k) i + modeDot q (d k) * diff c d (q - k) i := by
  simp only [outputFiber, diff, modeDot_sub, Pi.sub_apply]
  ring

theorem amplitude_nonneg (u : FourierVelocity) (k : Wavevector) : 0 ≤ amplitude u k :=
  norm_nonneg _

theorem norm_component_le (v : VelocityCoefficient) (i : Fin 3) :
    ‖v i‖ ≤ ‖coefficientVec v‖ :=
  (norm_le_pi_norm v i).trans (PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean v)

theorem norm_outputFiber_sub_le (q : Wavevector) (c d : FourierVelocity) (k : Wavevector)
    (i : Fin 3) :
    ‖outputFiber q c k i - outputFiber q d k i‖ ≤
      ‖frequencyVec q‖ * (amplitude (diff c d) k * amplitude c (q - k) +
        amplitude d k * amplitude (diff c d) (q - k)) := by
  rw [outputFiber_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := norm_modeDot_le q (diff c d k)
  have h2 := norm_modeDot_le q (d k)
  have h3 := norm_component_le (c (q - k)) i
  have h4 := norm_component_le (diff c d (q - k)) i
  change ‖modeDot q (diff c d k)‖ ≤ ‖frequencyVec q‖ * amplitude (diff c d) k at h1
  change ‖modeDot q (d k)‖ ≤ ‖frequencyVec q‖ * amplitude d k at h2
  change ‖c (q - k) i‖ ≤ amplitude c (q - k) at h3
  change ‖diff c d (q - k) i‖ ≤ amplitude (diff c d) (q - k) at h4
  have hq := norm_nonneg (frequencyVec q)
  calc ‖modeDot q (diff c d k)‖ * ‖c (q - k) i‖ + ‖modeDot q (d k)‖ * ‖diff c d (q - k) i‖
      ≤ (‖frequencyVec q‖ * amplitude (diff c d) k) * amplitude c (q - k) +
          (‖frequencyVec q‖ * amplitude d k) * amplitude (diff c d) (q - k) :=
        add_le_add (mul_le_mul h1 h3 (norm_nonneg _) (mul_nonneg hq (amplitude_nonneg _ _)))
          (mul_le_mul h2 h4 (norm_nonneg _) (mul_nonneg hq (amplitude_nonneg _ _)))
    _ = _ := by ring

theorem lerayMode_sub (q : Wavevector) (v v' : VelocityCoefficient) :
    lerayMode q (v - v') = lerayMode q v - lerayMode q v' := by
  unfold lerayMode
  split_ifs with h
  · rfl
  · ext i
    simp only [Pi.sub_apply, modeDot_sub]
    ring

theorem viscous_sub (nu : ℝ) (c d : FourierVelocity) (q : Wavevector) :
    unitTorusViscousVorticityCoeff nu c q - unitTorusViscousVorticityCoeff nu d q =
      unitTorusViscousVorticityCoeff nu (diff c d) q := by
  simp only [unitTorusViscousVorticityCoeff, diff, smul_sub]

theorem hermitian_sub_right (u v v' : VelocityCoefficient) :
    coefficientHermitian u (v - v') = coefficientHermitian u v - coefficientHermitian u v' := by
  simp only [coefficientHermitian, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem abs_re_hermitian_phase_le (w X : VelocityCoefficient) {M : ℝ}
    (hX : ∀ i, ‖X i‖ ≤ M) :
    |(coefficientHermitian w ((-unitTorusDerivativePhase) • X)).re| ≤
      2 * Real.pi * (3 * ‖coefficientVec w‖ * M) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold coefficientHermitian
  refine (norm_sum_le _ _).trans ?_
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hX 0)
  have hterm : ∀ i : Fin 3, ‖conj (w i) * ((-unitTorusDerivativePhase) • X) i‖ ≤
      2 * Real.pi * (‖coefficientVec w‖ * M) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_conj, norm_neg,
      norm_derivativePhase]
    have hw := norm_component_le w i
    calc ‖w i‖ * (2 * Real.pi * ‖X i‖) ≤ ‖coefficientVec w‖ * (2 * Real.pi * M) := by
          gcongr
          exact hX i
      _ = 2 * Real.pi * (‖coefficientVec w‖ * M) := by ring
  calc ∑ i : Fin 3, ‖conj (w i) * ((-unitTorusDerivativePhase) • X) i‖
      ≤ ∑ _i : Fin 3, 2 * Real.pi * (‖coefficientVec w‖ * M) := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = 2 * Real.pi * (3 * ‖coefficientVec w‖ * M) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The per-mode rate of the difference.** The dissipation absorbs the whole
convection difference, leaving `(9 / 2ν) Y²`, where `|q| Y` bounds its
components. -/
theorem two_re_hermitian_rhs_sub_le (nu : ℝ) (hnu : 0 < nu) (c d : FourierVelocity)
    (q : Wavevector) (hw : modeDot q (diff c d q) = 0) {Y : ℝ}
    (hX : ∀ i, ‖infiniteConvection c q i - infiniteConvection d q i‖ ≤ ‖frequencyVec q‖ * Y) :
    2 * (coefficientHermitian (diff c d q)
        (infiniteVelocityRHS nu c q - infiniteVelocityRHS nu d q)).re ≤ 9 / (2 * nu) * Y ^ 2 := by
  have hsplit : infiniteVelocityRHS nu c q - infiniteVelocityRHS nu d q =
      lerayMode q ((-unitTorusDerivativePhase) • (infiniteConvection c q - infiniteConvection d q)) +
        unitTorusViscousVorticityCoeff nu (diff c d) q := by
    rw [← viscous_sub, smul_sub, lerayMode_sub]
    simp only [infiniteVelocityRHS]
    abel
  rw [hsplit, hermitian_add_right, Complex.add_re, hermitian_leray_right q _ _ hw,
    viscous_energy_pair, ← norm_frequencyVec_sq, ← norm_coefficientVec_sq]
  have hconv := abs_re_hermitian_phase_le (diff c d q)
    (infiniteConvection c q - infiniteConvection d q) (M := ‖frequencyVec q‖ * Y) hX
  set x := ‖frequencyVec q‖ * ‖coefficientVec (diff c d q)‖ with hx
  have hx0 : 0 ≤ x := by positivity
  have hre := (le_abs_self _).trans hconv
  have hbound : 2 * (2 * Real.pi * (3 * ‖coefficientVec (diff c d q)‖ *
      (‖frequencyVec q‖ * Y)) + -nu * (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 *
        ‖coefficientVec (diff c d q)‖ ^ 2) ≤ 9 / (2 * nu) * Y ^ 2 := by
    have hπ : 0 < Real.pi := Real.pi_pos
    have e : 2 * (2 * Real.pi * (3 * ‖coefficientVec (diff c d q)‖ *
        (‖frequencyVec q‖ * Y)) + -nu * (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 *
          ‖coefficientVec (diff c d q)‖ ^ 2) =
        12 * Real.pi * x * Y - 8 * Real.pi ^ 2 * nu * x ^ 2 := by
      rw [hx]
      ring
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (4 * Real.pi * nu * x - 3 * Y), mul_pos hπ hnu]
  linarith

end Mode

section Solutions

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}

/-- A tame solution of order at least seven restricts to a closed-interval
local solution on `[0, S]`, for any `S < T`, with a common third-moment
envelope. -/
theorem local_envelope_at (hm : 7 ≤ m) (c : TameSolutionOn nu m u₀ T) {S : ℝ} (hST : S < T) :
    ∃ B, ∃ s : LocalInfiniteVelocitySolution nu u₀ S B, s.coefficients = c.coefficients ∧
      ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
        ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k := by
  obtain ⟨B, hB⟩ := c.sobolev_local S hST
  obtain ⟨E, hE⟩ := c.order_local S hST
  refine ⟨B, restrictLocal c.toSolutionOn hST hB, rfl,
    fun k ↦ Real.sqrt E * latticeDecayWeight k,
    fun k ↦ mul_nonneg (Real.sqrt_nonneg E) (latticeDecayWeight_pos k).le,
    summable_latticeDecayWeight.mul_left _, fun t ht k ↦ ?_⟩
  exact orderMoment_le_latticeEnvelope 3 _ E
    (fun F ↦ (velocityEnergy_le_of_order_le (by omega) _ F).trans (hE t ht F)) k

theorem amplitude_le_moment (u : FourierVelocity) (k : Wavevector) :
    amplitude u k ≤ fourierMoment 3 u k := by
  have h := fourierMoment_mono u (by omega : 0 ≤ 3) k
  show ‖coefficientVec (u k)‖ ≤ fourierMoment 3 u k
  simpa only [fourierMoment, pow_zero, one_mul] using h

theorem amplitude_diff_le (c d : FourierVelocity) (k : Wavevector) :
    amplitude (diff c d) k ≤ amplitude c k + amplitude d k := by
  change ‖coefficientVec (c k - d k)‖ ≤ ‖coefficientVec (c k)‖ + ‖coefficientVec (d k)‖
  exact norm_sub_le (coefficientVec (c k)) (coefficientVec (d k))

theorem coefficientEnergy_diff_eq (c d : FourierVelocity) (k : Wavevector) :
    coefficientEnergy (diff c d k) = amplitude (diff c d) k ^ 2 :=
  (norm_coefficientVec_sq _).symm

/-- **Uniqueness.** Two tame solutions of order at least seven with the same
data agree at every time of their common interval. -/
theorem TameSolutionOn.coefficients_eq (hm : 7 ≤ m) (hnu : 0 < nu)
    (c d : TameSolutionOn nu m u₀ T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    c.coefficients t = d.coefficients t := by
  set S := (t + T) / 2 with hSdef
  have htS : t < S := by linarith [ht.2]
  have hST : S < T := by linarith [ht.2]
  have hS0 : 0 < S := lt_of_le_of_lt ht.1 htS
  obtain ⟨Bc, sc, hsc, gc, hgc, hSc, huc⟩ := local_envelope_at hm c hST
  obtain ⟨Bd, sd, hsd, gd, hgd, hSd, hud⟩ := local_envelope_at hm d hST
  let w : ℝ → FourierVelocity := fun τ ↦ diff (c.coefficients τ) (d.coefficients τ)
  -- amplitude bounds on `[0, S]`
  have hac : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, amplitude (c.coefficients τ) k ≤ gc k := by
    intro τ hτ k
    rw [← hsc]
    exact (amplitude_le_moment _ k).trans (huc τ hτ k)
  have had : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, amplitude (d.coefficients τ) k ≤ gd k := by
    intro τ hτ k
    rw [← hsd]
    exact (amplitude_le_moment _ k).trans (hud τ hτ k)
  set Mc := ∑' k, gc k with hMc
  set Md := ∑' k, gd k with hMd
  have hMc0 : 0 ≤ Mc := tsum_nonneg hgc
  have hMd0 : 0 ≤ Md := tsum_nonneg hgd
  have hgcle : ∀ k, gc k ≤ Mc := fun k ↦ hSc.le_tsum k fun j _ ↦ hgc j
  have hgdle : ∀ k, gd k ≤ Md := fun k ↦ hSd.le_tsum k fun j _ ↦ hgd j
  -- the energy envelope of the difference
  let env : Wavevector → ℝ := fun k ↦ (Mc + Md) * (gc k + gd k)
  have henv : Summable env := (hSc.add hSd).mul_left _
  have hwk : ∀ τ ∈ Icc (0 : ℝ) S, ∀ k, coefficientEnergy (w τ k) ≤ env k := by
    intro τ hτ k
    rw [coefficientEnergy_diff_eq]
    have h1 := (amplitude_diff_le _ _ k).trans (add_le_add (hac τ hτ k) (had τ hτ k))
    have h0 : 0 ≤ amplitude (diff (c.coefficients τ) (d.coefficients τ)) k := norm_nonneg _
    calc amplitude (diff (c.coefficients τ) (d.coefficients τ)) k ^ 2
        ≤ (gc k + gd k) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ (Mc + Md) * (gc k + gd k) := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (add_le_add (hgcle k) (hgdle k))
            (add_nonneg (hgc k) (hgd k))
  have hE0 : ∀ τ k, 0 ≤ coefficientEnergy (w τ k) := fun τ k ↦ by
    rw [coefficientEnergy_diff_eq]
    positivity
  -- the full energy of the difference
  let Z : ℝ → ℝ := fun τ ↦ ∑' k, coefficientEnergy (w τ k)
  have hZs : ∀ τ ∈ Icc (0 : ℝ) S, Summable (fun k ↦ coefficientEnergy (w τ k)) :=
    fun τ hτ ↦ henv.of_nonneg_of_le (hE0 τ) (hwk τ hτ)
  have hZ0 : ∀ τ, 0 ≤ Z τ := fun τ ↦ tsum_nonneg (hE0 τ)
  have hZc : ContinuousOn Z (Icc 0 S) := by
    refine continuousOn_iff_continuous_domRestrict.mpr ?_
    refine continuous_tsum (f := fun k (τ : Icc (0 : ℝ) S) ↦ coefficientEnergy (w τ k))
      (fun k ↦ ?_) henv (fun k τ ↦ ?_)
    · have hc (i : Fin 3) : Continuous (fun τ : Icc (0 : ℝ) S ↦ w τ k i) :=
        ((c.continuous k i).sub (d.continuous k i)).comp continuous_subtype_val
      show Continuous fun τ : Icc (0 : ℝ) S ↦ ∑ i : Fin 3, Complex.normSq (w τ k i)
      exact continuous_finsetSum _ fun i _ ↦ Complex.continuous_normSq.comp (hc i)
    · rw [Real.norm_eq_abs, abs_of_nonneg (hE0 _ _)]
      exact hwk τ τ.2 k
  have hsumle : ∀ τ ∈ Icc (0 : ℝ) S, ∀ H : Finset Wavevector,
      ∑ j ∈ H, amplitude (w τ) j ^ 2 ≤ Z τ := by
    intro τ hτ H
    calc ∑ j ∈ H, amplitude (w τ) j ^ 2 = ∑ j ∈ H, coefficientEnergy (w τ j) :=
          Finset.sum_congr rfl fun j _ ↦ (coefficientEnergy_diff_eq _ _ j).symm
      _ ≤ Z τ := (hZs τ hτ).sum_le_tsum H fun j _ ↦ hE0 τ j
  -- the rate bound at interior times
  set κ := 9 / nu * (Mc ^ 2 + Md ^ 2) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hrate : ∀ τ ∈ Ioo (0 : ℝ) S, ∀ F : Finset Wavevector,
      orderVelocityRate 0 F (w τ)
        (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
          infiniteVelocityRHS nu (d.coefficients τ) q) ≤ κ * Z τ := by
    intro τ hτ F
    have hτS : τ ∈ Icc (0 : ℝ) S := Ioo_subset_Icc_self hτ
    set cτ := c.coefficients τ
    set dτ := d.coefficients τ
    have hcs : ∀ q i, Summable (fun k ↦ outputFiber q cτ k i) := by
      intro q i
      have h := sc.summable_convection τ hτS q i
      rwa [hsc] at h
    have hds : ∀ q i, Summable (fun k ↦ outputFiber q dτ k i) := by
      intro q i
      have h := sd.summable_convection τ hτS q i
      rwa [hsd] at h
    let Y1 : Wavevector → ℝ := fun q ↦ ∑' k, amplitude cτ k * amplitude (w τ) (q - k)
    let Y2 : Wavevector → ℝ := fun q ↦ ∑' k, amplitude dτ k * amplitude (w τ) (q - k)
    have hwb : ∀ j, amplitude (w τ) j ≤ Real.sqrt (Z τ) := fun j ↦ by
      have h := hsumle τ hτS {j}
      rw [Finset.sum_singleton] at h
      exact Real.le_sqrt_of_sq_le h
    have hcl1 : Summable (fun k ↦ amplitude cτ k) :=
      hSc.of_nonneg_of_le (fun k ↦ norm_nonneg _) (hac τ hτS)
    have hdl1 : Summable (fun k ↦ amplitude dτ k) :=
      hSd.of_nonneg_of_le (fun k ↦ norm_nonneg _) (had τ hτS)
    have hs1 : ∀ q, Summable (fun k ↦ amplitude cτ k * amplitude (w τ) (q - k)) := fun q ↦
      (hcl1.mul_right (Real.sqrt (Z τ))).of_nonneg_of_le (fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _))
        (fun k ↦ mul_le_mul_of_nonneg_left (hwb _) (norm_nonneg _))
    have hs2 : ∀ q, Summable (fun k ↦ amplitude dτ k * amplitude (w τ) (q - k)) := fun q ↦
      (hdl1.mul_right (Real.sqrt (Z τ))).of_nonneg_of_le (fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _))
        (fun k ↦ mul_le_mul_of_nonneg_left (hwb _) (norm_nonneg _))
    have hY1 : ∀ q, 0 ≤ Y1 q := fun q ↦
      tsum_nonneg fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _)
    have hY2 : ∀ q, 0 ≤ Y2 q := fun q ↦
      tsum_nonneg fun k ↦ mul_nonneg (amplitude_nonneg _ _) (amplitude_nonneg _ _)
    -- the component bound for the convection difference
    have hX : ∀ q i, ‖infiniteConvection cτ q i - infiniteConvection dτ q i‖ ≤
        ‖frequencyVec q‖ * (Y1 q + Y2 q) := by
      intro q i
      have hfs : Summable (fun k ↦ ‖frequencyVec q‖ * (amplitude (w τ) k * amplitude cτ (q - k) +
          amplitude dτ k * amplitude (w τ) (q - k))) := by
        refine Summable.mul_left _ (Summable.add ?_ (hs2 q))
        have h := (Equiv.subLeft q).summable_iff.mpr (hs1 q)
        refine h.congr fun k ↦ ?_
        simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel]
        ring
      have hdiff : infiniteConvection cτ q i - infiniteConvection dτ q i =
          ∑' k, (outputFiber q cτ k i - outputFiber q dτ k i) := by
        simp only [infiniteConvection]
        exact ((hcs q i).tsum_sub (hds q i)).symm
      rw [hdiff]
      refine (norm_tsum_le_tsum_norm ?_).trans ?_
      · exact hfs.of_nonneg_of_le (fun k ↦ norm_nonneg _)
          (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i)
      · refine (hfs.of_nonneg_of_le (fun k ↦ norm_nonneg _)
            (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i)).tsum_le_tsum
            (fun k ↦ norm_outputFiber_sub_le q cτ dτ k i) hfs |>.trans ?_
        rw [tsum_mul_left]
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)
        have hr : (∑' k, amplitude (w τ) k * amplitude cτ (q - k)) = Y1 q := by
          rw [← (Equiv.subLeft q).tsum_eq]
          refine tsum_congr fun k ↦ ?_
          simp only [Equiv.subLeft_apply, sub_sub_cancel]
          ring
        have hsA : Summable (fun k ↦ amplitude (w τ) k * amplitude cτ (q - k)) := by
          have h := (Equiv.subLeft q).summable_iff.mpr (hs1 q)
          refine h.congr fun k ↦ ?_
          simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel]
          ring
        rw [Summable.tsum_add hsA (hs2 q), hr]
    -- sum over the output set
    have hmode : ∀ q ∈ F, 2 * (coefficientHermitian (w τ q)
        (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re ≤
          9 / (2 * nu) * (Y1 q + Y2 q) ^ 2 := by
      intro q _
      have h1 : modeDot q (cτ q) = 0 := c.transverse τ q
      have h2 : modeDot q (dτ q) = 0 := d.transverse τ q
      have hw : modeDot q (diff cτ dτ q) = 0 := by
        simp only [diff, modeDot_sub, h1, h2, sub_zero]
      exact two_re_hermitian_rhs_sub_le nu hnu cτ dτ q hw (hX q)
    have hyoung1 := sum_sq_tsum_conv_le F (amplitude (w τ)) (amplitude cτ)
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hcl1 (hsumle τ hτS)
    have hyoung2 := sum_sq_tsum_conv_le F (amplitude (w τ)) (amplitude dτ)
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) hdl1 (hsumle τ hτS)
    have hMc' : (∑' k, amplitude cτ k) ≤ Mc :=
      hcl1.tsum_le_tsum (hac τ hτS) hSc
    have hMd' : (∑' k, amplitude dτ k) ≤ Md :=
      hdl1.tsum_le_tsum (had τ hτS) hSd
    have hc0 : 0 ≤ ∑' k, amplitude cτ k := tsum_nonneg fun k ↦ norm_nonneg _
    have hd0 : 0 ≤ ∑' k, amplitude dτ k := tsum_nonneg fun k ↦ norm_nonneg _
    have hZτ := hZ0 τ
    have hsq : ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 ≤ 2 * (Mc ^ 2 + Md ^ 2) * Z τ := by
      calc ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 ≤ ∑ q ∈ F, (2 * Y1 q ^ 2 + 2 * Y2 q ^ 2) :=
            Finset.sum_le_sum fun q _ ↦ by nlinarith [sq_nonneg (Y1 q - Y2 q)]
        _ = 2 * ∑ q ∈ F, Y1 q ^ 2 + 2 * ∑ q ∈ F, Y2 q ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * ((∑' k, amplitude cτ k) ^ 2 * Z τ) + 2 * ((∑' k, amplitude dτ k) ^ 2 * Z τ) := by
            gcongr
        _ ≤ 2 * (Mc ^ 2 * Z τ) + 2 * (Md ^ 2 * Z τ) := by
            gcongr
        _ = 2 * (Mc ^ 2 + Md ^ 2) * Z τ := by ring
    have hrw : orderVelocityRate 0 F (w τ)
        (fun q ↦ infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q) =
          ∑ q ∈ F, 2 * (coefficientHermitian (w τ q)
            (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re := by
      simp only [orderVelocityRate, orderWeight, pow_zero, one_pow, one_mul, Finset.mul_sum]
    rw [hrw]
    calc ∑ q ∈ F, 2 * (coefficientHermitian (w τ q)
          (infiniteVelocityRHS nu cτ q - infiniteVelocityRHS nu dτ q)).re
        ≤ ∑ q ∈ F, 9 / (2 * nu) * (Y1 q + Y2 q) ^ 2 := Finset.sum_le_sum hmode
      _ = 9 / (2 * nu) * ∑ q ∈ F, (Y1 q + Y2 q) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 9 / (2 * nu) * (2 * (Mc ^ 2 + Md ^ 2) * Z τ) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = κ * Z τ := by
          rw [hκ]
          field_simp
  -- the truncated energies stay below the integral
  have htrunc : ∀ F : Finset Wavevector, ∀ τ ∈ Icc (0 : ℝ) S,
      velocityEnergy 0 F (w τ) ≤ κ * ∫ r in (0 : ℝ)..τ, Z r := by
    intro F
    let φ : ℝ → ℝ := fun τ ↦ velocityEnergy 0 F (w τ) - κ * ∫ r in (0 : ℝ)..τ, Z r
    have hint : IntegrableOn Z (uIcc 0 S) := by
      rw [uIcc_of_le hS0.le]
      exact hZc.integrableOn_Icc
    have hprim : ContinuousOn (fun τ ↦ ∫ r in (0 : ℝ)..τ, Z r) (Icc 0 S) := by
      have h := intervalIntegral.continuousOn_primitive_interval hint
      rwa [uIcc_of_le hS0.le] at h
    have hwc : ∀ q i, Continuous (fun τ ↦ w τ q i) := fun q i ↦
      (c.continuous q i).sub (d.continuous q i)
    have hφc : ContinuousOn φ (Icc 0 S) :=
      (continuous_velocityEnergy_along 0 F hwc).continuousOn.sub (hprim.const_smul κ)
    have hder : ∀ τ ∈ Ioo (0 : ℝ) S, HasDerivAt φ
        (orderVelocityRate 0 F (w τ)
          (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
            infiniteVelocityRHS nu (d.coefficients τ) q) - κ * Z τ) τ := by
      intro τ hτ
      have hτT : τ ∈ Ioo (0 : ℝ) T := ⟨hτ.1, hτ.2.trans hST⟩
      have hE := hasDerivAt_velocityEnergy 0 F w
        (fun q ↦ infiniteVelocityRHS nu (c.coefficients τ) q -
          infiniteVelocityRHS nu (d.coefficients τ) q) τ
        (fun q _ i ↦ (c.equation τ hτT q i).sub (d.equation τ hτT q i))
      have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτ.2.le
      have hi : IntervalIntegrable Z volume 0 τ :=
        (hZc.mono hsub).intervalIntegrable_of_Icc hτ.1.le
      have hm : StronglyMeasurableAtFilter Z (𝓝 τ) :=
        (hZc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
      have hcz : ContinuousAt Z τ := hZc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
      exact hE.sub ((intervalIntegral.integral_hasDerivAt_right hi hm hcz).const_mul κ)
    have hanti : AntitoneOn φ (Icc 0 S) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S) hφc
      · intro τ hτ
        rw [interior_Icc] at hτ
        exact (hder τ hτ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hder τ hτ).deriv]
        linarith [hrate τ hτ F]
    intro τ hτ
    have h := hanti ⟨le_rfl, hS0.le⟩ hτ hτ.1
    have h0 : φ 0 = 0 := by
      have hw0 : w 0 = fun _ ↦ 0 := by
        funext k
        simp only [w, diff, c.initial, d.initial, sub_self]
      simp only [φ, hw0, intervalIntegral.integral_same, mul_zero, sub_zero]
      simp [velocityEnergy_eq, coefficientEnergy]
    change velocityEnergy 0 F (w τ) - κ * ∫ r in (0 : ℝ)..τ, Z r ≤ φ 0 at h
    linarith
  -- the full energy obeys the same bound, and Grönwall closes it
  have hZle : ∀ τ ∈ Icc (0 : ℝ) S, Z τ ≤ 0 + κ * ∫ r in (0 : ℝ)..τ, 1 * Z r := by
    intro τ hτ
    simp only [zero_add, one_mul]
    refine Real.tsum_le_of_sum_le (hE0 τ) fun H ↦ ?_
    have h := htrunc H τ hτ
    simpa only [velocityEnergy_eq, orderWeight, pow_zero, one_pow, one_mul] using h
  have hG := le_mul_exp_of_le_add_integral hS0.le hκ0 hZc continuousOn_const
    (fun _ _ ↦ zero_le_one) hZle
  have hZt : Z t ≤ 0 := by
    have hG' := le_mul_exp_of_le_add_integral ht.1 hκ0 (hZc.mono (Icc_subset_Icc le_rfl htS.le))
      continuousOn_const (fun _ _ ↦ zero_le_one)
      (fun τ hτ ↦ hZle τ (Icc_subset_Icc le_rfl htS.le hτ))
    simpa only [zero_mul] using hG'
  have hZt0 : Z t = 0 := le_antisymm hZt (hZ0 t)
  have htS' : t ∈ Icc (0 : ℝ) S := ⟨ht.1, htS.le⟩
  have hs0 : HasSum (fun k ↦ coefficientEnergy (w t k)) 0 := by
    rw [← hZt0]
    exact (hZs t htS').hasSum
  have hk : ∀ k, coefficientEnergy (w t k) = 0 :=
    fun k ↦ congrFun ((hasSum_zero_iff_of_nonneg (hE0 t)).mp hs0) k
  funext k
  have h := hk k
  rw [coefficientEnergy_diff_eq, sq_eq_zero_iff] at h
  have h' : coefficientVec (c.coefficients t k - d.coefficients t k) = 0 := norm_eq_zero.mp h
  have h'' : WithLp.toLp 2 (c.coefficients t k) = WithLp.toLp 2 (d.coefficients t k) := by
    have h3 : coefficientVec (c.coefficients t k) - coefficientVec (d.coefficients t k) = 0 := by
      simpa [coefficientVec] using h'
    exact sub_eq_zero.mp h3
  exact WithLp.toLp_injective 2 h''

end Solutions

end Mettapedia.FluidDynamics.NavierStokes.FourierUniqueness
