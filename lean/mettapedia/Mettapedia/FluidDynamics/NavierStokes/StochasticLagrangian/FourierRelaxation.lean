import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialTheorems
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DyadicPancakeClosure
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierTime

/-!
# The transported dyadic relaxation inequality for the Fourier solutions

Mode by mode the Fourier system is a damped equation

```text
ċ_k = -4π²ν|k|² c_k + N_k,   N_k = P_k(-2πi conv_k),
```

so Duhamel's formula bounds the time integral of `|c_k|` by the initial
coefficient plus the time integral of the source, divided by the damping.
Summing over the dyadic shells `2^q ≤ |k| < 2^(q+1)`, `q ≥ Q`, with the
Wiener (`ℓ¹`) norm of the vorticity coefficients on each shell, gives the
relaxation inequality of the pancake route for actual tame solutions:

```text
∫₀ᴴ W_Q(t) dt ≤ R + ∫₀ᴴ S(t) dt,
```

where `W_Q` dominates the block sum `D_Q = ∑_{q ≥ Q} ‖Δ_q ω‖_∞` used by the
continuation theorem, `R` depends only on the data, and the source `S` is the
weighted Wiener norm of the vorticity nonlinearity over the high shells. Any
split of `S` into pancake, coercive and residual shares therefore realizes the
route's relaxation data on actual solutions, and sector estimates for that
split with gains summing below one, with constants uniform on bounded
horizons, give the official periodic statement.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierRelaxation

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeHigherSobolevVelocityRate
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
open PancakeGalerkinKineticEnergy PancakeSobolevVelocityRate PancakeArbitraryDataBlocks
open PancakeInfiniteFourierTime PancakeInfinitePressureCoefficients PancakeIndexedFourierMoments
open PancakePeriodicVorticityEquation
open FourierTimeRegularity FourierTameContinuation FourierDyadicBlockContinuation
open FourierRegularityEquivalence FourierGlobalSolution FourierSpatialCalculus
open FourierInitialData FourierOfficialTheorems OfficialPeriodicProblem

section Duhamel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The primitive `∫₀ᵗ e^{ls} ‖g s‖ ds`. -/
def primitive (l : ℝ) (g : ℝ → E) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.exp (l * s) * ‖g s‖

/-- The damped primitive `e^{-lt} ∫₀ᵗ e^{ls} ‖g s‖ ds`. -/
def damped (l : ℝ) (g : ℝ → E) (t : ℝ) : ℝ := Real.exp (-(l * t)) * primitive l g t

theorem hasDerivAt_exp_mul (l t : ℝ) :
    HasDerivAt (fun τ ↦ Real.exp (l * τ)) (Real.exp (l * t) * l) t := by
  simpa using ((hasDerivAt_id' t).const_mul l).exp

theorem hasDerivAt_exp_neg_mul (l t : ℝ) :
    HasDerivAt (fun τ ↦ Real.exp (-(l * τ))) (Real.exp (-(l * t)) * (-l)) t := by
  simpa using ((hasDerivAt_id' t).const_mul l).neg.exp

theorem exp_neg_mul_exp (l t : ℝ) : Real.exp (-(l * t)) * Real.exp (l * t) = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem integral_exp_neg_le {l H : ℝ} (hl : 0 < l) :
    ∫ t in (0 : ℝ)..H, Real.exp (-(l * t)) ≤ 1 / l := by
  have hl' : l ≠ 0 := hl.ne'
  have hd : ∀ t ∈ uIcc (0 : ℝ) H, HasDerivAt (fun t ↦ Real.exp (-(l * t)) * (-1 / l))
      (Real.exp (-(l * t))) t := by
    intro t _
    refine ((hasDerivAt_exp_neg_mul l t).mul_const (-1 / l)).congr_deriv ?_
    rw [mul_assoc, neg_div, neg_mul_neg, mul_one_div, div_self hl', mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, neg_div]
  have h0 := mul_pos (Real.exp_pos (-(l * H))) (one_div_pos.mpr hl)
  linarith

/-- **Duhamel's bound.** -/
theorem exp_mul_norm_le {f g : ℝ → E} {l H : ℝ}
    (hf : ContinuousOn f (Icc 0 H)) (hg : ContinuousOn g (Icc 0 H))
    (hd : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt f (-(l • f t) + g t) t) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) H) :
    Real.exp (l * t) * ‖f t‖ ≤ ‖f 0‖ + primitive l g t := by
  have hF : ∀ τ ∈ Ioo (0 : ℝ) t, HasDerivAt (fun τ ↦ Real.exp (l * τ) • f τ)
      (Real.exp (l * τ) • g τ) τ := by
    intro τ hτ
    have h : HasDerivAt (fun τ ↦ Real.exp (l * τ) • f τ)
        (Real.exp (l * τ) • (-(l • f τ) + g τ) + (Real.exp (l * τ) * l) • f τ) τ :=
      (hasDerivAt_exp_mul l τ).smul (hd τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    refine h.congr_deriv ?_
    rw [smul_add, smul_neg, smul_smul]
    abel
  have hec : Continuous (fun τ : ℝ ↦ Real.exp (l * τ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcont : ContinuousOn (fun τ ↦ Real.exp (l * τ) • f τ) (Icc 0 t) :=
    hec.continuousOn.smul (hf.mono (Icc_subset_Icc le_rfl ht.2))
  have hint : IntervalIntegrable (fun τ ↦ Real.exp (l * τ) • g τ) volume 0 t :=
    (hec.continuousOn.smul (hg.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hF hint
  have e : Real.exp (l * t) • f t = (∫ τ in (0 : ℝ)..t, Real.exp (l * τ) • g τ) + f 0 := by
    have := sub_eq_iff_eq_add.mp hftc.symm
    simpa using this
  calc Real.exp (l * t) * ‖f t‖ = ‖Real.exp (l * t) • f t‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ = ‖(∫ τ in (0 : ℝ)..t, Real.exp (l * τ) • g τ) + f 0‖ := by rw [e]
    _ ≤ ‖∫ τ in (0 : ℝ)..t, Real.exp (l * τ) • g τ‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ (∫ τ in (0 : ℝ)..t, ‖Real.exp (l * τ) • g τ‖) + ‖f 0‖ :=
        add_le_add (intervalIntegral.norm_integral_le_integral_norm ht.1) le_rfl
    _ = ‖f 0‖ + primitive l g t := by
        rw [add_comm]
        congr 1
        refine intervalIntegral.integral_congr fun s _ ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **The integrated Duhamel bound.** -/
theorem integral_norm_le_duhamel {f g : ℝ → E} {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hf : ContinuousOn f (Icc 0 H)) (hg : ContinuousOn g (Icc 0 H))
    (hd : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt f (-(l • f t) + g t) t) :
    ∫ t in (0 : ℝ)..H, ‖f t‖ ≤ (‖f 0‖ + ∫ t in (0 : ℝ)..H, ‖g t‖) / l := by
  have hec : Continuous (fun τ : ℝ ↦ Real.exp (l * τ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have henc : Continuous (fun τ : ℝ ↦ Real.exp (-(l * τ))) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have hgn : ContinuousOn (fun s ↦ Real.exp (l * s) * ‖g s‖) (Icc 0 H) :=
    hec.continuousOn.mul hg.norm
  have hPc : ContinuousOn (primitive l g) (Icc 0 H) := by
    have h_int : IntegrableOn (fun s ↦ Real.exp (l * s) * ‖g s‖) (uIcc 0 H) volume := by
      rw [uIcc_of_le hH]
      exact hgn.integrableOn_Icc
    have h := intervalIntegral.continuousOn_primitive_interval h_int
    rw [uIcc_of_le hH] at h
    exact h
  have hGc : ContinuousOn (damped l g) (Icc 0 H) := henc.continuousOn.mul hPc
  have hpt : ∀ t ∈ Icc (0 : ℝ) H, ‖f t‖ ≤ Real.exp (-(l * t)) * ‖f 0‖ + damped l g t := by
    intro t ht
    have h := exp_mul_norm_le hf hg hd ht
    have hpos := Real.exp_pos (-(l * t))
    calc ‖f t‖ = Real.exp (-(l * t)) * (Real.exp (l * t) * ‖f t‖) := by
          rw [← mul_assoc, exp_neg_mul_exp, one_mul]
      _ ≤ Real.exp (-(l * t)) * (‖f 0‖ + primitive l g t) := mul_le_mul_of_nonneg_left h hpos.le
      _ = _ := by unfold damped; ring
  have hbc : ContinuousOn (fun t ↦ Real.exp (-(l * t)) * ‖f 0‖ + damped l g t) (Icc 0 H) :=
    (henc.continuousOn.mul continuousOn_const).add hGc
  have h1 : ∫ t in (0 : ℝ)..H, ‖f t‖ ≤
      ∫ t in (0 : ℝ)..H, (Real.exp (-(l * t)) * ‖f 0‖ + damped l g t) :=
    intervalIntegral.integral_mono_on hH (hf.norm.intervalIntegrable_of_Icc hH)
      (hbc.intervalIntegrable_of_Icc hH) hpt
  have hi1 : IntervalIntegrable (fun t ↦ Real.exp (-(l * t)) * ‖f 0‖) volume 0 H :=
    (henc.continuousOn.mul continuousOn_const).intervalIntegrable_of_Icc hH
  have hi2 : IntervalIntegrable (damped l g) volume 0 H := hGc.intervalIntegrable_of_Icc hH
  have h2 : ∫ t in (0 : ℝ)..H, (Real.exp (-(l * t)) * ‖f 0‖ + damped l g t) =
      (∫ t in (0 : ℝ)..H, Real.exp (-(l * t))) * ‖f 0‖ + ∫ t in (0 : ℝ)..H, damped l g t := by
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const]
  have hGd : ∀ t ∈ Ioo (0 : ℝ) H, HasDerivAt (damped l g) (-(l * damped l g t) + ‖g t‖) t := by
    intro t ht
    have hPd : HasDerivAt (primitive l g) (Real.exp (l * t) * ‖g t‖) t :=
      intervalIntegral.integral_hasDerivAt_right
        ((hgn.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
        ((hgn.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
        ((hgn.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds ht))
    have h : HasDerivAt (damped l g) (Real.exp (-(l * t)) * (-l) * primitive l g t +
        Real.exp (-(l * t)) * (Real.exp (l * t) * ‖g t‖)) t :=
      (hasDerivAt_exp_neg_mul l t).mul hPd
    refine h.congr_deriv ?_
    have he : Real.exp (-(l * t)) * (Real.exp (l * t) * ‖g t‖) = ‖g t‖ := by
      rw [← mul_assoc, exp_neg_mul_exp, one_mul]
    rw [he]
    unfold damped
    ring
  have hi3 : IntervalIntegrable (fun t ↦ -(l * damped l g t)) volume 0 H :=
    (continuousOn_const.mul hGc).neg.intervalIntegrable_of_Icc hH
  have hi4 : IntervalIntegrable (fun t ↦ ‖g t‖) volume 0 H := hg.norm.intervalIntegrable_of_Icc hH
  have hGint : IntervalIntegrable (fun t ↦ -(l * damped l g t) + ‖g t‖) volume 0 H := hi3.add hi4
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hH hGc hGd hGint
  have hG0 : damped l g 0 = 0 := by simp [damped, primitive]
  have hGH : 0 ≤ damped l g H :=
    mul_nonneg (Real.exp_pos _).le (intervalIntegral.integral_nonneg hH fun s _ ↦ by positivity)
  rw [intervalIntegral.integral_add hi3 hi4, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, hG0, sub_zero] at hftc
  have hI := integral_exp_neg_le (H := H) hl
  have hf0 : 0 ≤ ‖f 0‖ := norm_nonneg _
  have hG : ∫ t in (0 : ℝ)..H, damped l g t ≤ (∫ t in (0 : ℝ)..H, ‖g t‖) / l := by
    rw [le_div_iff₀ hl]
    linarith
  calc ∫ t in (0 : ℝ)..H, ‖f t‖ ≤ _ := h1
    _ = _ := h2
    _ ≤ (1 / l) * ‖f 0‖ + (∫ t in (0 : ℝ)..H, ‖g t‖) / l :=
        add_le_add (mul_le_mul_of_nonneg_right hI hf0) hG
    _ = _ := by ring

end Duhamel

section Modes

/-- The damping rate `4π²ν|k|²` of the `k`-th mode. -/
def damping (nu : ℝ) (k : Wavevector) : ℝ := 4 * Real.pi ^ 2 * nu * ‖frequencyVec k‖ ^ 2

/-- The nonlinear part of the right-hand side: the Leray projection of the
phased convection. -/
def nonlinear (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  nonlinearMap q (conv u u q)

theorem damping_pos {nu : ℝ} (hnu : 0 < nu) {k : Wavevector} (hk : k ≠ 0) : 0 < damping nu k := by
  have h1 : 0 < ‖frequencyVec k‖ := by linarith [one_le_norm_frequencyVec hk]
  unfold damping
  exact mul_pos (mul_pos (by positivity) hnu) (pow_pos h1 2)

theorem modeSquare_eq (q : Wavevector) : modeSquare q = ((‖frequencyVec q‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_frequencyVec_sq]
  simp [modeSquare, sq, Complex.ofReal_sum]

theorem viscous_eq (nu : ℝ) (q : Wavevector) :
    (nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q = ((-(damping nu q) : ℝ) : ℂ) := by
  rw [modeSquare_eq, unitTorusDerivativePhase, damping]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The right-hand side is the damping plus the nonlinear part. -/
theorem infiniteVelocityRHS_eq (nu : ℝ) (u : FourierVelocity) (q : Wavevector) :
    infiniteVelocityRHS nu u q = -(damping nu q • u q) + nonlinear u q := by
  have e : infiniteVelocityRHS nu u q = nonlinearMap q (conv u u q) + viscousMap nu q (u q) := rfl
  rw [e, add_comm]
  congr 1
  change ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • u q = _
  rw [viscous_eq, Complex.coe_smul, neg_smul]

theorem norm_coefficientVec_le_three (v : VelocityCoefficient) :
    ‖coefficientVec v‖ ≤ 3 * ‖v‖ := by
  refine (norm_le_sum_components v).trans ?_
  rw [Fin.sum_univ_three]
  linarith [norm_le_pi_norm v 0, norm_le_pi_norm v 1, norm_le_pi_norm v 2]

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem continuousOn_nonlinear (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (k : Wavevector) : ContinuousOn (fun t ↦ nonlinear (s.coefficients t) k) (Icc 0 T) := by
  refine continuousOn_pi.mpr fun i ↦ ?_
  have h1 : ContinuousOn (fun t ↦ infiniteVelocityRHS nu (s.coefficients t) k i) (Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_velocityRHS_component s hB k i)
  have h2 : ContinuousOn (fun t ↦ (damping nu k : ℂ) * s.coefficients t k i) (Icc 0 T) :=
    continuousOn_const.mul (s.continuous k i).continuousOn
  refine (h1.add h2).congr fun t _ ↦ ?_
  show nonlinear (s.coefficients t) k i =
    infiniteVelocityRHS nu (s.coefficients t) k i + (damping nu k : ℂ) * s.coefficients t k i
  have e := congrFun (infiniteVelocityRHS_eq nu (s.coefficients t) k) i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Complex.real_smul] at e
  linear_combination (-1 : ℂ) * e

/-- **The modewise Duhamel bound along a local solution.** -/
theorem integral_norm_mode_le (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (hnu : 0 < nu) {k : Wavevector} (hk : k ≠ 0) {H : ℝ} (hH : H ∈ Icc (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, ‖s.coefficients t k‖ ≤
      (‖u₀ k‖ + ∫ t in (0 : ℝ)..H, ‖nonlinear (s.coefficients t) k‖) / damping nu k := by
  have h := integral_norm_le_duhamel (E := VelocityCoefficient) (damping_pos hnu hk) hH.1
    (f := fun t ↦ s.coefficients t k) (g := fun t ↦ nonlinear (s.coefficients t) k)
    (continuousOn_pi.mpr fun i ↦ (s.continuous k i).continuousOn)
    ((continuousOn_nonlinear s hB k).mono (Icc_subset_Icc le_rfl hH.2))
    (fun t ht ↦ by
      rw [← infiniteVelocityRHS_eq]
      exact hasDerivAt_pi.mpr fun i ↦ s.equation t ⟨ht.1, ht.2.trans_le hH.2⟩ k i)
  simpa [s.initial] using h

/-- The relaxation weight `6π(1 + |k|) / (4π²ν|k|²)`. -/
def relaxWeight (nu : ℝ) (k : Wavevector) : ℝ :=
  6 * Real.pi * (1 + ‖frequencyVec k‖) / damping nu k

theorem relaxWeight_nonneg (hnu : 0 < nu) (k : Wavevector) : 0 ≤ relaxWeight nu k := by
  unfold relaxWeight damping
  positivity

theorem relaxWeight_le (hnu : 0 < nu) {k : Wavevector} (hk : k ≠ 0) :
    relaxWeight nu k ≤ 3 / (Real.pi * nu) := by
  have h1 := one_le_norm_frequencyVec hk
  have hd := damping_pos hnu hk
  unfold relaxWeight
  rw [div_le_div_iff₀ hd (by positivity)]
  unfold damping
  have h2 : 1 + ‖frequencyVec k‖ ≤ 2 * ‖frequencyVec k‖ ^ 2 := by nlinarith
  calc 6 * Real.pi * (1 + ‖frequencyVec k‖) * (Real.pi * nu)
      = 6 * (Real.pi ^ 2 * nu) * (1 + ‖frequencyVec k‖) := by ring
    _ ≤ 6 * (Real.pi ^ 2 * nu) * (2 * ‖frequencyVec k‖ ^ 2) := by gcongr
    _ = 3 * (4 * Real.pi ^ 2 * nu * ‖frequencyVec k‖ ^ 2) := by ring

/-- The Wiener mass of a vorticity coefficient. -/
def curlMass (u : FourierVelocity) (k : Wavevector) : ℝ := ‖coefficientVec (fourierCurl u k)‖

/-- The weighted Wiener mass of the vorticity nonlinearity. -/
def sourceMass (nu : ℝ) (u : FourierVelocity) (k : Wavevector) : ℝ :=
  relaxWeight nu k * ‖coefficientVec (nonlinear u k)‖

theorem curlMass_nonneg (u : FourierVelocity) (k : Wavevector) : 0 ≤ curlMass u k := norm_nonneg _

theorem sourceMass_nonneg (hnu : 0 < nu) (u : FourierVelocity) (k : Wavevector) :
    0 ≤ sourceMass nu u k :=
  mul_nonneg (relaxWeight_nonneg hnu k) (norm_nonneg _)

theorem curlMass_le (u : FourierVelocity) (k : Wavevector) :
    curlMass u k ≤ 6 * Real.pi * (1 + ‖frequencyVec k‖) * ‖u k‖ := by
  have h1 := norm_coefficientVec_fourierCurl_le u k
  have h2 : fourierMoment 1 u k ≤ (1 + ‖frequencyVec k‖) * (3 * ‖u k‖) := by
    unfold fourierMoment
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (norm_coefficientVec_le_three _) (by positivity)
  calc curlMass u k ≤ 2 * Real.pi * fourierMoment 1 u k := h1
    _ ≤ 2 * Real.pi * ((1 + ‖frequencyVec k‖) * (3 * ‖u k‖)) := by gcongr
    _ = _ := by ring

theorem continuousOn_curlMass (s : LocalInfiniteVelocitySolution nu u₀ T B) (k : Wavevector) :
    ContinuousOn (fun t ↦ curlMass (s.coefficients t) k) (Icc 0 T) :=
  ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
    (continuousOn_pi.mpr fun i ↦ continuousOn_fourierCurl_coefficient s.coefficients _ k
      (fun j ↦ (s.continuous k j).continuousOn) i)).norm

theorem continuousOn_sourceMass (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (k : Wavevector) : ContinuousOn (fun t ↦ sourceMass nu (s.coefficients t) k) (Icc 0 T) :=
  continuousOn_const.mul ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
    (continuousOn_nonlinear s hB k)).norm

/-- **The modewise relaxation bound for the vorticity coefficients.** -/
theorem integral_curlMass_le (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (hnu : 0 < nu) {k : Wavevector} (hk : k ≠ 0) {H : ℝ} (hH : H ∈ Icc (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, curlMass (s.coefficients t) k ≤
      relaxWeight nu k * ‖coefficientVec (u₀ k)‖ + ∫ t in (0 : ℝ)..H, sourceMass nu (s.coefficients t) k := by
  have hd := damping_pos hnu hk
  have hm := integral_norm_mode_le s hB hnu hk hH
  have hc1 : IntervalIntegrable (fun t ↦ curlMass (s.coefficients t) k) volume 0 H :=
    ((continuousOn_curlMass s k).mono (Icc_subset_Icc le_rfl hH.2)).intervalIntegrable_of_Icc hH.1
  have hcn : ContinuousOn (fun t ↦ ‖s.coefficients t k‖) (Icc 0 H) :=
    (continuousOn_pi.mpr fun i ↦ (s.continuous k i).continuousOn).norm
  have hcN : ContinuousOn (fun t ↦ ‖nonlinear (s.coefficients t) k‖) (Icc 0 H) :=
    ((continuousOn_nonlinear s hB k).mono (Icc_subset_Icc le_rfl hH.2)).norm
  have hcS : ContinuousOn (fun t ↦ sourceMass nu (s.coefficients t) k) (Icc 0 H) :=
    (continuousOn_sourceMass s hB k).mono (Icc_subset_Icc le_rfl hH.2)
  have h1 : ∫ t in (0 : ℝ)..H, curlMass (s.coefficients t) k ≤
      ∫ t in (0 : ℝ)..H, 6 * Real.pi * (1 + ‖frequencyVec k‖) * ‖s.coefficients t k‖ :=
    intervalIntegral.integral_mono_on hH.1 hc1
      ((continuousOn_const.mul hcn).intervalIntegrable_of_Icc hH.1) fun t _ ↦ curlMass_le _ k
  have h2 : ∫ t in (0 : ℝ)..H, ‖nonlinear (s.coefficients t) k‖ ≤
      ∫ t in (0 : ℝ)..H, ‖coefficientVec (nonlinear (s.coefficients t) k)‖ :=
    intervalIntegral.integral_mono_on hH.1 (hcN.intervalIntegrable_of_Icc hH.1)
      (((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
        ((continuousOn_nonlinear s hB k).mono (Icc_subset_Icc le_rfl hH.2))).norm.intervalIntegrable_of_Icc
        hH.1) fun t _ ↦ norm_coefficient_sup_le_euclidean _
  have h3 : ‖u₀ k‖ ≤ ‖coefficientVec (u₀ k)‖ := norm_coefficient_sup_le_euclidean _
  rw [intervalIntegral.integral_const_mul] at h1
  have hw : relaxWeight nu k = 6 * Real.pi * (1 + ‖frequencyVec k‖) / damping nu k := rfl
  have hS : ∫ t in (0 : ℝ)..H, sourceMass nu (s.coefficients t) k =
      relaxWeight nu k * ∫ t in (0 : ℝ)..H, ‖coefficientVec (nonlinear (s.coefficients t) k)‖ := by
    unfold sourceMass
    rw [intervalIntegral.integral_const_mul]
  rw [hS, hw]
  have hpos : 0 ≤ 6 * Real.pi * (1 + ‖frequencyVec k‖) := by positivity
  calc ∫ t in (0 : ℝ)..H, curlMass (s.coefficients t) k
      ≤ 6 * Real.pi * (1 + ‖frequencyVec k‖) * ∫ t in (0 : ℝ)..H, ‖s.coefficients t k‖ := h1
    _ ≤ 6 * Real.pi * (1 + ‖frequencyVec k‖) *
        ((‖u₀ k‖ + ∫ t in (0 : ℝ)..H, ‖nonlinear (s.coefficients t) k‖) / damping nu k) :=
        mul_le_mul_of_nonneg_left hm hpos
    _ ≤ 6 * Real.pi * (1 + ‖frequencyVec k‖) *
        ((‖coefficientVec (u₀ k)‖ +
          ∫ t in (0 : ℝ)..H, ‖coefficientVec (nonlinear (s.coefficients t) k)‖) / damping nu k) := by
        gcongr
    _ = _ := by ring

end Modes

section Envelopes

/-- The convolution of an envelope with itself. -/
def convEnvelope (g : Wavevector → ℝ) (k : Wavevector) : ℝ := ∑' p, g p * g (k - p)

/-- The reindexing `(k, p) ↦ (p, k - p)`. -/
def pairEquiv : Wavevector × Wavevector ≃ Wavevector × Wavevector where
  toFun kp := (kp.2, kp.1 - kp.2)
  invFun pr := (pr.1 + pr.2, pr.1)
  left_inv kp := by simp
  right_inv pr := by simp

variable {g : Wavevector → ℝ}

theorem summable_pair (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    Summable (fun kp : Wavevector × Wavevector ↦ g kp.2 * g (kp.1 - kp.2)) := by
  have hn : Summable (fun k ↦ ‖g k‖) := by
    simpa only [Real.norm_of_nonneg (hg0 _)] using hg
  exact (summable_mul_of_summable_norm hn hn).comp_injective pairEquiv.injective

theorem summable_convEnvelope (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    Summable (convEnvelope g) :=
  (summable_pair hg0 hg).prod

theorem convEnvelope_nonneg (hg0 : ∀ k, 0 ≤ g k) (k : Wavevector) : 0 ≤ convEnvelope g k :=
  tsum_nonneg fun p ↦ mul_nonneg (hg0 p) (hg0 _)

/-- **Envelope of the convection.** -/
theorem norm_conv_le_convEnvelope {u : FourierVelocity} (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g)
    (hu : ∀ k, fourierMoment 3 u k ≤ g k) (k : Wavevector) :
    ‖coefficientVec (conv u u k)‖ ≤ convEnvelope g k := by
  have hbound : ∀ p, ‖coefficientVec (modeDot k (u p) • u (k - p))‖ ≤ g p * g (k - p) := by
    intro p
    have e : coefficientVec (modeDot k (u p) • u (k - p)) =
        modeDot k (u p) • coefficientVec (u (k - p)) := rfl
    rw [e, norm_smul]
    have h1 := PancakeLowPressureBudget.norm_modeDot_le k (u p)
    have hw := weight_le_mul k p
    have hk1 : ‖frequencyVec k‖ ≤ (1 + ‖frequencyVec p‖) * (1 + ‖frequencyVec (k - p)‖) := by
      linarith [norm_nonneg (frequencyVec k)]
    have hp3 : 1 + ‖frequencyVec p‖ ≤ (1 + ‖frequencyVec p‖) ^ 3 :=
      le_self_pow₀ (by linarith [norm_nonneg (frequencyVec p)]) (by norm_num)
    have hr3 : 1 + ‖frequencyVec (k - p)‖ ≤ (1 + ‖frequencyVec (k - p)‖) ^ 3 :=
      le_self_pow₀ (by linarith [norm_nonneg (frequencyVec (k - p))]) (by norm_num)
    calc ‖modeDot k (u p)‖ * ‖coefficientVec (u (k - p))‖
        ≤ (‖frequencyVec k‖ * ‖coefficientVec (u p)‖) * ‖coefficientVec (u (k - p))‖ := by gcongr
      _ ≤ ((1 + ‖frequencyVec p‖) * (1 + ‖frequencyVec (k - p)‖) * ‖coefficientVec (u p)‖) *
          ‖coefficientVec (u (k - p))‖ := by gcongr
      _ = ((1 + ‖frequencyVec p‖) * ‖coefficientVec (u p)‖) *
          ((1 + ‖frequencyVec (k - p)‖) * ‖coefficientVec (u (k - p))‖) := by ring
      _ ≤ ((1 + ‖frequencyVec p‖) ^ 3 * ‖coefficientVec (u p)‖) *
          ((1 + ‖frequencyVec (k - p)‖) ^ 3 * ‖coefficientVec (u (k - p))‖) := by gcongr
      _ = fourierMoment 3 u p * fourierMoment 3 u (k - p) := rfl
      _ ≤ g p * g (k - p) :=
          mul_le_mul (hu p) (hu _) (fourierMoment_nonneg _ _ _) (hg0 _)
  have hs : Summable (fun p ↦ g p * g (k - p)) := (summable_pair hg0 hg).prod_factor k
  have hsn : Summable (fun p ↦ ‖coefficientVec (modeDot k (u p) • u (k - p))‖) :=
    hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hsv : Summable (fun p ↦ modeDot k (u p) • u (k - p)) :=
    hs.of_norm_bounded fun p ↦ (norm_coefficient_sup_le_euclidean _).trans (hbound p)
  rw [conv_self, infiniteConvection_eq_of_summable hsv]
  have e : coefficientVec (∑' p, modeDot k (u p) • u (k - p)) =
      ∑' p, coefficientVec (modeDot k (u p) • u (k - p)) :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.map_tsum
  rw [e]
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbound hs)

theorem norm_nonlinear_le (u : FourierVelocity) (k : Wavevector) :
    ‖coefficientVec (nonlinear u k)‖ ≤ 2 * Real.pi * ‖coefficientVec (conv u u k)‖ := by
  have h := norm_nonlinearMap_le k (conv u u k)
  unfold nonlinear
  simpa using h

/-- The constant of the source envelope. -/
def sourceConst (nu : ℝ) : ℝ := 3 / (Real.pi * nu) * (2 * Real.pi)

theorem sourceConst_nonneg {nu : ℝ} (hnu : 0 < nu) : 0 ≤ sourceConst nu := by
  unfold sourceConst
  positivity

theorem sourceMass_le {nu : ℝ} (hnu : 0 < nu) {u : FourierVelocity} (hg0 : ∀ k, 0 ≤ g k)
    (hg : Summable g) (hu : ∀ k, fourierMoment 3 u k ≤ g k) {k : Wavevector} (hk : k ≠ 0) :
    sourceMass nu u k ≤ sourceConst nu * convEnvelope g k := by
  unfold sourceMass
  have h1 := relaxWeight_le hnu hk
  have h2 := (norm_nonlinear_le u k).trans
    (mul_le_mul_of_nonneg_left (norm_conv_le_convEnvelope hg0 hg hu k) (by positivity))
  calc relaxWeight nu k * ‖coefficientVec (nonlinear u k)‖
      ≤ 3 / (Real.pi * nu) * (2 * Real.pi * convEnvelope g k) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = sourceConst nu * convEnvelope g k := by unfold sourceConst; ring

theorem curlMass_le_envelope {u : FourierVelocity} (hu : ∀ k, fourierMoment 3 u k ≤ g k)
    (k : Wavevector) : curlMass u k ≤ 2 * Real.pi * g k :=
  (norm_coefficientVec_fourierCurl_le u k).trans
    (mul_le_mul_of_nonneg_left ((fourierMoment_mono u (by norm_num) k).trans (hu k)) (by positivity))

theorem ne_zero_of_mem_shell {q : ℕ} {k : Wavevector} (hk : k ∈ dyadicShellModes q) : k ≠ 0 := by
  intro h
  subst h
  have h := ((mem_dyadicShellModes_iff_pow_four q 0).mp hk).1
  have h0 : modeSquareNat (0 : Wavevector) = 0 := by simp [modeSquareNat]
  rw [h0] at h
  exact absurd h (not_le.mpr (pow_pos (by norm_num) q))

end Envelopes

section Sums

/-- The Wiener norm of the vorticity over the high shells. -/
def wienerHigh (Q : ℕ) (u : FourierVelocity) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ dyadicShellModes (Q + n), curlMass u k

/-- The weighted Wiener norm of the vorticity nonlinearity over the high shells. -/
def sourceSum (nu : ℝ) (Q : ℕ) (u : FourierVelocity) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ dyadicShellModes (Q + n), sourceMass nu u k

/-- The relaxation constant, from the data alone. -/
def relaxConst (nu : ℝ) (Q : ℕ) (u₀ : FourierVelocity) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ dyadicShellModes (Q + n), relaxWeight nu k * ‖coefficientVec (u₀ k)‖

theorem wienerHigh_nonneg (Q : ℕ) (u : FourierVelocity) : 0 ≤ wienerHigh Q u :=
  tsum_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem sourceSum_nonneg {nu : ℝ} (hnu : 0 < nu) (Q : ℕ) (u : FourierVelocity) :
    0 ≤ sourceSum nu Q u :=
  tsum_nonneg fun _ ↦ Finset.sum_nonneg fun k _ ↦
    mul_nonneg (relaxWeight_nonneg hnu k) (norm_nonneg _)

/-- The block sum of the continuation theorem is dominated by the Wiener norm. -/
theorem highBlockSum_le_wienerHigh (Q : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : highBlockSum Q u ≤ wienerHigh Q u :=
  (summable_blockSup Q u hu).tsum_le_tsum (fun n ↦ blockSup_le _ u)
    (summable_shell_sums Q _ (fun _ ↦ norm_nonneg _) (summable_curlMass u hu))

/-- Partial sums of the Wiener norm over the shells. -/
def partialWiener (Q N : ℕ) (u : FourierVelocity) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n), curlMass u k

/-- The shell envelope of the vorticity Wiener masses. -/
def wienerEnvelope (Q : ℕ) (g : Wavevector → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicShellModes (Q + n), 2 * Real.pi * g k

/-- The shell envelope of the weighted source masses. -/
def sourceEnvelope (nu : ℝ) (Q : ℕ) (g : Wavevector → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ dyadicShellModes (Q + n), sourceConst nu * convEnvelope g k

variable {nu T B : ℝ} {u₀ : FourierVelocity} {g : Wavevector → ℝ}

/-- A summable envelope of the third Fourier moments along a local solution. -/
structure Envelope (s : LocalInfiniteVelocitySolution nu u₀ T B) (g : Wavevector → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ g k
  summable : Summable g
  bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k

variable {s : LocalInfiniteVelocitySolution nu u₀ T B}

theorem summable_wienerEnvelope (he : Envelope s g) (Q : ℕ) : Summable (wienerEnvelope Q g) :=
  summable_shell_sums Q _ (fun k ↦ mul_nonneg (by positivity) (he.nonneg k))
    (he.summable.mul_left _)

theorem summable_sourceEnvelope (hnu : 0 < nu) (he : Envelope s g) (Q : ℕ) :
    Summable (sourceEnvelope nu Q g) :=
  summable_shell_sums Q (fun k ↦ sourceConst nu * convEnvelope g k)
    (fun k ↦ mul_nonneg (sourceConst_nonneg hnu) (convEnvelope_nonneg he.nonneg k))
    ((summable_convEnvelope he.nonneg he.summable).mul_left _)

theorem shellWiener_le (he : Envelope s g) (Q n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖∑ k ∈ dyadicShellModes (Q + n), curlMass (s.coefficients t) k‖ ≤ wienerEnvelope Q g n := by
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ curlMass_nonneg _ k)]
  exact Finset.sum_le_sum fun k _ ↦ curlMass_le_envelope (he.bound t ht) k

theorem shellSource_le (hnu : 0 < nu) (he : Envelope s g) (Q n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖∑ k ∈ dyadicShellModes (Q + n), sourceMass nu (s.coefficients t) k‖ ≤
      sourceEnvelope nu Q g n := by
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ sourceMass_nonneg hnu _ k)]
  exact Finset.sum_le_sum fun k hk ↦
    sourceMass_le hnu he.nonneg he.summable (he.bound t ht) (ne_zero_of_mem_shell hk)

theorem continuousOn_shellWiener (s : LocalInfiniteVelocitySolution nu u₀ T B) (Q n : ℕ) :
    ContinuousOn (fun t ↦ ∑ k ∈ dyadicShellModes (Q + n), curlMass (s.coefficients t) k)
      (Icc 0 T) :=
  continuousOn_finsetSum _ fun k _ ↦ continuousOn_curlMass s k

theorem continuousOn_shellSource (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (Q n : ℕ) :
    ContinuousOn (fun t ↦ ∑ k ∈ dyadicShellModes (Q + n), sourceMass nu (s.coefficients t) k)
      (Icc 0 T) :=
  continuousOn_finsetSum _ fun k _ ↦ continuousOn_sourceMass s hB k

theorem continuousOn_wienerHigh (he : Envelope s g) (Q : ℕ) :
    ContinuousOn (fun t ↦ wienerHigh Q (s.coefficients t)) (Icc 0 T) := by
  unfold wienerHigh
  exact continuousOn_tsum (fun n ↦ continuousOn_shellWiener s Q n) (summable_wienerEnvelope he Q)
    fun n t ht ↦ shellWiener_le he Q n ht

theorem continuousOn_sourceSum (hB : 0 ≤ B) (hnu : 0 < nu) (he : Envelope s g) (Q : ℕ) :
    ContinuousOn (fun t ↦ sourceSum nu Q (s.coefficients t)) (Icc 0 T) := by
  unfold sourceSum
  exact continuousOn_tsum (fun n ↦ continuousOn_shellSource s hB Q n)
    (summable_sourceEnvelope hnu he Q) fun n t ht ↦ shellSource_le hnu he Q n ht

theorem continuousOn_partialWiener (s : LocalInfiniteVelocitySolution nu u₀ T B) (Q N : ℕ) :
    ContinuousOn (fun t ↦ partialWiener Q N (s.coefficients t)) (Icc 0 T) := by
  unfold partialWiener
  exact continuousOn_finsetSum _ fun n _ ↦ continuousOn_shellWiener s Q n

theorem summable_shellWiener (he : Envelope s g) (Q : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n), curlMass (s.coefficients t) k) :=
  (summable_wienerEnvelope he Q).of_norm_bounded fun n ↦ shellWiener_le he Q n ht

theorem summable_shellSource (hnu : 0 < nu) (he : Envelope s g) (Q : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n), sourceMass nu (s.coefficients t) k) :=
  (summable_sourceEnvelope hnu he Q).of_norm_bounded fun n ↦ shellSource_le hnu he Q n ht

theorem summable_relaxTerms (hnu : 0 < nu) (he : Envelope s g) (hT : 0 ≤ T) (Q : ℕ) :
    Summable (fun n ↦ ∑ k ∈ dyadicShellModes (Q + n),
      relaxWeight nu k * ‖coefficientVec (u₀ k)‖) := by
  refine (summable_shell_sums Q (fun k ↦ 3 / (Real.pi * nu) * g k)
    (fun k ↦ mul_nonneg (by positivity) (he.nonneg k)) (he.summable.mul_left _)).of_nonneg_of_le
    (fun n ↦ Finset.sum_nonneg fun k _ ↦ mul_nonneg (relaxWeight_nonneg hnu k) (norm_nonneg _))
    fun _ ↦ Finset.sum_le_sum fun k hk ↦ ?_
  have h0 : ‖coefficientVec (u₀ k)‖ ≤ g k := by
    have h3 := he.bound 0 ⟨le_rfl, hT⟩ k
    rw [s.initial] at h3
    calc ‖coefficientVec (u₀ k)‖
        ≤ (1 + ‖frequencyVec k‖) ^ 3 * ‖coefficientVec (u₀ k)‖ :=
          le_mul_of_one_le_left (norm_nonneg _)
            (one_le_pow₀ (by linarith [norm_nonneg (frequencyVec k)]))
      _ = fourierMoment 3 u₀ k := rfl
      _ ≤ g k := h3
  exact mul_le_mul (relaxWeight_le hnu (ne_zero_of_mem_shell hk)) h0 (norm_nonneg _)
    (by positivity)

/-- The relaxation bound for every partial sum. -/
theorem integral_partialWiener_le (hB : 0 ≤ B) (hnu : 0 < nu) (he : Envelope s g) (Q N : ℕ)
    {H : ℝ} (hH : H ∈ Icc (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, partialWiener Q N (s.coefficients t) ≤
      relaxConst nu Q u₀ + ∫ t in (0 : ℝ)..H, sourceSum nu Q (s.coefficients t) := by
  have hsub : Icc (0 : ℝ) H ⊆ Icc 0 T := Icc_subset_Icc le_rfl hH.2
  have hint : ∀ n ∈ Finset.range N, ∀ k ∈ dyadicShellModes (Q + n),
      IntervalIntegrable (fun t ↦ curlMass (s.coefficients t) k) volume 0 H :=
    fun n _ k _ ↦ ((continuousOn_curlMass s k).mono hsub).intervalIntegrable_of_Icc hH.1
  have hintS : ∀ n ∈ Finset.range N, ∀ k ∈ dyadicShellModes (Q + n),
      IntervalIntegrable (fun t ↦ sourceMass nu (s.coefficients t) k) volume 0 H :=
    fun n _ k _ ↦ ((continuousOn_sourceMass s hB k).mono hsub).intervalIntegrable_of_Icc hH.1
  have e1 : ∫ t in (0 : ℝ)..H, partialWiener Q N (s.coefficients t) =
      ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
        ∫ t in (0 : ℝ)..H, curlMass (s.coefficients t) k := by
    unfold partialWiener
    rw [intervalIntegral.integral_finsetSum fun n _ ↦
      ((continuousOn_shellWiener s Q n).mono hsub).intervalIntegrable_of_Icc hH.1]
    exact Finset.sum_congr rfl fun n hn ↦ intervalIntegral.integral_finsetSum (hint n hn)
  have e2 : ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
      ∫ t in (0 : ℝ)..H, sourceMass nu (s.coefficients t) k =
      ∫ t in (0 : ℝ)..H, ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
        sourceMass nu (s.coefficients t) k := by
    rw [intervalIntegral.integral_finsetSum fun n _ ↦
      ((continuousOn_shellSource s hB Q n).mono hsub).intervalIntegrable_of_Icc hH.1]
    exact Finset.sum_congr rfl fun n hn ↦ (intervalIntegral.integral_finsetSum (hintS n hn)).symm
  have h3 : ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
      relaxWeight nu k * ‖coefficientVec (u₀ k)‖ ≤ relaxConst nu Q u₀ :=
    (summable_relaxTerms hnu he (hH.1.trans hH.2) Q).sum_le_tsum _ fun n _ ↦
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (relaxWeight_nonneg hnu k) (norm_nonneg _)
  have h4 : ∫ t in (0 : ℝ)..H, ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
      sourceMass nu (s.coefficients t) k ≤
      ∫ t in (0 : ℝ)..H, sourceSum nu Q (s.coefficients t) := by
    refine intervalIntegral.integral_mono_on hH.1
      ((continuousOn_finsetSum _ fun n _ ↦
        (continuousOn_shellSource s hB Q n).mono hsub).intervalIntegrable_of_Icc hH.1)
      (((continuousOn_sourceSum hB hnu he Q).mono hsub).intervalIntegrable_of_Icc hH.1)
      fun t ht ↦ ?_
    exact (summable_shellSource hnu he Q (hsub ht)).sum_le_tsum _ fun n _ ↦
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (relaxWeight_nonneg hnu k) (norm_nonneg _)
  rw [e1]
  calc ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
        ∫ t in (0 : ℝ)..H, curlMass (s.coefficients t) k
      ≤ ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
        (relaxWeight nu k * ‖coefficientVec (u₀ k)‖ +
          ∫ t in (0 : ℝ)..H, sourceMass nu (s.coefficients t) k) :=
        Finset.sum_le_sum fun n _ ↦ Finset.sum_le_sum fun k hk ↦
          integral_curlMass_le s hB hnu (ne_zero_of_mem_shell hk) hH
    _ = (∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
          relaxWeight nu k * ‖coefficientVec (u₀ k)‖) +
        ∑ n ∈ Finset.range N, ∑ k ∈ dyadicShellModes (Q + n),
          ∫ t in (0 : ℝ)..H, sourceMass nu (s.coefficients t) k := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun n _ ↦ Finset.sum_add_distrib
    _ ≤ relaxConst nu Q u₀ + ∫ t in (0 : ℝ)..H, sourceSum nu Q (s.coefficients t) := by
        rw [e2]
        exact add_le_add h3 h4

/-- **The relaxation inequality along a local solution with a moment envelope.** -/
theorem integral_wienerHigh_le_local (hB : 0 ≤ B) (hnu : 0 < nu) (he : Envelope s g) (Q : ℕ)
    {H : ℝ} (hH : H ∈ Icc (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, wienerHigh Q (s.coefficients t) ≤
      relaxConst nu Q u₀ + ∫ t in (0 : ℝ)..H, sourceSum nu Q (s.coefficients t) := by
  have hsub : Icc (0 : ℝ) H ⊆ Icc 0 T := Icc_subset_Icc le_rfl hH.2
  have hWint : IntegrableOn (fun t ↦ wienerHigh Q (s.coefficients t)) (Ioc 0 H) volume :=
    (((continuousOn_wienerHigh he Q).mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hlim : Tendsto (fun N ↦ ∫ t in Ioc (0 : ℝ) H, partialWiener Q N (s.coefficients t)) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) H, wienerHigh Q (s.coefficients t))) := by
    refine tendsto_integral_of_dominated_convergence (fun t ↦ wienerHigh Q (s.coefficients t))
      (fun N ↦ ((continuousOn_partialWiener s Q N).mono
        (Ioc_subset_Icc_self.trans hsub)).aestronglyMeasurable measurableSet_Ioc) hWint
      (fun N ↦ ?_) ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
      have ht' : t ∈ Icc (0 : ℝ) T := hsub (Ioc_subset_Icc_self ht)
      unfold partialWiener wienerHigh
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun k _ ↦
        curlMass_nonneg _ k)]
      exact (summable_shellWiener he Q ht').sum_le_tsum _ fun n _ ↦
        Finset.sum_nonneg fun k _ ↦ curlMass_nonneg _ k
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
      have ht' : t ∈ Icc (0 : ℝ) T := hsub (Ioc_subset_Icc_self ht)
      unfold partialWiener wienerHigh
      exact (summable_shellWiener he Q ht').hasSum.tendsto_sum_nat
  rw [intervalIntegral.integral_of_le hH.1]
  refine le_of_tendsto' hlim fun N ↦ ?_
  rw [← intervalIntegral.integral_of_le hH.1]
  exact integral_partialWiener_le hB hnu he Q N hH

/-- **The relaxation inequality along a tame solution.** -/
theorem integral_wienerHigh_le (m : ℕ) (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (Q : ℕ) {H : ℝ} (hH : H ∈ Ico (0 : ℝ) T) :
    IntervalIntegrable (fun t ↦ wienerHigh Q (c.coefficients t)) volume 0 H ∧
    IntervalIntegrable (fun t ↦ sourceSum nu Q (c.coefficients t)) volume 0 H ∧
    ∫ t in (0 : ℝ)..H, wienerHigh Q (c.coefficients t) ≤
      relaxConst nu Q u₀ + ∫ t in (0 : ℝ)..H, sourceSum nu Q (c.coefficients t) := by
  obtain ⟨S, hHS, hST, B, s, hsc, g, hg0, hg, hu⟩ := exists_local_envelope m hm c H hH
  have hB : 0 ≤ B :=
    le_trans (PancakeSobolevWeights.energy_nonneg ∅ _)
      (s.sobolev_bound 0 ⟨le_rfl, hH.1.trans hHS.le⟩ ∅)
  have he : Envelope s g := ⟨hg0, hg, hu⟩
  have hsub : Icc (0 : ℝ) H ⊆ Icc 0 S := Icc_subset_Icc le_rfl hHS.le
  rw [← hsc]
  exact ⟨((continuousOn_wienerHigh he Q).mono hsub).intervalIntegrable_of_Icc hH.1,
    ((continuousOn_sourceSum hB hnu he Q).mono hsub).intervalIntegrable_of_Icc hH.1,
    integral_wienerHigh_le_local hB hnu he Q ⟨hH.1, hHS.le⟩⟩

end Sums

section Route

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- A split of the source into pancake, angularly coercive and residual shares
on `[0, H]`. -/
structure SectorSplit (nu : ℝ) (Q : ℕ) (c : ℝ → FourierVelocity) (H : ℝ) where
  pancake : ℝ → ℝ
  coercive : ℝ → ℝ
  residual : ℝ → ℝ
  pancake_nonneg : ∀ t, 0 ≤ pancake t
  coercive_nonneg : ∀ t, 0 ≤ coercive t
  residual_nonneg : ∀ t, 0 ≤ residual t
  pancake_integrable : IntervalIntegrable pancake volume 0 H
  coercive_integrable : IntervalIntegrable coercive volume 0 H
  residual_integrable : IntervalIntegrable residual volume 0 H
  split_le : ∀ t ∈ Icc (0 : ℝ) H, sourceSum nu Q (c t) ≤ pancake t + coercive t + residual t

/-- **The relaxation data of a tame solution.** For every sector split of the
source, the time functionals of the route are realized on the actual solution
with the relaxation inequality proved. -/
def relaxData (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ} (c : TameSolutionOn nu m u₀ T) (Q : ℕ)
    {H : ℝ} (hH : H ∈ Ico (0 : ℝ) T) (sp : SectorSplit nu Q c.coefficients H) :
    DyadicVorticityStretchingData where
  T := H
  T_nonneg := hH.1
  highBlockSum := fun t ↦ wienerHigh Q (c.coefficients t)
  highBlockSum_nonneg := fun t ↦ wienerHigh_nonneg Q _
  highBlockSum_integrable := (integral_wienerHigh_le m hm hnu c Q hH).1
  pancakeStretchSum := sp.pancake
  pancakeStretchSum_nonneg := sp.pancake_nonneg
  pancakeStretchSum_integrable := sp.pancake_integrable
  coerciveStretchSum := sp.coercive
  coerciveStretchSum_nonneg := sp.coercive_nonneg
  coerciveStretchSum_integrable := sp.coercive_integrable
  residualSum := sp.residual
  residualSum_nonneg := sp.residual_nonneg
  residualSum_integrable := sp.residual_integrable
  relaxationConst := relaxConst nu Q u₀
  relaxation_bound := by
    obtain ⟨_, hSint, hle⟩ := integral_wienerHigh_le m hm hnu c Q hH
    have h2 : ∫ t in (0 : ℝ)..H, sourceSum nu Q (c.coefficients t) ≤
        ∫ t in (0 : ℝ)..H, (sp.pancake t + sp.coercive t + sp.residual t) :=
      intervalIntegral.integral_mono_on hH.1 hSint
        ((sp.pancake_integrable.add sp.coercive_integrable).add sp.residual_integrable) sp.split_le
    rw [intervalIntegral.integral_add (sp.pancake_integrable.add sp.coercive_integrable)
      sp.residual_integrable, intervalIntegral.integral_add sp.pancake_integrable
      sp.coercive_integrable] at h2
    linarith

theorem relaxData_T (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ} (c : TameSolutionOn nu m u₀ T) (Q : ℕ)
    {H : ℝ} (hH : H ∈ Ico (0 : ℝ) T) (sp : SectorSplit nu Q c.coefficients H) :
    (relaxData hm hnu c Q hH sp).T = H := rfl

/-- **Sector estimates on actual solutions give the official statement.** If
for every viscosity, every admissible datum and every horizon `H` the source
of every tame solution admits a sector split whose three estimates hold with
gains summing below one and constants uniform over the horizon, then the
official periodic existence-and-smoothness statement holds. The relaxation
inequality is not assumed: it is the theorem `integral_wienerHigh_le`. -/
theorem periodicStatementB_of_sectorEstimates (m : ℕ) (hm : 7 ≤ m) (Q : ℕ)
    (hsec : ∀ nu : ℝ, ∀ hnu : 0 < nu, ∀ u₀ : FourierVelocity, Admissible m u₀ → ∀ H, 0 < H →
      ∃ Cp εp Cc εc Cr εr : ℝ, εp + εc + εr < 1 ∧
        ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T, ∀ τ, ∀ hτ : τ ∈ Ico (0 : ℝ) T,
          ∃ sp : SectorSplit nu Q c.coefficients τ,
            PancakeSectorEstimate (relaxData hm hnu c Q hτ sp) Cp εp ∧
            CoerciveSectorEstimate (relaxData hm hnu c Q hτ sp) Cc εc ∧
            ResidualSectorEstimate (relaxData hm hnu c Q hτ sp) Cr εr) :
    PeriodicStatementB := by
  intro nu hnu u₀ hu₀
  have hadm := admissible_fluctuation hu₀ m
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := id hadm
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  have hglobal : Nonempty (GlobalSolution nu m (fluctuation u₀)) := by
    refine nonempty_globalSolution_of_highBlockSum hm hnu hr hd hz hE₀0 hE₀ Q fun H hH ↦ ?_
    obtain ⟨Cp, εp, Cc, εc, Cr, εr, hε, hall⟩ := hsec nu hnu (fluctuation u₀) hadm H hH
    refine ⟨(relaxConst nu Q (fluctuation u₀) + (Cp + Cc + Cr)) / (1 - (εp + εc + εr)),
      fun T hT c τ hτ ↦ ?_⟩
    obtain ⟨sp, hpan, hcoh, hres⟩ := hall T hT c τ hτ
    have hD := highBlockIntegral_le_of_sectorEstimates _ hpan hcoh hres hε
    obtain ⟨S, hτS, hST, B, s, hsc, g, hg0, hg, hu⟩ := exists_local_envelope m hm c τ hτ
    have hg1 : ∀ t ∈ Icc (0 : ℝ) S, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ g k :=
      fun t ht k ↦ (fourierMoment_mono _ (by norm_num) k).trans (hu t ht k)
    have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
    have hDc : ContinuousOn (fun t ↦ highBlockSum Q (c.coefficients t)) (Icc 0 τ) := by
      rw [← hsc]
      exact (continuousOn_highBlockSum s Q g hg0 hg hg1).mono hsub
    have hle : ∫ t in (0 : ℝ)..τ, highBlockSum Q (c.coefficients t) ≤
        ∫ t in (0 : ℝ)..τ, wienerHigh Q (c.coefficients t) := by
      refine intervalIntegral.integral_mono_on hτ.1 (hDc.intervalIntegrable_of_Icc hτ.1)
        (integral_wienerHigh_le m hm hnu c Q hτ).1 fun t ht ↦ ?_
      refine highBlockSum_le_wienerHigh Q _ ?_
      rw [← hsc]
      exact (hg.of_nonneg_of_le (fun k ↦ fourierMoment_nonneg _ _ _)
        fun k ↦ hg1 t (hsub ht) k)
    exact hle.trans hD
  obtain ⟨g⟩ := hglobal
  exact exists_official_of_globalSolution hnu hu₀ hm g

end Route

end Mettapedia.FluidDynamics.NavierStokes.FourierRelaxation
