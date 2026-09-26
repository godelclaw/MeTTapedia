import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StochasticLagrangianFlow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteVelocityLipschitz
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The label derivative of the stochastic flow, and volume preservation

The stochastic flow `X_t` of `StochasticLagrangianFlow.lean` sends each label to
the position of its trajectory at time `t`. Its label derivative `∇X_t` is the
object behind the Constantin–Iyer representation `u = P 𝔼[(∇A)ᵀ u₀(A)]`, where
`A_t = X_t⁻¹` is the back-to-labels map.

The velocity of the actual solution is a Fourier series whose termwise
derivatives are summable, so it is differentiable in space, with a bounded and
Lipschitz gradient whose trace vanishes by Fourier incompressibility
(`hasFDerivAt_liftedField`, `norm_liftedGradient_le`,
`norm_liftedGradient_sub_le`, `trace_liftedGradient`). The Jacobian equation
`J' = ∇u J` is linear, and its solutions exist on the whole local interval
(`exists_linearODE`, by Picard–Lindelöf for a truncated field that the
solution never feels). Grönwall's inequality bounds the second-order remainder,
so the flow at each time is differentiable in the label with derivative `J`
(`hasFDerivAt_noisyFlow`). Liouville's formula for the determinant of three
columns, together with zero trace, gives `det J = 1`, and the change of
variables formula then shows that the flow preserves volume
(`exists_noisyFlow_measurePreserving`, `exists_stochasticFlow_measurePreserving`).
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StochasticFlowJacobian

open scoped BigOperators NNReal
open PeriodicFourierTriad PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeLocalSpatialVelocity PancakeFourierMaterialPaths PancakeCurlOutputTail
open PancakeInfiniteVelocityLipschitz PancakeInfiniteFourierDerivative
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeIncomingLowSourceEnergy PancakeConcreteSmoothCellCutoff PancakeIndexedFourierMoments
open StochasticLagrangianFlow
open Set Metric

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

/-! ## The spatial derivative of a lifted Fourier field -/

/-- Coordinatewise real part, as a real-linear map. -/
def realPartCLM : VelocityCoefficient →L[ℝ] X3 :=
  ContinuousLinearMap.pi fun i ↦ Complex.reCLM.comp (ContinuousLinearMap.proj i)

theorem realPartCLM_apply (z : VelocityCoefficient) (i : Fin 3) :
    realPartCLM z i = (z i).re := rfl

theorem norm_realPartCLM_le : ‖realPartCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
    rw [one_mul]
    exact norm_realPart_le z

/-- The real frequency pairing `h ↦ ⟨q, h⟩`. -/
def realModeDotCLM (q : Wavevector) : X3 →L[ℝ] ℝ :=
  ∑ i : Fin 3, (q i : ℝ) • ContinuousLinearMap.proj i

theorem realModeDotCLM_apply (q : Wavevector) (h : X3) :
    realModeDotCLM q h = realModeDot q h := by
  simp [realModeDotCLM, realModeDot]

/-- The derivative of the lifted character `x ↦ exp (2πi ⟨q, x⟩)`. -/
def charDeriv (q : Wavevector) (x : X3) : X3 →L[ℝ] ℂ :=
  UnitAddTorus.mFourier q (torusPoint x) •
    unitTorusDerivativePhase • (Complex.ofRealCLM.comp (realModeDotCLM q))

theorem charDeriv_apply (q : Wavevector) (x h : X3) :
    charDeriv q x h =
      unitTorusDerivativePhase * (realModeDot q h : ℂ) * UnitAddTorus.mFourier q (torusPoint x) := by
  simp only [charDeriv, smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, realModeDotCLM_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_char (q : Wavevector) (x : X3) :
    HasFDerivAt (fun y ↦ UnitAddTorus.mFourier q (torusPoint y)) (charDeriv q x) x := by
  have hlin : HasFDerivAt (fun y : X3 ↦ unitTorusDerivativePhase * (realModeDot q y : ℂ))
      (unitTorusDerivativePhase • (Complex.ofRealCLM.comp (realModeDotCLM q))) x := by
    convert (unitTorusDerivativePhase •
      (Complex.ofRealCLM.comp (realModeDotCLM q))).hasFDerivAt (x := x) using 1
    funext y
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, realModeDotCLM_apply, smul_eq_mul]
  have h := hlin.cexp
  unfold charDeriv
  simp only [mFourier_torusPoint]
  exact h

/-- The derivative of a lifted Fourier mode `x ↦ exp (2πi ⟨q, x⟩) a`. -/
def modeDeriv (q : Wavevector) (a : VelocityCoefficient) (x : X3) :
    X3 →L[ℝ] VelocityCoefficient :=
  (charDeriv q x).smulRight a

theorem modeDeriv_apply (q : Wavevector) (a : VelocityCoefficient) (x h : X3) :
    modeDeriv q a x h = charDeriv q x h • a := rfl

theorem hasFDerivAt_mode (q : Wavevector) (a : VelocityCoefficient) (x : X3) :
    HasFDerivAt (fun y ↦ UnitAddTorus.mFourier q (torusPoint y) • a) (modeDeriv q a x) x :=
  (hasFDerivAt_char q x).smul_const a

theorem norm_phase_realModeDot_le (q : Wavevector) (h : X3) :
    ‖unitTorusDerivativePhase * (realModeDot q h : ℂ)‖ ≤
      (3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖h‖ := by
  rw [norm_mul, norm_derivativePhase, Complex.norm_real]
  calc 2 * Real.pi * ‖realModeDot q h‖ ≤ 2 * Real.pi * (3 * ‖frequencyVec q‖ * ‖h‖) := by
        gcongr
        exact norm_realModeDot_le q h
    _ = _ := by ring

theorem norm_modeDeriv_le (q : Wavevector) (a : VelocityCoefficient) (x : X3) :
    ‖modeDeriv q a x‖ ≤ (3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [modeDeriv_apply, norm_smul, charDeriv_apply, norm_mul, norm_mFourier_apply, mul_one]
  calc ‖unitTorusDerivativePhase * (realModeDot q h : ℂ)‖ * ‖a‖ ≤
        ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖h‖) * ‖a‖ := by
        gcongr
        exact norm_phase_realModeDot_le q h
    _ = _ := by ring

theorem norm_modeDeriv_sub_le (q : Wavevector) (a : VelocityCoefficient) (x y : X3) :
    ‖modeDeriv q a x - modeDeriv q a y‖ ≤
      (3 * (2 * Real.pi)) ^ 2 * (‖frequencyVec q‖ ^ 2 * ‖a‖) * ‖x - y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [sub_apply, modeDeriv_apply, modeDeriv_apply, ← sub_smul, norm_smul,
    charDeriv_apply, charDeriv_apply, ← mul_sub, norm_mul]
  have h1 := norm_phase_realModeDot_le q h
  have h2 := norm_character_lift_sub_le q x y
  calc ‖unitTorusDerivativePhase * (realModeDot q h : ℂ)‖ *
        ‖UnitAddTorus.mFourier q (torusPoint x) - UnitAddTorus.mFourier q (torusPoint y)‖ * ‖a‖ ≤
        ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖h‖) *
          ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖x - y‖) * ‖a‖ := by
        gcongr
    _ = _ := by ring

theorem pow_norm_frequency_mul_le_fourierMoment (u : FourierVelocity) (n : ℕ) (q : Wavevector) :
    ‖frequencyVec q‖ ^ n * ‖u q‖ ≤ fourierMoment n u q := by
  unfold fourierMoment
  gcongr
  · linarith [norm_nonneg (frequencyVec q)]
  · exact norm_coefficient_sup_le_euclidean _

theorem norm_le_fourierMoment (u : FourierVelocity) (n : ℕ) (q : Wavevector) :
    ‖u q‖ ≤ fourierMoment n u q := by
  unfold fourierMoment
  calc ‖u q‖ ≤ 1 * ‖coefficientVec (u q)‖ := by
        rw [one_mul]; exact norm_coefficient_sup_le_euclidean _
    _ ≤ _ := by
        gcongr
        exact one_le_pow₀ (by linarith [norm_nonneg (frequencyVec q)])

/-- The lifted real Fourier field of a coefficient family. -/
def liftedField (u : FourierVelocity) (x : X3) : X3 :=
  realPartCLM (∑' q, UnitAddTorus.mFourier q (torusPoint x) • u q)

/-- Its spatial derivative: the velocity gradient, `liftedGradient u x h = (h · ∇) u (x)`. -/
def liftedGradient (u : FourierVelocity) (x : X3) : X3 →L[ℝ] X3 :=
  realPartCLM.comp (∑' q, modeDeriv q (u q) x)

section Field

variable (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
include hu

omit hu in
theorem norm_modeDeriv_le_moment (q : Wavevector) (x : X3) :
    ‖modeDeriv q (u q) x‖ ≤ (3 * (2 * Real.pi)) * fourierMoment 1 u q :=
  (norm_modeDeriv_le q (u q) x).trans (by
    rw [mul_assoc]
    gcongr
    simpa only [pow_one] using pow_norm_frequency_mul_le_fourierMoment u 1 q)

theorem summable_modeDeriv (x : X3) : Summable (fun q ↦ modeDeriv q (u q) x) :=
  (hu.mul_left _).of_norm_bounded fun q ↦ norm_modeDeriv_le_moment u q x

theorem summable_modes (x : X3) :
    Summable (fun q ↦ UnitAddTorus.mFourier q (torusPoint x) • u q) :=
  hu.of_norm_bounded fun q ↦ by
    rw [norm_smul, norm_mFourier_apply, one_mul]
    exact norm_le_fourierMoment u 1 q

/-- **The lifted field is differentiable, with the termwise derivative.** -/
theorem hasFDerivAt_liftedField (x : X3) :
    HasFDerivAt (liftedField u) (liftedGradient u x) x := by
  have h := hasFDerivAt_tsum (hu.mul_left (3 * (2 * Real.pi)))
    (fun q y ↦ hasFDerivAt_mode q (u q) y) (fun q y ↦ norm_modeDeriv_le_moment u q y)
    (summable_modes u hu 0) x
  exact realPartCLM.hasFDerivAt.comp x h

theorem liftedGradient_apply (x w : X3) :
    liftedGradient u x w = realPartCLM (∑' q, charDeriv q x w • u q) := by
  unfold liftedGradient
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℝ VelocityCoefficient w).map_tsum (summable_modeDeriv u hu x)

theorem norm_liftedGradient_le (x : X3) :
    ‖liftedGradient u x‖ ≤ 3 * (2 * Real.pi) * ∑' q, fourierMoment 1 u q := by
  unfold liftedGradient
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_realPartCLM_le).trans ?_
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded (hu.mul_left _).hasSum fun q ↦ norm_modeDeriv_le_moment u q x

omit hu in
/-- **The gradient is Lipschitz**, with the second Fourier moment as constant. -/
theorem norm_liftedGradient_sub_le (hu2 : Summable (fourierMoment 2 u)) (x y : X3) :
    ‖liftedGradient u x - liftedGradient u y‖ ≤
      (3 * (2 * Real.pi)) ^ 2 * (∑' q, fourierMoment 2 u q) * ‖x - y‖ := by
  have hu : Summable (fourierMoment 1 u) :=
    hu2.of_nonneg_of_le (fun q ↦ by unfold fourierMoment; positivity)
      (fun q ↦ PancakeHigherDerivativeMoments.fourierMoment_mono u (by omega) q)
  unfold liftedGradient
  rw [← ContinuousLinearMap.comp_sub,
    ← (summable_modeDeriv u hu x).tsum_sub (summable_modeDeriv u hu y)]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_realPartCLM_le).trans ?_
  have hb : ∀ q, ‖modeDeriv q (u q) x - modeDeriv q (u q) y‖ ≤
      ((3 * (2 * Real.pi)) ^ 2 * ‖x - y‖) * fourierMoment 2 u q := fun q ↦
    (norm_modeDeriv_sub_le q (u q) x y).trans (by
      rw [mul_comm ((3 * (2 * Real.pi)) ^ 2 * _) ‖x - y‖, mul_comm ((3 * (2 * Real.pi)) ^ 2) ‖x - y‖,
        mul_assoc]
      gcongr
      exact pow_norm_frequency_mul_le_fourierMoment u 2 q)
  calc ‖∑' q, (modeDeriv q (u q) x - modeDeriv q (u q) y)‖ ≤
        ∑' q, ((3 * (2 * Real.pi)) ^ 2 * ‖x - y‖) * fourierMoment 2 u q :=
        tsum_of_norm_bounded (hu2.mul_left _).hasSum hb
    _ = _ := by rw [tsum_mul_left]; ring

omit hu in
theorem realModeDot_single (q : Wavevector) (i : Fin 3) :
    realModeDot q (Pi.single i 1) = q i := by
  simp [realModeDot, Pi.single_apply]

/-- **The gradient is traceless**: its trace is the divergence, which vanishes by
Fourier incompressibility. -/
theorem trace_liftedGradient (hd : ∀ q, modeDot q (u q) = 0) (x : X3) :
    ∑ i : Fin 3, liftedGradient u x (Pi.single i 1) i = 0 := by
  have hsv : ∀ i : Fin 3, Summable (fun q ↦ charDeriv q x (Pi.single i 1) • u q) := by
    intro i
    refine ((hu.mul_left (3 * (2 * Real.pi))).mul_left ‖(Pi.single i 1 : X3)‖).of_norm_bounded
      fun q ↦ ?_
    rw [norm_smul]
    calc ‖charDeriv q x (Pi.single i 1)‖ * ‖u q‖ ≤
          ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖(Pi.single i 1 : X3)‖) * ‖u q‖ := by
          gcongr
          rw [charDeriv_apply, norm_mul, norm_mFourier_apply, mul_one]
          exact norm_phase_realModeDot_le q _
      _ = ‖(Pi.single i 1 : X3)‖ * ((3 * (2 * Real.pi)) * (‖frequencyVec q‖ * ‖u q‖)) := by ring
      _ ≤ _ := by
          gcongr
          simpa only [pow_one] using pow_norm_frequency_mul_le_fourierMoment u 1 q
  have hs : ∀ i : Fin 3, Summable (fun q ↦ charDeriv q x (Pi.single i 1) * u q i) :=
    fun i ↦ Pi.summable.mp (hsv i) i
  have hcomp : ∀ i : Fin 3, liftedGradient u x (Pi.single i 1) i =
      (∑' q, charDeriv q x (Pi.single i 1) * u q i).re := by
    intro i
    rw [liftedGradient_apply u hu, realPartCLM_apply, tsum_apply (hsv i)]
    try rfl
  simp_rw [hcomp]
  rw [← Complex.re_sum, ← Summable.tsum_finsetSum (fun i _ ↦ hs i)]
  have hz : ∀ q, ∑ i : Fin 3, charDeriv q x (Pi.single i 1) * u q i = 0 := by
    intro q
    simp only [charDeriv_apply, realModeDot_single]
    have := hd q
    simp only [modeDot] at this
    calc ∑ i : Fin 3, unitTorusDerivativePhase * ((q i : ℤ) : ℝ) *
          UnitAddTorus.mFourier q (torusPoint x) * u q i =
        unitTorusDerivativePhase * UnitAddTorus.mFourier q (torusPoint x) *
          ∑ i : Fin 3, (q i : ℂ) * u q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          ring
      _ = 0 := by rw [this, mul_zero]
  simp only [hz, tsum_zero, Complex.zero_re]

end Field

/-! ## Linear equations on the whole interval -/

/-- Clamp every coordinate to `[-R, R]`. -/
def clampVec (R : ℝ) (w : X3) : X3 := fun i ↦ max (-R) (min R (w i))

theorem abs_clamp_sub_le (R a b : ℝ) :
    |max (-R) (min R a) - max (-R) (min R b)| ≤ |a - b| := by
  have h1 := abs_max_sub_max_le_abs (min R a) (min R b) (-R)
  have h2 := abs_min_sub_min_le_max R a R b
  rw [sub_self, abs_zero] at h2
  rw [max_comm (-R) (min R a), max_comm (-R) (min R b)]
  calc _ ≤ |min R a - min R b| := h1
    _ ≤ max 0 |a - b| := h2
    _ = |a - b| := max_eq_right (abs_nonneg _)

theorem lipschitzWith_clampVec (R : ℝ) : LipschitzWith 1 (clampVec R) := by
  apply LipschitzWith.of_dist_le_mul
  intro w w'
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
  have h := norm_le_pi_norm (w - w') i
  rw [Pi.sub_apply, Real.norm_eq_abs] at h
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact (abs_clamp_sub_le R (w i) (w' i)).trans h

theorem norm_clampVec_le (R : ℝ) (hR : 0 ≤ R) (w : X3) : ‖clampVec R w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
  have hwi := norm_le_pi_norm w i
  rw [Real.norm_eq_abs] at hwi ⊢
  refine le_trans ?_ hwi
  simp only [clampVec]
  rw [abs_le]
  constructor
  · exact le_trans (le_min (by linarith [abs_nonneg (w i)]) (neg_abs_le (w i))) (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg (w i)]) ((min_le_right _ _).trans (le_abs_self _))

theorem norm_clampVec_le_bound (R : ℝ) (hR : 0 ≤ R) (w : X3) : ‖clampVec R w‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  simp only [clampVec]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clampVec_eq (R : ℝ) (w : X3) (hw : ‖w‖ ≤ R) : clampVec R w = w := by
  funext i
  have hwi := (norm_le_pi_norm w i).trans hw
  rw [Real.norm_eq_abs, abs_le] at hwi
  simp only [clampVec]
  rw [min_eq_right hwi.2, max_eq_right hwi.1]

/-- **Linear equations are solvable on the whole interval.** Picard–Lindelöf applies
to the field truncated outside the ball of radius `‖z₀‖ exp (K T)`; Grönwall's
inequality keeps the solution inside that ball, where the truncation is inactive. -/
theorem exists_linearODE {T : ℝ} (hT : 0 ≤ T) (A : ℝ → X3 →L[ℝ] X3) (K : ℝ≥0)
    (hA : ∀ τ ∈ Icc (0 : ℝ) T, ‖A τ‖ ≤ K)
    (hAc : ∀ w, ContinuousOn (fun τ ↦ A τ w) (Icc (0 : ℝ) T)) (z₀ : X3) :
    ∃ z : ℝ → X3, z 0 = z₀ ∧
      ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (A τ (z τ)) (Icc (0 : ℝ) T) τ := by
  set R : ℝ := ‖z₀‖ * Real.exp (K * T) with hRdef
  have hR : 0 ≤ R := by positivity
  let f : ℝ → X3 → X3 := fun τ w ↦ A τ (clampVec R w)
  let L : ℝ≥0 := ⟨K * R, by positivity⟩
  let r : ℝ≥0 := ⟨K * R * T, by positivity⟩
  have hp : IsPicardLindelof f (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) z₀ r 0 L K := {
    lipschitzOnWith := fun τ hτ ↦ by
      apply LipschitzWith.lipschitzOnWith
      have h1 : LipschitzWith K (A τ) := by
        apply LipschitzWith.of_dist_le_mul
        intro w w'
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact (A τ).le_of_opNorm_le (hA τ hτ) _
      have h2 := h1.comp (lipschitzWith_clampVec R)
      rw [mul_one] at h2
      exact h2
    continuousOn := fun w _ ↦ hAc (clampVec R w)
    norm_le := fun τ hτ w _ ↦ by
      calc ‖A τ (clampVec R w)‖ ≤ K * ‖clampVec R w‖ := (A τ).le_of_opNorm_le (hA τ hτ) _
        _ ≤ K * R := by gcongr; exact norm_clampVec_le_bound R hR w
    mul_max_le := by
      show (L : ℝ) * max (T - 0) (0 - 0) ≤ (r : ℝ) - ((0 : ℝ≥0) : ℝ)
      simp only [sub_zero, sub_self, max_eq_left hT, NNReal.coe_zero]
      exact le_rfl }
  obtain ⟨z, hz0, hz⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- the solution stays in the ball where the truncation is inactive
  have hbound : ∀ τ ∈ Icc (0 : ℝ) T, ‖z τ‖ ≤ R := by
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖z₀‖) (K := (K : ℝ))
      (ε := 0) (HasDerivWithinAt.continuousOn hz)
      (fun τ hτ ↦ (hz τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
      (le_of_eq (by rw [hz0]))
      (fun τ hτ ↦ by
        rw [add_zero]
        exact ((A τ).le_of_opNorm_le (hA τ ⟨hτ.1, hτ.2.le⟩) _).trans
          (by gcongr; exact norm_clampVec_le R hR _))
    intro τ hτ
    have h := hgr τ hτ
    rw [gronwallBound_ε0, sub_zero] at h
    refine h.trans ?_
    rw [hRdef]
    gcongr
    exact hτ.2
  refine ⟨z, hz0, fun τ hτ ↦ ?_⟩
  have hfz : f τ (z τ) = A τ (z τ) := by
    show A τ (clampVec R (z τ)) = A τ (z τ)
    rw [clampVec_eq R (z τ) (hbound τ hτ)]
  have h := hz τ hτ
  rwa [hfz] at h

/-! ## Determinants of three columns -/

/-- The determinant of the matrix with columns `u`, `v`, `w`. -/
def colDet (u v w : X3) : ℝ :=
  u 0 * v 1 * w 2 - u 0 * v 2 * w 1 - v 0 * u 1 * w 2 + v 0 * u 2 * w 1 +
    w 0 * u 1 * v 2 - w 0 * u 2 * v 1

/-- The linear map with prescribed columns. -/
def colMap (z : Fin 3 → X3) : X3 →L[ℝ] X3 :=
  ∑ j : Fin 3, (ContinuousLinearMap.proj j).smulRight (z j)

theorem colMap_apply (z : Fin 3 → X3) (h : X3) : colMap z h = ∑ j : Fin 3, h j • z j := by
  simp [colMap]

theorem colMap_single (z : Fin 3 → X3) (j : Fin 3) : colMap z (Pi.single j 1) = z j := by
  simp [colMap_apply, Pi.single_apply]

theorem det_colMap (z : Fin 3 → X3) : (colMap z).det = colDet (z 0) (z 1) (z 2) := by
  show LinearMap.det (colMap z : X3 →ₗ[ℝ] X3) = _
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_three]
  simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, colMap_single, colDet]
  ring

/-- **Liouville's identity for three columns.** -/
theorem colDet_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (u v w : X3) :
    colDet (A.mulVec u) v w + colDet u (A.mulVec v) w + colDet u v (A.mulVec w) =
      A.trace * colDet u v w := by
  simp only [colDet, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.trace_fin_three]
  ring

theorem hasDerivWithinAt_colDet {u v w : ℝ → X3} {u' v' w' : X3} {S : Set ℝ} {τ : ℝ}
    (hu : HasDerivWithinAt u u' S τ) (hv : HasDerivWithinAt v v' S τ)
    (hw : HasDerivWithinAt w w' S τ) :
    HasDerivWithinAt (fun σ ↦ colDet (u σ) (v σ) (w σ))
      (colDet u' (v τ) (w τ) + colDet (u τ) v' (w τ) + colDet (u τ) (v τ) w') S τ := by
  have c : ∀ (f : ℝ → X3) (f' : X3), HasDerivWithinAt f f' S τ → ∀ i,
      HasDerivWithinAt (fun σ ↦ f σ i) (f' i) S τ := fun f f' h i ↦ hasDerivWithinAt_pi.mp h i
  have t1 := ((c u u' hu 0).mul (c v v' hv 1)).mul (c w w' hw 2)
  have t2 := ((c u u' hu 0).mul (c v v' hv 2)).mul (c w w' hw 1)
  have t3 := ((c v v' hv 0).mul (c u u' hu 1)).mul (c w w' hw 2)
  have t4 := ((c v v' hv 0).mul (c u u' hu 2)).mul (c w w' hw 1)
  have t5 := ((c w w' hw 0).mul (c u u' hu 1)).mul (c v v' hv 2)
  have t6 := ((c w w' hw 0).mul (c u u' hu 2)).mul (c v v' hv 1)
  have h := ((((t1.sub t2).sub t3).add t4).add t5).sub t6
  refine h.congr_deriv ?_
  simp only [colDet, Pi.mul_apply]
  ring

theorem colDet_single : colDet (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1) = 1 := by
  simp [colDet]

/-- A quadratic remainder bound gives the derivative. -/
theorem hasFDerivAt_of_quadratic {f : X3 → X3} {f' : X3 →L[ℝ] X3} {x : X3} {C : ℝ}
    (h : ∀ h : X3, ‖f (x + h) - f x - f' h‖ ≤ C * ‖h‖ ^ 2) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : X3 ↦ ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun h' ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact h h'

theorem gronwallBound_zero_eq_mul (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  by_cases hK : K = 0
  · subst hK
    simp only [gronwallBound_K0, zero_add, one_mul]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_mul, zero_add]
    ring

/-- **Flows with unit Jacobian determinant preserve volume**, by the change of
variables formula. -/
theorem measurePreserving_of_hasFDerivAt_det_one (e : X3 ≃ X3) (he : Continuous e)
    (hJ : ∀ x, ∃ J : X3 →L[ℝ] X3, HasFDerivAt e J x ∧ J.det = 1) :
    MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
  choose J hJd hJ1 using hJ
  have himage : ∀ S, MeasurableSet S →
      MeasureTheory.volume (e '' S) = MeasureTheory.volume S := by
    intro S hS
    rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image MeasureTheory.volume hS
      (fun x _ ↦ (hJd x).hasFDerivWithinAt) e.injective.injOn]
    simp [hJ1]
  refine ⟨he.measurable, ?_⟩
  ext S hS
  rw [MeasureTheory.Measure.map_apply he.measurable hS, ← himage _ (hS.preimage he.measurable),
    e.image_preimage]

/-! ## The gradient along the noisy trajectories -/

section Noisy

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem liftedVelocity_eq_liftedField (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ)
    (hs : Summable (fun q ↦ ‖s.coefficients t q‖)) (x : X3) :
    liftedVelocity s t x = liftedField (s.coefficients t) x := by
  unfold liftedVelocity liftedField spatialField
  rw [fullFourierField_apply id _ hs]
  rfl

/-- The gradient of the velocity seen at the noise-displaced position. -/
def noisyGradient (s : LocalInfiniteVelocitySolution nu u₀ T B) (a : ℝ → X3) (t : ℝ) (y : X3) :
    X3 →L[ℝ] X3 :=
  liftedGradient (s.coefficients t) (y + a t)

variable (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
include hg hSum hu

omit hg hSum in
theorem moment_one_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (q : Wavevector) :
    fourierMoment 1 (s.coefficients t) q ≤ g q :=
  (PancakeHigherDerivativeMoments.fourierMoment_mono _ (by omega) q).trans (hu t ht q)

omit hg in
theorem summable_moment_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fourierMoment 1 (s.coefficients t)) :=
  hSum.of_nonneg_of_le (fun q ↦ by unfold fourierMoment; positivity) (moment_one_le s g hu t ht)

omit hg in
theorem summable_moment_two (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fourierMoment 2 (s.coefficients t)) :=
  hSum.of_nonneg_of_le (fun q ↦ by unfold fourierMoment; positivity) (hu t ht)

omit hg in
/-- **The velocity seen along a noise path is differentiable in space.** -/
theorem hasFDerivAt_noisyVelocity (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : X3) :
    HasFDerivAt (noisyVelocity s a t) (noisyGradient s a t y) y := by
  have hs := summable_moment_one s g hSum hu t ht
  have hfun : noisyVelocity s a t = fun y' ↦ liftedField (s.coefficients t) (y' + a t) := by
    funext y'
    exact liftedVelocity_eq_liftedField s t
      (hs.of_nonneg_of_le (fun q ↦ norm_nonneg _) (fun q ↦ norm_le_fourierMoment _ 1 q))
      (y' + a t)
  rw [hfun]
  have h := (hasFDerivAt_liftedField _ hs (y + a t)).comp y ((hasFDerivAt_id y).add_const (a t))
  simpa [noisyGradient] using h

omit hg in
theorem norm_noisyGradient_le (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : X3) :
    ‖noisyGradient s a t y‖ ≤ 3 * (2 * Real.pi) * ∑' q, g q := by
  have hs := summable_moment_one s g hSum hu t ht
  exact (norm_liftedGradient_le _ hs _).trans (mul_le_mul_of_nonneg_left
    (Summable.tsum_le_tsum (moment_one_le s g hu t ht) hs hSum) (by positivity))

omit hg in
theorem norm_noisyGradient_sub_le (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y y' : X3) :
    ‖noisyGradient s a t y - noisyGradient s a t y'‖ ≤
      (3 * (2 * Real.pi)) ^ 2 * (∑' q, g q) * ‖y - y'‖ := by
  have hs2 := summable_moment_two s g hSum hu t ht
  have h := norm_liftedGradient_sub_le (s.coefficients t) hs2 (y + a t) (y' + a t)
  rw [add_sub_add_right_eq_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Summable.tsum_le_tsum (hu t ht) hs2 hSum) (by positivity)) (norm_nonneg _))

omit hg in
/-- **The gradient seen along a noise path is traceless.** -/
theorem trace_noisyGradient (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : X3) :
    ∑ i : Fin 3, noisyGradient s a t y (Pi.single i 1) i = 0 :=
  trace_liftedGradient _ (summable_moment_one s g hSum hu t ht) (s.transverse t) _

omit hg in
theorem continuousOn_noisyGradient_apply {a p : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    (hp : ContinuousOn p (Icc (0 : ℝ) T)) (w : X3) :
    ContinuousOn (fun τ ↦ noisyGradient s a τ (p τ) w) (Icc (0 : ℝ) T) := by
  have heq : EqOn (fun τ ↦ noisyGradient s a τ (p τ) w)
      (fun τ ↦ realPartCLM (∑' q, charDeriv q (p τ + a τ) w • s.coefficients τ q))
      (Icc (0 : ℝ) T) := fun τ hτ ↦
    liftedGradient_apply _ (summable_moment_one s g hSum hu τ hτ) _ w
  refine ContinuousOn.congr ?_ heq
  refine realPartCLM.continuous.comp_continuousOn
    (continuousOn_tsum (u := fun q ↦ (3 * (2 * Real.pi) * ‖w‖) * g q) (fun q ↦ ?_)
      (hSum.mul_left _) (fun q τ hτ ↦ ?_))
  · have hc : Continuous (fun τ ↦ s.coefficients τ q) := continuous_pi (s.continuous q)
    have hm : ContinuousOn (fun τ ↦ UnitAddTorus.mFourier q (torusPoint (p τ + a τ)))
        (Icc (0 : ℝ) T) :=
      ((UnitAddTorus.mFourier q).continuous.comp continuous_torusPoint).comp_continuousOn
        (hp.add ha)
    simp only [charDeriv_apply]
    exact (continuousOn_const.mul hm).smul hc.continuousOn
  · rw [norm_smul, charDeriv_apply, norm_mul, norm_mFourier_apply, mul_one]
    calc ‖unitTorusDerivativePhase * (realModeDot q w : ℂ)‖ * ‖s.coefficients τ q‖ ≤
          ((3 * (2 * Real.pi)) * ‖frequencyVec q‖ * ‖w‖) * ‖s.coefficients τ q‖ := by
          gcongr
          exact norm_phase_realModeDot_le q w
      _ = (3 * (2 * Real.pi) * ‖w‖) * (‖frequencyVec q‖ ^ 1 * ‖s.coefficients τ q‖) := by ring
      _ ≤ _ := by
          gcongr
          exact (pow_norm_frequency_mul_le_fourierMoment _ 1 q).trans (moment_one_le s g hu τ hτ q)

/-- **Second-order Taylor bound** for the velocity seen along a noise path. -/
theorem norm_noisyVelocity_taylor_le (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (y y' : X3) :
    ‖noisyVelocity s a t y' - noisyVelocity s a t y - noisyGradient s a t y (y' - y)‖ ≤
      (3 * (2 * Real.pi)) ^ 2 * (∑' q, g q) * ‖y' - y‖ ^ 2 := by
  have hM : 0 ≤ (3 * (2 * Real.pi)) ^ 2 * (∑' q, g q) :=
    mul_nonneg (by positivity) (tsum_nonneg hg)
  let G : X3 → X3 := fun w ↦ noisyVelocity s a t w - noisyGradient s a t y w
  have hG : ∀ w ∈ closedBall y ‖y' - y‖, HasFDerivWithinAt G
      (noisyGradient s a t w - noisyGradient s a t y) (closedBall y ‖y' - y‖) w := fun w _ ↦
    ((hasFDerivAt_noisyVelocity s g hSum hu a t ht w).sub
      (noisyGradient s a t y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ w ∈ closedBall y ‖y' - y‖,
      ‖noisyGradient s a t w - noisyGradient s a t y‖ ≤
        (3 * (2 * Real.pi)) ^ 2 * (∑' q, g q) * ‖y' - y‖ := fun w hw ↦ by
    refine (norm_noisyGradient_sub_le s g hSum hu a t ht w y).trans ?_
    rw [mem_closedBall, dist_eq_norm] at hw
    exact mul_le_mul_of_nonneg_left hw hM
  have h := (convex_closedBall y ‖y' - y‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hG
    hbound (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.mpr (le_of_eq (dist_eq_norm _ _)))
  have hGeq : G y' - G y = noisyVelocity s a t y' - noisyVelocity s a t y -
      noisyGradient s a t y (y' - y) := by
    simp only [G, map_sub]
    abel
  rw [← hGeq]
  calc ‖G y' - G y‖ ≤ (3 * (2 * Real.pi)) ^ 2 * (∑' q, g q) * ‖y' - y‖ * ‖y' - y‖ := h
    _ = _ := by ring

/-- **The flow is differentiable in the label, with unit Jacobian determinant.** For
every continuous path and every time `t` of the local interval, the map sending each
label to the position of its trajectory at time `t` has at every label a derivative
`J` with `det J = 1`. The columns of `J` solve the Jacobian equation `J' = ∇u J` along
the trajectory; Grönwall's inequality bounds the second-order remainder, and
Liouville's identity with zero trace keeps the determinant at one. -/
theorem hasFDerivAt_noisyFlow (hT : 0 ≤ T) {a : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (Φ : X3 → X3)
    (hΦ : ∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ) → Φ (Y 0) = Y t)
    (x : X3) : ∃ J : X3 →L[ℝ] X3, HasFDerivAt Φ J x ∧ J.det = 1 := by
  have hu1 : ∀ τ ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    moment_one_le s g hu
  have hG0 : 0 ≤ ∑' q, g q := tsum_nonneg hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ≥0, K = Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) := ⟨_, rfl⟩
  have hK : (K : ℝ) = 3 * (2 * Real.pi) * ∑' q, g q := by
    rw [hKdef]; exact Real.coe_toNNReal _ (by positivity)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (3 * (2 * Real.pi)) ^ 2 * ∑' q, g q := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  -- the trajectory from every label
  choose Y hY0 hY using fun x' ↦ exists_noisyTrajectory s g hg hSum hu1 hT ha x'
  have hΦY : ∀ x', Φ x' = Y x' t := fun x' ↦ by
    have h := hΦ (Y x') (hY x')
    rwa [hY0] at h
  -- the gradient along the trajectory from `x`
  let A : ℝ → X3 →L[ℝ] X3 := fun τ ↦ noisyGradient s a τ (Y x τ)
  have hA : ∀ τ ∈ Icc (0 : ℝ) T, ‖A τ‖ ≤ K := fun τ hτ ↦ by
    rw [hK]; exact norm_noisyGradient_le s g hSum hu a τ hτ _
  have hAc : ∀ w, ContinuousOn (fun τ ↦ A τ w) (Icc (0 : ℝ) T) := fun w ↦
    continuousOn_noisyGradient_apply s g hSum hu ha (HasDerivWithinAt.continuousOn (hY x)) w
  -- the columns of the Jacobian
  choose z hz0 hz using fun j : Fin 3 ↦ exists_linearODE hT A K hA hAc (Pi.single j 1)
  let J : ℝ → X3 →L[ℝ] X3 := fun τ ↦ colMap (fun j ↦ z j τ)
  have hJd : ∀ h : X3, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun σ ↦ J σ h) (A τ (J τ h)) (Icc (0 : ℝ) T) τ := by
    intro h τ hτ
    have hs : HasDerivWithinAt (fun σ ↦ ∑ j : Fin 3, h j • z j σ)
        (∑ j : Fin 3, h j • A τ (z j τ)) (Icc (0 : ℝ) T) τ :=
      HasDerivWithinAt.fun_sum fun j _ ↦ (hz j τ hτ).const_smul (h j)
    simpa only [J, colMap_apply, map_sum, map_smul] using hs
  have hJ0 : ∀ h : X3, J 0 h = h := by
    intro h
    simp only [J, colMap_apply, hz0]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  -- the second-order remainder
  have hrem : ∀ h : X3, ‖Φ (x + h) - Φ x - J t h‖ ≤
      (M * Real.exp (2 * K * T) * gronwallBound 0 K 1 t) * ‖h‖ ^ 2 := by
    intro h
    let Δ : ℝ → X3 := fun τ ↦ Y (x + h) τ - Y x τ - J τ h
    have hΔ0 : Δ 0 = 0 := by
      simp only [Δ, hY0, hJ0, add_sub_cancel_left, sub_self]
    have hΔd : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Δ
        (noisyVelocity s a τ (Y (x + h) τ) - noisyVelocity s a τ (Y x τ) - A τ (J τ h))
        (Icc (0 : ℝ) T) τ :=
      fun τ hτ ↦ ((hY (x + h) τ hτ).sub (hY x τ hτ)).sub (hJd h τ hτ)
    have hbd : ∀ τ ∈ Ico (0 : ℝ) T,
        ‖noisyVelocity s a τ (Y (x + h) τ) - noisyVelocity s a τ (Y x τ) - A τ (J τ h)‖ ≤
          K * ‖Δ τ‖ + M * Real.exp (2 * K * T) * ‖h‖ ^ 2 := by
      intro τ hτ
      have hτ' : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.le⟩
      have hsplit : noisyVelocity s a τ (Y (x + h) τ) - noisyVelocity s a τ (Y x τ) -
          A τ (J τ h) = (noisyVelocity s a τ (Y (x + h) τ) - noisyVelocity s a τ (Y x τ) -
            A τ (Y (x + h) τ - Y x τ)) + A τ (Δ τ) := by
        simp only [Δ, map_sub]
        abel
      rw [hsplit]
      have htay := norm_noisyVelocity_taylor_le s g hg hSum hu a τ hτ' (Y x τ) (Y (x + h) τ)
      rw [← hMdef] at htay
      have hdist := noisyTrajectory_dist_le s g hg hSum hu1 a (Y (x + h)) (Y x)
        (hY (x + h)) (hY x) τ hτ'
      rw [hY0, hY0, dist_eq_norm, dist_eq_norm, add_sub_cancel_left, ← hKdef] at hdist
      have hexp : Real.exp (K * τ) ^ 2 ≤ Real.exp (2 * K * T) := by
        rw [sq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (NNReal.coe_nonneg K) (sub_nonneg.mpr hτ'.2)]
      calc _ ≤ ‖noisyVelocity s a τ (Y (x + h) τ) - noisyVelocity s a τ (Y x τ) -
              A τ (Y (x + h) τ - Y x τ)‖ + ‖A τ (Δ τ)‖ := norm_add_le _ _
        _ ≤ M * ‖Y (x + h) τ - Y x τ‖ ^ 2 + K * ‖Δ τ‖ :=
            add_le_add htay ((A τ).le_of_opNorm_le (hA τ hτ') _)
        _ ≤ M * (‖h‖ * Real.exp (K * τ)) ^ 2 + K * ‖Δ τ‖ :=
            add_le_add (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hM) le_rfl
        _ = M * Real.exp (K * τ) ^ 2 * ‖h‖ ^ 2 + K * ‖Δ τ‖ := by ring
        _ ≤ M * Real.exp (2 * K * T) * ‖h‖ ^ 2 + K * ‖Δ τ‖ :=
            add_le_add (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp hM) (sq_nonneg _)) le_rfl
        _ = K * ‖Δ τ‖ + M * Real.exp (2 * K * T) * ‖h‖ ^ 2 := by ring
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0)
      (HasDerivWithinAt.continuousOn hΔd)
      (fun τ hτ ↦ (hΔd τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
      (le_of_eq (by rw [hΔ0, norm_zero])) hbd t ht
    rw [sub_zero, gronwallBound_zero_eq_mul] at hgr
    rw [hΦY, hΦY]
    calc ‖Y (x + h) t - Y x t - J t h‖ = ‖Δ t‖ := rfl
      _ ≤ M * Real.exp (2 * K * T) * ‖h‖ ^ 2 * gronwallBound 0 K 1 t := hgr
      _ = _ := by ring
  refine ⟨J t, hasFDerivAt_of_quadratic hrem, ?_⟩
  -- Liouville: the determinant of the columns is constant
  have hD : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun σ ↦ colDet (z 0 σ) (z 1 σ) (z 2 σ)) 0 (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    refine (hasDerivWithinAt_colDet (hz 0 τ hτ) (hz 1 τ hτ) (hz 2 τ hτ)).congr_deriv ?_
    have hmv : ∀ w, A τ w = (LinearMap.toMatrix' (A τ : X3 →ₗ[ℝ] X3)).mulVec w := fun w ↦
      (LinearMap.toMatrix'_mulVec _ w).symm
    have htr : (LinearMap.toMatrix' (A τ : X3 →ₗ[ℝ] X3)).trace = 0 := by
      simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix'_apply,
        ContinuousLinearMap.coe_coe]
      exact trace_noisyGradient s g hSum hu a τ hτ _
    rw [hmv, hmv, hmv, colDet_mulVec, htr, zero_mul]
  have hconst := constant_of_has_deriv_right_zero (HasDerivWithinAt.continuousOn hD)
    (fun τ hτ ↦ (hD τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
  show (colMap (fun j ↦ z j t)).det = 1
  rw [det_colMap]
  refine (hconst t ht).trans ?_
  show colDet (z 0 0) (z 1 0) (z 2 0) = 1
  rw [hz0, hz0, hz0]
  exact colDet_single

/-- **The flow preserves volume.** For every continuous path and every time of the
local interval, the flow map is a bijection of space, differentiable with unit
Jacobian determinant at every label, and it preserves Lebesgue measure. -/
theorem exists_noisyFlow_measurePreserving (hT : 0 ≤ T) {a : ℝ → X3}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ e : X3 ≃ X3,
      (∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ) →
        e (Y 0) = Y t) ∧
      (∀ x, ∃ J : X3 →L[ℝ] X3, HasFDerivAt e J x ∧ J.det = 1) ∧
      MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume := by
  obtain ⟨e, he, hL, -, -⟩ := exists_noisyFlow s g hg hSum (moment_one_le s g hu) hT ha ht
  have hJ := hasFDerivAt_noisyFlow s g hg hSum hu hT ha ht e he
  exact ⟨e, he, hJ, measurePreserving_of_hasFDerivAt_det_one e hL.continuous hJ⟩

/-- **The stochastic flow and its back-to-labels map preserve volume, path by path.**
For every continuous path `a`, for instance `√(2ν)` times a Brownian path, and every
time `t` of the local interval, the stochastic flow `X_t` (label to position
`Y(t) + a(t)`) and the back-to-labels map `A_t = X_t⁻¹` are differentiable with unit
Jacobian determinant everywhere, and both preserve Lebesgue measure. -/
theorem exists_stochasticFlow_measurePreserving (hT : 0 ≤ T) {a : ℝ → X3}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ X : X3 ≃ X3,
      (∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ) →
        X (Y 0) = Y t + a t) ∧
      (∀ x, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X J x ∧ J.det = 1) ∧
      (∀ y, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X.symm J y ∧ J.det = 1) ∧
      MeasureTheory.MeasurePreserving X MeasureTheory.volume MeasureTheory.volume ∧
      MeasureTheory.MeasurePreserving X.symm MeasureTheory.volume MeasureTheory.volume := by
  obtain ⟨e, he, hL, hL', -⟩ := exists_noisyFlow s g hg hSum (moment_one_le s g hu) hT ha ht
  have hJ := hasFDerivAt_noisyFlow s g hg hSum hu hT ha ht e he
  let X : X3 ≃ X3 := e.trans (Equiv.addRight (a t))
  have hXapp : ∀ x, X x = e x + a t := fun x ↦ rfl
  have hXsymm : ∀ y, X.symm y = e.symm (y - a t) := fun y ↦ by
    simp [X, sub_eq_add_neg]
  have hXc : Continuous X := by
    have hfun : (X : X3 → X3) = fun x ↦ e x + a t := funext hXapp
    rw [hfun]
    exact hL.continuous.add continuous_const
  have hXsc : Continuous X.symm := by
    have hfun : (X.symm : X3 → X3) = fun y ↦ e.symm (y - a t) := funext hXsymm
    rw [hfun]
    exact hL'.continuous.comp (continuous_id.sub continuous_const)
  have hJX : ∀ x, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X J x ∧ J.det = 1 := fun x ↦ by
    obtain ⟨J, hJd, hJ1⟩ := hJ x
    have hfun : (X : X3 → X3) = fun x ↦ e x + a t := funext hXapp
    exact ⟨J, hfun ▸ hJd.add_const (a t), hJ1⟩
  have hJXs : ∀ y, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X.symm J y ∧ J.det = 1 := fun y ↦ by
    obtain ⟨J, hJd, hJ1⟩ := hJX (X.symm y)
    have hne : J.det ≠ 0 := by rw [hJ1]; exact one_ne_zero
    refine ⟨((J.toContinuousLinearEquivOfDetNeZero hne).symm : X3 →L[ℝ] X3), ?_, ?_⟩
    · apply HasFDerivAt.of_local_left_inverse hXsc.continuousAt
      · simpa using hJd
      · exact Filter.Eventually.of_forall fun y' ↦ X.apply_symm_apply y'
    · rw [ContinuousLinearEquiv.det_coe_symm]
      simp [hJ1]
  refine ⟨X, fun Y hY ↦ ?_, hJX, hJXs, ?_, ?_⟩
  · rw [hXapp, he Y hY]
  · exact measurePreserving_of_hasFDerivAt_det_one X hXc hJX
  · exact measurePreserving_of_hasFDerivAt_det_one X.symm hXsc hJXs

end Noisy

section Tame

open FourierTameContinuation FourierUniqueness PancakeHigherDerivativeMoments

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}

/-- **Volume preservation for the stochastic flow of every tame solution.** For a
tame solution of order at least seven from admissible data, every earlier time `S`,
every continuous path `a` and every `t ∈ [0, S]`, the stochastic flow `X_t` and the
back-to-labels map `A_t = X_t⁻¹` of the actual solution are differentiable with unit
Jacobian determinant and preserve Lebesgue measure. -/
theorem exists_stochasticFlow_measurePreserving_of_tame (hm : 7 ≤ m)
    (c : TameSolutionOn nu m u₀ T) {S : ℝ} (hS : 0 ≤ S) (hST : S < T) :
    ∃ B, ∃ s : LocalInfiniteVelocitySolution nu u₀ S B, s.coefficients = c.coefficients ∧
      ∀ a : ℝ → X3, ContinuousOn a (Icc (0 : ℝ) S) → ∀ t ∈ Icc (0 : ℝ) S,
        ∃ X : X3 ≃ X3,
          (∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) S,
              HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) S) τ) →
            X (Y 0) = Y t + a t) ∧
          (∀ x, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X J x ∧ J.det = 1) ∧
          (∀ y, ∃ J : X3 →L[ℝ] X3, HasFDerivAt X.symm J y ∧ J.det = 1) ∧
          MeasureTheory.MeasurePreserving X MeasureTheory.volume MeasureTheory.volume ∧
          MeasureTheory.MeasurePreserving X.symm MeasureTheory.volume MeasureTheory.volume := by
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := local_envelope_at hm c hST
  have hu2 : ∀ t ∈ Icc (0 : ℝ) S, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q :=
    fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu3 t ht q)
  exact ⟨B, s, hs, fun a ha t ht ↦
    exists_stochasticFlow_measurePreserving s g hg hSum hu2 hS ha ht⟩

end Tame

end Mettapedia.FluidDynamics.NavierStokes.StochasticFlowJacobian
