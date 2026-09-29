import MettapediaNS.WholeSpacePressureHistory
import MettapediaNS.WholeSpaceNSBlowup
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A bounded primitive for separated pressure histories

A smooth separation cutoff gives a bounded pressure observation. The
pressure/core reserve's normalized weight converts it to a primitive
bounded by actual kinetic energy, even at vorticity zeros. This bound is
uniform on smooth unforced prefixes and permits changing receivers and
directions. The separation radius stays fixed and positive. Removing this
separated pressure from the logarithmic reserve changes it by at most the
same energy bound, with no assumption on the observation's derivative.

The companion lab identifies the full signed generator by a shared-noise
receiver/parent calculation. Its stochastic realization, martingale
expectation and actual moment identification are analytic, not formalized
here. A bound on this primitive does not bound its absolute variation or
the individual source terms. In particular, the evolving weight and
near-field costs remain in the continuation problem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureObserver

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field WholeSpaceViscousFlow WholeSpacePressureHistory
  PressureBoundaryResponse

/-- A cutoff of the actual Newtonian stress response. Smoothness is only
needed for the generator identification, not the spatial bound here. -/
def cutoffResponse (A : SmoothL2Field Space) (e x : Space) (χ : Space → ℝ) : ℝ :=
  ∫ y, χ (x - y) * pressureKernel e (x - y) (A.field y)

theorem abs_cutoffResponse_le (A : SmoothL2Field Space) (e x : Space)
    (χ : Space → ℝ) (R : ℝ) (hR : 0 < R) (he : ‖e‖ = 1)
    (hm : Measurable χ) (hb : ∀ z, |χ z| ≤ 1)
    (hz : ∀ z, ‖z‖ < R → χ z = 0) :
    |cutoffResponse A e x χ| ≤ (6 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2 := by
  have hA : Measurable A.field := A.smooth.continuous.measurable
  have hk : Measurable (fun y ↦ pressureKernel e (x - y) (A.field y)) := by
    unfold pressureKernel angularKernel
    fun_prop
  have hχ : Measurable (fun y : Space ↦ χ (x - y)) :=
    hm.comp (measurable_const.sub measurable_id)
  have hf : AEStronglyMeasurable
      (fun y : Space ↦ χ (x - y) * pressureKernel e (x - y) (A.field y)) volume :=
    (hχ.mul hk).aestronglyMeasurable
  have hi : Integrable (fun y ↦ ‖A.field y‖ ^ 2) :=
    A.memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hp (y : Space) : |χ (x - y) * pressureKernel e (x - y) (A.field y)| ≤
      (6 / (Real.pi * R ^ 5)) * ‖A.field y‖ ^ 2 := by
    by_cases hs : R ≤ ‖x - y‖
    · have h := abs_pressureKernel_le e (x - y) (A.field y) R hR hs
      simp only [he, one_pow, mul_one] at h
      calc
        _ = |χ (x - y)| * |pressureKernel e (x - y) (A.field y)| := abs_mul _ _
        _ ≤ 1 * |pressureKernel e (x - y) (A.field y)| :=
          mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using h
    · rw [hz _ (lt_of_not_ge hs), zero_mul, abs_zero]
      positivity
  have hc := hi.const_mul (6 / (Real.pi * R ^ 5))
  have hfi := hc.mono' hf (by simpa only [Real.norm_eq_abs] using Filter.Eventually.of_forall hp)
  calc
    _ ≤ ∫ y, |χ (x - y) * pressureKernel e (x - y) (A.field y)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, (6 / (Real.pi * R ^ 5)) * ‖A.field y‖ ^ 2 :=
      integral_mono_ae hfi.abs hc (Filter.Eventually.of_forall hp)
    _ = _ := by rw [integral_const_mul, WholeSpaceOfficial.integral_norm_sq]

/-- The normalized pressure sensitivity times the separated pressure.
For the physical moments, `W=|ω|²`, and `e` is its unit direction whenever
it is nonzero. At a zero, `W=0` makes the choice of direction irrelevant. -/
def observation (A : SmoothL2Field Space) (e x : Space) (χ : Space → ℝ)
    (θ W Y : ℝ) : ℝ := θ * (2 * W * cutoffResponse A e x χ) / Y

theorem coercive_observation_le (A : SmoothL2Field Space) (e x : Space)
    (χ : Space → ℝ) (θ W Y R : ℝ) (hR : 0 < R) (he : ‖e‖ = 1)
    (hm : Measurable χ) (hb : ∀ z, |χ z| ≤ 1)
    (hz : ∀ z, ‖z‖ < R → χ z = 0)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hW : 0 ≤ W)
    (hY : 1 + (44/95) * W ^ 2 ≤ Y) :
    |observation A e x χ θ W Y| ≤ (9 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2 := by
  have hYp : 0 < Y := by nlinarith [sq_nonneg W]
  have hp := abs_cutoffResponse_le A e x χ R hR he hm hb hz
  rw [observation, abs_div, abs_of_pos hYp]
  apply (div_le_iff₀ hYp).2
  calc
    _ ≤ (3/2) * |cutoffResponse A e x χ| * Y :=
      PressureCoreEnvelope.weighted_source_le θ W Y _ hθ hθ1 hW hY
    _ ≤ (3/2) * ((6 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2) * Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hYp.le
    _ = _ := by ring

theorem reserve_observation_le (A : SmoothL2Field Space) (e x : Space)
    (χ : Space → ℝ) (η δ Q W V Z N R : ℝ) (he : ‖e‖ = 1)
    (hη : 0 < η) (hδ : 0 < δ) (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hR : 0 < R) (hm : Measurable χ) (hb : ∀ z, |χ z| ≤ 1)
    (hz : ∀ z, ‖z‖ < R → χ z = 0) :
    |observation A e x χ
      (PressureCoreEnvelope.weight δ
        (PressureCoreEnvelope.pressure η W V N - PressureCoreEnvelope.core η Q W V Z)) W
      (PressureCoreEnvelope.reserve η δ Q W V Z N)| ≤
      (9 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2 := by
  have hw := PressureCoreEnvelope.weight_mem δ
    (PressureCoreEnvelope.pressure η W V N - PressureCoreEnvelope.core η Q W V Z) hδ
  exact coercive_observation_le A e x χ _ W _ R hR he hm hb hz hw.1 hw.2 hW
    (PressureCoreEnvelope.reserve_coercive η δ Q W V Z N hη hQ hW hZ)

/-- Differentiating the pressure entry of the actual candidate. The
interpolation changes the observation, not the fluid or its forcing. -/
theorem log_reserve_pressure_path_hasDerivAt (η δ Q W V Z N d r : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z) :
    HasDerivAt
      (fun a ↦ Real.log (PressureCoreEnvelope.reserve η δ Q W V Z (N - a * d)))
      (PressureCoreEnvelope.weight δ
        (PressureCoreEnvelope.pressure η W V (N - r * d) -
          PressureCoreEnvelope.core η Q W V Z) * (2 * d) /
        PressureCoreEnvelope.reserve η δ Q W V Z (N - r * d)) r := by
  have hp : HasDerivAt
      (fun a ↦ PressureCoreEnvelope.pressure η W V (N - a * d) -
        PressureCoreEnvelope.core η Q W V Z) (2 * d) r := by
    have h := (((((hasDerivAt_id r).mul_const d).const_sub N).const_mul (-2)).const_add
      (5 * V ^ 2 / (W + η) + (63/95) * W ^ 2)).sub_const
        (PressureCoreEnvelope.core η Q W V Z)
    convert h using 1
    · rfl
    · rfl
    · funext a
      dsimp [PressureCoreEnvelope.pressure]
      ring
    · ring
  have hs := (PressureCoreEnvelope.smoothPositive_hasDerivAt δ
    (PressureCoreEnvelope.pressure η W V (N - r * d) -
      PressureCoreEnvelope.core η Q W V Z) hδ).comp r hp
  have hr : HasDerivAt
      (fun a ↦ PressureCoreEnvelope.reserve η δ Q W V Z (N - a * d))
      (PressureCoreEnvelope.weight δ
        (PressureCoreEnvelope.pressure η W V (N - r * d) -
          PressureCoreEnvelope.core η Q W V Z) * (2 * d)) r := by
    simpa only [PressureCoreEnvelope.reserve, Function.comp_def] using
      hs.const_add (1 + PressureCoreEnvelope.core η Q W V Z)
  have hc := PressureCoreEnvelope.reserve_coercive η δ Q W V Z (N - r * d) hη hQ hW hZ
  have hpos : 0 < PressureCoreEnvelope.reserve η δ Q W V Z (N - r * d) := by
    nlinarith [sq_nonneg W]
  exact hr.log hpos.ne'

/-- Removing the separated pressure from the logarithmic reserve costs
only a bounded correction. This does not remove that pressure's influence
on the actual nearby fluid dynamics. No derivative bound is assumed. -/
theorem reserve_log_cutoff_comparison (A : SmoothL2Field Space) (e x : Space)
    (χ : Space → ℝ) (η δ Q W V Z N R : ℝ) (he : ‖e‖ = 1)
    (hη : 0 < η) (hδ : 0 < δ) (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hR : 0 < R) (hm : Measurable χ) (hb : ∀ z, |χ z| ≤ 1)
    (hz : ∀ z, ‖z‖ < R → χ z = 0) :
    |Real.log (PressureCoreEnvelope.reserve η δ Q W V Z
        (N - W * cutoffResponse A e x χ)) -
      Real.log (PressureCoreEnvelope.reserve η δ Q W V Z N)| ≤
      (9 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2 := by
  let g : ℝ → ℝ := fun r ↦ Real.log (PressureCoreEnvelope.reserve η δ Q W V Z
    (N - r * (W * cutoffResponse A e x χ)))
  let g' : ℝ → ℝ := fun r ↦ observation A e x χ
    (PressureCoreEnvelope.weight δ
      (PressureCoreEnvelope.pressure η W V (N - r * (W * cutoffResponse A e x χ)) -
        PressureCoreEnvelope.core η Q W V Z)) W
    (PressureCoreEnvelope.reserve η δ Q W V Z (N - r * (W * cutoffResponse A e x χ)))
  have hd (r : ℝ) : HasDerivAt g (g' r) r := by
    dsimp [g, g', observation]
    convert log_reserve_pressure_path_hasDerivAt η δ Q W V Z N
      (W * cutoffResponse A e x χ) r hη hδ hQ hW hZ using 1
    ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun r _ ↦ (hd r).hasDerivWithinAt)
    (fun r _ ↦ show ‖g' r‖ ≤ (9 / (Real.pi * R ^ 5)) * ‖A.toLp‖ ^ 2 from by
      simpa only [g', Real.norm_eq_abs] using
        reserve_observation_le A e x χ η δ Q W V Z
          (N - r * (W * cutoffResponse A e x χ)) R he hη hδ hQ hW hZ hR hm hb hz)
  simpa [g, Real.norm_eq_abs] using hh

/-- An actual unforced smooth prefix shares one initial-energy bound.
This is a bound on the observation, not on its separate derivative terms. -/
theorem evolution_observation_le_initial {ν T : ℝ} {hT : 0 ≤ T}
    (U : NSEvolution ν T hT) (hν : 0 ≤ ν) (t : Icc (0 : ℝ) T)
    (e x : Space) (χ : Space → ℝ) (θ W Y R : ℝ) (hR : 0 < R) (he : ‖e‖ = 1)
    (hm : Measurable χ) (hb : ∀ z, |χ z| ≤ 1)
    (hz : ∀ z, ‖z‖ < R → χ z = 0)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hW : 0 ≤ W)
    (hY : 1 + (44/95) * W ^ 2 ≤ Y) :
    |observation (U.velocity t) e x χ θ W Y| ≤
      (9 / (Real.pi * R ^ 5)) * ‖(U.velocity ⟨0, le_rfl, hT⟩).toLp‖ ^ 2 := by
  have he0 := U.l2_norm_le hν t
  exact (coercive_observation_le (U.velocity t) e x χ θ W Y R hR he hm hb hz
    hθ hθ1 hW hY).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) he0 2) (by positivity))

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureObserver
