import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMVorticityGrowth

/-!
# BKM log-Sobolev gradient-control interface

This module does not prove the analytic log-Sobolev/Biot-Savart estimate.
It records the exact interface needed by the BKM route: once such a gradient
control is supplied, the already-checked stretching and standard-vorticity
growth estimates apply with the corresponding logarithmic envelope.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory

section BKMContinuation

/-- Candidate logarithmic gradient envelope for the BKM route.  The `H`
argument is an external high-norm envelope; this definition only records the
shape used downstream, not a proof that `H` is any particular Sobolev norm. -/
def bkmLogSobolevGradientEnvelope
    (C : ℝ) (Ω H : NSTime → ℝ) (t : NSTime) : ℝ :=
  C * (1 + Ω t * Real.log (Real.exp 1 + H t))

/-- The vorticity-log factor in the BKM logarithmic gradient envelope. -/
def bkmLogSobolevLogFactor
    (Ω H : NSTime → ℝ) (t : NSTime) : ℝ :=
  Ω t * Real.log (Real.exp 1 + H t)

/-- The BKM logarithmic factor is nonnegative when both envelopes are
nonnegative at the current time. -/
theorem bkmLogSobolevLogFactor_nonneg_of_nonneg
    {Ω H : NSTime → ℝ} {t : NSTime}
    (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    0 ≤ bkmLogSobolevLogFactor Ω H t := by
  have hexp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have harg : (1 : ℝ) ≤ Real.exp (1 : ℝ) + H t := by
    linarith
  have hlog : 0 ≤ Real.log (Real.exp (1 : ℝ) + H t) :=
    Real.log_nonneg harg
  exact mul_nonneg hΩ hlog

/-- The logarithmic envelope is nonnegative under the expected sign
hypotheses on its constant, vorticity envelope, and high-norm envelope. -/
theorem bkmLogSobolevGradientEnvelope_nonneg_of_nonneg
    {C : ℝ} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC : 0 ≤ C) (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    0 ≤ bkmLogSobolevGradientEnvelope C Ω H t := by
  have hprod : 0 ≤ bkmLogSobolevLogFactor Ω H t :=
    bkmLogSobolevLogFactor_nonneg_of_nonneg hΩ hH
  have hprod_raw : 0 ≤ Ω t * Real.log (Real.exp (1 : ℝ) + H t) := by
    simpa [bkmLogSobolevLogFactor] using hprod
  exact mul_nonneg hC (by linarith)

/-- If the vorticity and high-norm envelopes are bounded at a time, then the
BKM logarithmic factor is bounded by the corresponding constant factor. -/
theorem bkmLogSobolevLogFactor_le_of_bounds
    {Ω H : NSTime → ℝ} {t : NSTime} {Ωmax Hmax : ℝ}
    (hΩ_nonneg : 0 ≤ Ω t) (hΩ_le : Ω t ≤ Ωmax)
    (hH_nonneg : 0 ≤ H t) (hH_le : H t ≤ Hmax) :
    bkmLogSobolevLogFactor Ω H t ≤
      Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax) := by
  have hΩmax_nonneg : 0 ≤ Ωmax := hΩ_nonneg.trans hΩ_le
  have harg_pos : 0 < Real.exp (1 : ℝ) + H t := by
    linarith [Real.exp_pos (1 : ℝ)]
  have harg_le :
      Real.exp (1 : ℝ) + H t ≤ Real.exp (1 : ℝ) + Hmax := by
    linarith
  have hlog_le :
      Real.log (Real.exp (1 : ℝ) + H t) ≤
        Real.log (Real.exp (1 : ℝ) + Hmax) :=
    Real.log_le_log harg_pos harg_le
  have hlog_nonneg :
      0 ≤ Real.log (Real.exp (1 : ℝ) + H t) := by
    have hexp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    have harg_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) + H t := by
      linarith
    exact Real.log_nonneg harg_one
  simpa [bkmLogSobolevLogFactor] using
    (mul_le_mul hΩ_le hlog_le hlog_nonneg hΩmax_nonneg)

/-- A slabwise constant upper bound for both the vorticity envelope and the
high-norm envelope gives a constant upper bound for the BKM gradient
coefficient at the current time. -/
theorem bkmLogSobolevGradientEnvelope_le_of_bounds
    {C : ℝ} {Ω H : NSTime → ℝ} {t : NSTime} {Ωmax Hmax : ℝ}
    (hC : 0 ≤ C)
    (hΩ_nonneg : 0 ≤ Ω t) (hΩ_le : Ω t ≤ Ωmax)
    (hH_nonneg : 0 ≤ H t) (hH_le : H t ≤ Hmax) :
    bkmLogSobolevGradientEnvelope C Ω H t ≤
      C * (1 + Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax)) := by
  have hLogFactor :=
    bkmLogSobolevLogFactor_le_of_bounds
      hΩ_nonneg hΩ_le hH_nonneg hH_le
  have hsum :
      1 + bkmLogSobolevLogFactor Ω H t ≤
        1 + Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax) := by
    exact add_le_add_right hLogFactor 1
  simpa [bkmLogSobolevGradientEnvelope, bkmLogSobolevLogFactor] using
    (mul_le_mul_of_nonneg_left hsum hC)

/-- Slabwise version of `bkmLogSobolevGradientEnvelope_le_of_bounds`, shaped
for the constant-majorant scalar Gronwall comparison on `Set.Ico 0 T`. -/
theorem bkmLogSobolevGradientEnvelope_le_constant_on_Ico_of_bounds
    {C T : ℝ} {Ω H : NSTime → ℝ} {Ωmax Hmax : ℝ}
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hΩ_le : ∀ t, 0 ≤ t → t ≤ T → Ω t ≤ Ωmax)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le : ∀ t, 0 ≤ t → t ≤ T → H t ≤ Hmax) :
    ∀ t, t ∈ Set.Ico 0 T →
      bkmLogSobolevGradientEnvelope C Ω H t ≤
        C * (1 + Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax)) := by
  intro t ht
  exact
    bkmLogSobolevGradientEnvelope_le_of_bounds hC
      (hΩ_nonneg t ht.1 (le_of_lt ht.2))
      (hΩ_le t ht.1 (le_of_lt ht.2))
      (hH_nonneg t ht.1 (le_of_lt ht.2))
      (hH_le t ht.1 (le_of_lt ht.2))

/-- The one-constant BKM envelope dominates the conventional affine-log
form `C0 + C1 * Omega log(e + H)` once `C` dominates both affine constants. -/
theorem bkmLogSobolevGradientEnvelope_dominates_affineLog
    {C C0 C1 : ℝ} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : 0 ≤ Ω t) (hH : 0 ≤ H t) :
    C0 + C1 * bkmLogSobolevLogFactor Ω H t ≤
      bkmLogSobolevGradientEnvelope C Ω H t := by
  have hlogFactor : 0 ≤ bkmLogSobolevLogFactor Ω H t :=
    bkmLogSobolevLogFactor_nonneg_of_nonneg hΩ hH
  have hmul :
      C1 * bkmLogSobolevLogFactor Ω H t ≤
        C * bkmLogSobolevLogFactor Ω H t :=
    mul_le_mul_of_nonneg_right hC1 hlogFactor
  calc
    C0 + C1 * bkmLogSobolevLogFactor Ω H t
        ≤ C + C * bkmLogSobolevLogFactor Ω H t := add_le_add hC0 hmul
    _ = bkmLogSobolevGradientEnvelope C Ω H t := by
      simp [bkmLogSobolevGradientEnvelope, bkmLogSobolevLogFactor]
      ring

/-- The actual pointwise log-Sobolev/Biot-Savart inequality on a slab.  The
separate control predicate below adds only envelope nonnegativity. -/
def BKMLogSobolevPointwiseInequalityOn
    (u : NSVelocityField) (T C : ℝ) (Ω H : NSTime → ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T →
    ‖spatialFDeriv u t x‖ ≤ bkmLogSobolevGradientEnvelope C Ω H t

/-- Conventional affine-log form of the BKM Biot-Savart/log-Sobolev estimate:
`||grad u||_∞ <= C0 + C1 * Omega log(e + H)`.

The checked theorem below normalizes this two-constant analytic statement into
the one-constant downstream BKM envelope. -/
def BKMLogSobolevAffinePointwiseInequalityOn
    (u : NSVelocityField) (T C0 C1 : ℝ) (Ω H : NSTime → ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T →
    ‖spatialFDeriv u t x‖ ≤
      C0 + C1 * bkmLogSobolevLogFactor Ω H t

/-- A supplied log-Sobolev/Biot-Savart gradient-control hypothesis on a slab. -/
def BKMLogSobolevGradientControlOn
    (u : NSVelocityField) (T C : ℝ) (Ω H : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ bkmLogSobolevGradientEnvelope C Ω H t) ∧
    ∀ t x, 0 ≤ t → t ≤ T →
      ‖spatialFDeriv u t x‖ ≤ bkmLogSobolevGradientEnvelope C Ω H t

/-- A pointwise log-Sobolev inequality plus nonnegative envelopes gives the
gradient-control predicate used downstream. -/
theorem BKMLogSobolevGradientControlOn.of_pointwiseInequality
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hC : 0 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hIneq : BKMLogSobolevPointwiseInequalityOn u T C Ω H) :
    BKMLogSobolevGradientControlOn u T C Ω H := by
  exact
    ⟨fun t ht0 htT =>
        bkmLogSobolevGradientEnvelope_nonneg_of_nonneg hC
          (hΩ t ht0 htT) (hH t ht0 htT),
      hIneq⟩

/-- A conventional affine-log pointwise estimate implies the downstream
one-constant pointwise BKM log-Sobolev estimate. -/
theorem BKMLogSobolevPointwiseInequalityOn.of_affinePointwiseInequality
    {u : NSVelocityField} {T C C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevPointwiseInequalityOn u T C Ω H := by
  intro t x ht0 htT
  exact
    (hAffine t x ht0 htT).trans
      (bkmLogSobolevGradientEnvelope_dominates_affineLog
        hC0 hC1 (hΩ t ht0 htT) (hH t ht0 htT))

/-- A conventional affine-log pointwise estimate plus nonnegative envelopes
gives the downstream log-Sobolev gradient-control predicate. -/
theorem BKMLogSobolevGradientControlOn.of_affinePointwiseInequality
    {u : NSVelocityField} {T C C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC : 0 ≤ C)
    (hC0 : C0 ≤ C) (hC1 : C1 ≤ C)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevGradientControlOn u T C Ω H := by
  exact
    BKMLogSobolevGradientControlOn.of_pointwiseInequality
      hC hΩ hH
      (BKMLogSobolevPointwiseInequalityOn.of_affinePointwiseInequality
        hC0 hC1 hΩ hH hAffine)

/-- If the affine constants are nonnegative, the normalized BKM constant can
be chosen as their maximum. -/
theorem BKMLogSobolevGradientControlOn.of_affinePointwiseInequality_max
    {u : NSVelocityField} {T C0 C1 : ℝ} {Ω H : NSTime → ℝ}
    (hC0_nonneg : 0 ≤ C0) (hC1_nonneg : 0 ≤ C1)
    (hΩ : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H) :
    BKMLogSobolevGradientControlOn u T (max C0 C1) Ω H := by
  have hC : 0 ≤ max C0 C1 := by
    by_cases h : C0 ≤ C1
    · simpa [max_eq_right h] using hC1_nonneg
    · have h' : C1 ≤ C0 := le_of_not_ge h
      simpa [max_eq_left h'] using hC0_nonneg
  exact
    BKMLogSobolevGradientControlOn.of_affinePointwiseInequality
      hC (le_max_left C0 C1) (le_max_right C0 C1) hΩ hH hAffine

/-- A supplied log-Sobolev gradient control is exactly the gradient envelope
needed by the checked stretching estimates. -/
theorem BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ}
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H) :
    spatialGradientOperatorEnvelopeOn u T
      (bkmLogSobolevGradientEnvelope C Ω H) :=
  hLog

/-- If a supplied BKM log-Sobolev control has slabwise constant bounds for
the vorticity and high-norm envelopes, then it gives a uniform slabwise
gradient bound.  This is the algebraic bridge from the logarithmic coefficient
to the constant-coefficient continuation estimates; it does not prove the
missing PDE continuation theorem. -/
theorem BKMLogSobolevGradientControlOn.to_uniformSpatialGradientOperatorBoundUpTo_of_bounds
    {u : NSVelocityField} {T C : ℝ} {Ω H : NSTime → ℝ} {Ωmax Hmax : ℝ}
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hC : 0 ≤ C) (hΩmax : 0 ≤ Ωmax) (hHmax : 0 ≤ Hmax)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hΩ_le : ∀ t, 0 ≤ t → t ≤ T → Ω t ≤ Ωmax)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le : ∀ t, 0 ≤ t → t ≤ T → H t ≤ Hmax) :
    uniformSpatialGradientOperatorBoundUpTo u T
      (C * (1 + Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax))) := by
  have hexp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hlog_max_nonneg :
      0 ≤ Real.log (Real.exp (1 : ℝ) + Hmax) := by
    have harg_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) + Hmax := by
      linarith
    exact Real.log_nonneg harg_one
  have hcoeff_nonneg :
      0 ≤ 1 + Ωmax * Real.log (Real.exp (1 : ℝ) + Hmax) := by
    exact add_nonneg zero_le_one (mul_nonneg hΩmax hlog_max_nonneg)
  refine ⟨mul_nonneg hC hcoeff_nonneg, ?_⟩
  intro t x ht0 htT
  exact
    (hLog.2 t x ht0 htT).trans
      (bkmLogSobolevGradientEnvelope_le_of_bounds hC
        (hΩ_nonneg t ht0 htT) (hΩ_le t ht0 htT)
        (hH_nonneg t ht0 htT) (hH_le t ht0 htT))

/-- Log-Sobolev gradient control gives the BKM enstrophy growth inequality
with the logarithmic coefficient at the current time. -/
theorem vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_control
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (bkmLogSobolevGradientEnvelope C Ω H t) := by
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_gradient_bound
      hν hBal (hLog.1 t ht0 htT) (fun x => hLog.2 t x ht0 htT)
      hStretchInt hEnstrophyInt

/-- The pointwise log-Sobolev/Biot-Savart inequality plugs directly into the
BKM enstrophy growth inequality once the balance identity is available. -/
theorem vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_pointwiseInequality
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hC : 0 ≤ C)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hIneq : BKMLogSobolevPointwiseInequalityOn u T C Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (bkmLogSobolevGradientEnvelope C Ω H t) := by
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_control
      hν hBal
      (BKMLogSobolevGradientControlOn.of_pointwiseInequality
        hC hΩ hH hIneq)
      ht0 htT hStretchInt hEnstrophyInt

/-- The affine log-Sobolev/Biot-Savart pointwise gradient estimate controls
the integrated vorticity-stretching production by the same affine logarithmic
coefficient.  This is the integral estimate feeding the BKM enstrophy
differential inequality. -/
theorem vorticityStretchingPowerIntegral_le_affineLog_enstrophyAt
    {T C0 C1 : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityStretchingPowerIntegral u t ≤
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) *
        vorticityEnstrophyAt u t := by
  have hLogFactor : 0 ≤ bkmLogSobolevLogFactor Ω H t :=
    bkmLogSobolevLogFactor_nonneg_of_nonneg
      (hΩ t ht0 htT) (hH t ht0 htT)
  have hCoeff : 0 ≤ C0 + C1 * bkmLogSobolevLogFactor Ω H t :=
    add_nonneg hC0 (mul_nonneg hC1 hLogFactor)
  exact
    vorticityStretchingPowerIntegral_le_gradient_mul_enstrophyAt
      hCoeff (fun x => hAffine t x ht0 htT) hStretchInt hEnstrophyInt

/-- The conventional affine-log pointwise Biot-Savart/log-Sobolev estimate
gives the BKM enstrophy growth inequality with the same affine coefficient:
`dE/dt <= (C0 + C1 * Omega log(e + H)) * E`. -/
theorem vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_affinePointwiseInequality
    {ν T C0 C1 : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hBal : vorticityEnstrophyBalanceAt ν u t)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hStretchInt : Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt : Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    vorticityEnstrophyGradientControlledAt ν u t
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) := by
  have hLogFactor : 0 ≤ bkmLogSobolevLogFactor Ω H t :=
    bkmLogSobolevLogFactor_nonneg_of_nonneg
      (hΩ t ht0 htT) (hH t ht0 htT)
  have hCoeff : 0 ≤ C0 + C1 * bkmLogSobolevLogFactor Ω H t :=
    add_nonneg hC0 (mul_nonneg hC1 hLogFactor)
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_gradient_bound
      hν hBal hCoeff (fun x => hAffine t x ht0 htT)
      hStretchInt hEnstrophyInt

/-- Finite-time witness form of the affine-log BKM enstrophy estimate.  Once
the standard vorticity equation is available and the time-pairing derivative
represents the slice enstrophy derivative, the checked transport and diffusion
identities turn the affine pointwise log-Sobolev estimate into the differential
inequality for the witness enstrophy. -/
theorem vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_affinePointwiseInequality
    {ν T C0 C1 : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hEq : concreteVorticityEquationOn ν W.velocity T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hVorticitySlices : finiteTimeWitnessVorticitySchwartzSlices W)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn
      W.velocity T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hEnstrophyInt :
      Integrable (fun x => vorticityEnstrophyDensity W.velocity t x)) :
    vorticityEnstrophyGradientControlledAt ν W.velocity t
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) := by
  have hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t :=
    vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
      hEq hInt hTime ht0 htT
  have hBal : vorticityEnstrophyBalanceAt ν W.velocity t :=
    vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocityVorticitySchwartzSlices
      W hVelocitySlices hVorticitySlices hRaw ht0 htT
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_affinePointwiseInequality
      hν hBal hC0 hC1 hΩ hH hAffine ht0 htT hInt.2.2 hEnstrophyInt

/-- Finite-time witness form of the affine-log BKM enstrophy estimate with
the vorticity Schwartz-slice input derived from the velocity Schwartz slice by
taking the checked Schwartz curl. -/
theorem vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_velocitySchwartz_affinePointwiseInequality
    {ν T C0 C1 : ℝ} {u₀ : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    {Ω H : NSTime → ℝ} {t : NSTime}
    (hν : 0 ≤ ν)
    (hEq : concreteVorticityEquationOn ν W.velocity T)
    (hVelocitySlices : finiteTimeWitnessVelocitySchwartzSlices W)
    (hInt : vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t)
    (hTime : vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hΩ : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s)
    (hH : ∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s)
    (hAffine : BKMLogSobolevAffinePointwiseInequalityOn
      W.velocity T C0 C1 Ω H)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hEnstrophyInt :
      Integrable (fun x => vorticityEnstrophyDensity W.velocity t x)) :
    vorticityEnstrophyGradientControlledAt ν W.velocity t
      (C0 + C1 * bkmLogSobolevLogFactor Ω H t) := by
  exact
    vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_affinePointwiseInequality
      W hν hEq hVelocitySlices
      (finiteTimeWitnessVorticitySchwartzSlices_of_velocitySchwartzSlices
        W hVelocitySlices)
      hInt hTime hC0 hC1 hΩ hH hAffine ht0 htT hEnstrophyInt

/-- Log-Sobolev gradient control and a vorticity envelope control the
material-minus-diffusion remainder under the standard vorticity equation. -/
theorem norm_vorticityMaterialDiffusionRemainder_le_of_logSobolev_control
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
      bkmLogSobolevGradientEnvelope C Ω H t * Ω t := by
  exact
    norm_vorticityMaterialDiffusionRemainder_le_of_envelopes hEq
      (BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog)
      hΩ ht0 htT

/-- Log-Sobolev gradient control and a vorticity envelope control the
pointwise enstrophy-production contribution of the standard vorticity
equation. -/
theorem abs_vorticityMaterialDiffusionPower_le_of_logSobolev_control
    {ν T C : ℝ} {u : NSVelocityField} {Ω H : NSTime → ℝ}
    (hEq : concreteVorticityEquationOn ν u T)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hΩ : vorticityEnvelopeOn u T Ω)
    {t : NSTime} {x : NSSpace} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    |vorticityMaterialDiffusionPower ν u t x| ≤
      bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t) := by
  exact
    abs_vorticityMaterialDiffusionPower_le_of_envelopes hEq
      (BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog)
      hΩ ht0 htT

/-- Checked logarithmic-enstrophy growth package: supplied log-Sobolev
gradient control turns the BKM enstrophy balance into
`dE/dt <= C (1 + Omega log(e + H)) E`. -/
def BKMVorticityEnstrophyLogSobolevGrowthClosed : Prop :=
  ∀ (ν T C : ℝ) (u : NSVelocityField) (Ω H : NSTime → ℝ) (t : NSTime),
    0 ≤ ν →
      vorticityEnstrophyBalanceAt ν u t →
        BKMLogSobolevGradientControlOn u T C Ω H →
          0 ≤ t →
            t ≤ T →
              Integrable (fun x => vorticityStretchingPower u t x) →
                Integrable (fun x => vorticityEnstrophyDensity u t x) →
                  vorticityEnstrophyGradientControlledAt ν u t
                    (bkmLogSobolevGradientEnvelope C Ω H t)

/-- Checked proof of the logarithmic-enstrophy growth package. -/
theorem BKMVorticityEnstrophyLogSobolevGrowthClosed_proved :
    BKMVorticityEnstrophyLogSobolevGrowthClosed := by
  intro ν T C u Ω H t hν hBal hLog ht0 htT hStretchInt hEnstrophyInt
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_control
      hν hBal hLog ht0 htT hStretchInt hEnstrophyInt

/-- Checked affine-logarithmic enstrophy growth package: a conventional
affine pointwise Biot-Savart/log-Sobolev estimate turns the BKM enstrophy
balance into `dE/dt <= (C0 + C1 * Omega log(e + H)) * E`. -/
def BKMVorticityEnstrophyAffineLogGrowthClosed : Prop :=
  ∀ (ν T C0 C1 : ℝ) (u : NSVelocityField) (Ω H : NSTime → ℝ) (t : NSTime),
    0 ≤ ν →
      vorticityEnstrophyBalanceAt ν u t →
        0 ≤ C0 →
          0 ≤ C1 →
            (∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s) →
              (∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s) →
                BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H →
                  0 ≤ t →
                    t ≤ T →
                      Integrable (fun x => vorticityStretchingPower u t x) →
                        Integrable (fun x => vorticityEnstrophyDensity u t x) →
                          vorticityEnstrophyGradientControlledAt ν u t
                            (C0 + C1 * bkmLogSobolevLogFactor Ω H t)

/-- Checked proof of the affine-logarithmic enstrophy growth package. -/
theorem BKMVorticityEnstrophyAffineLogGrowthClosed_proved :
    BKMVorticityEnstrophyAffineLogGrowthClosed := by
  intro ν T C0 C1 u Ω H t hν hBal hC0 hC1 hΩ hH hAffine
    ht0 htT hStretchInt hEnstrophyInt
  exact
    vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_affinePointwiseInequality
      hν hBal hC0 hC1 hΩ hH hAffine ht0 htT hStretchInt hEnstrophyInt

/-- Checked affine-logarithmic stretching-integral bound: the conventional
pointwise Biot-Savart/log-Sobolev gradient estimate directly bounds the
integrated BKM stretching production by
`(C0 + C1 * Omega log(e + H)) * int |omega|^2`. -/
def BKMVorticityStretchingAffineLogIntegralBoundClosed : Prop :=
  ∀ (T C0 C1 : ℝ) (u : NSVelocityField) (Ω H : NSTime → ℝ) (t : NSTime),
    0 ≤ C0 →
      0 ≤ C1 →
        (∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s) →
          (∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s) →
            BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H →
              0 ≤ t →
                t ≤ T →
                  Integrable (fun x => vorticityStretchingPower u t x) →
                    Integrable (fun x => vorticityEnstrophyDensity u t x) →
                      vorticityStretchingPowerIntegral u t ≤
                        (C0 + C1 * bkmLogSobolevLogFactor Ω H t) *
                          vorticityEnstrophyAt u t

/-- Checked proof of the affine-logarithmic stretching-integral package. -/
theorem BKMVorticityStretchingAffineLogIntegralBoundClosed_proved :
    BKMVorticityStretchingAffineLogIntegralBoundClosed := by
  intro T C0 C1 u Ω H t hC0 hC1 hΩ hH hAffine ht0 htT
    hStretchInt hEnstrophyInt
  exact
    vorticityStretchingPowerIntegral_le_affineLog_enstrophyAt
      hC0 hC1 hΩ hH hAffine ht0 htT hStretchInt hEnstrophyInt

/-- Checked finite-time witness affine-log enstrophy growth package.  This
packages the BKM hard core from standard vorticity equation plus time-pairing
derivative and Schwartz-slice identities to the affine-log differential
inequality for `1 / 2 * int |omega|^2`. -/
def BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed : Prop :=
  ∀ (ν T C0 C1 : ℝ) (u₀ : NSInitialVelocity)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω H : NSTime → ℝ) (t : NSTime),
    0 ≤ ν →
      concreteVorticityEquationOn ν W.velocity T →
        finiteTimeWitnessVelocitySchwartzSlices W →
          finiteTimeWitnessVorticitySchwartzSlices W →
            vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t →
              vorticityEnstrophyTimePairingDerivativeAt W.velocity t →
                0 ≤ C0 →
                  0 ≤ C1 →
                    (∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s) →
                      (∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s) →
                        BKMLogSobolevAffinePointwiseInequalityOn
                          W.velocity T C0 C1 Ω H →
                          0 ≤ t →
                            t ≤ T →
                              Integrable
                                (fun x => vorticityEnstrophyDensity W.velocity t x) →
                                vorticityEnstrophyGradientControlledAt ν W.velocity t
                                  (C0 + C1 * bkmLogSobolevLogFactor Ω H t)

/-- Checked proof of the finite-time witness affine-log enstrophy growth
package. -/
theorem BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed_proved :
    BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed := by
  intro ν T C0 C1 u₀ W Ω H t hν hEq hVelocitySlices hVorticitySlices
    hInt hTime hC0 hC1 hΩ hH hAffine ht0 htT hEnstrophyInt
  exact
    vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_affinePointwiseInequality
      W hν hEq hVelocitySlices hVorticitySlices hInt hTime hC0 hC1 hΩ hH
      hAffine ht0 htT hEnstrophyInt

/-- Checked finite-time witness affine-log enstrophy growth package with the
vorticity Schwartz-slice input derived from the velocity Schwartz slice. -/
def BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed : Prop :=
  ∀ (ν T C0 C1 : ℝ) (u₀ : NSInitialVelocity)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω H : NSTime → ℝ) (t : NSTime),
    0 ≤ ν →
      concreteVorticityEquationOn ν W.velocity T →
        finiteTimeWitnessVelocitySchwartzSlices W →
          vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t →
            vorticityEnstrophyTimePairingDerivativeAt W.velocity t →
              0 ≤ C0 →
                0 ≤ C1 →
                  (∀ s, 0 ≤ s → s ≤ T → 0 ≤ Ω s) →
                    (∀ s, 0 ≤ s → s ≤ T → 0 ≤ H s) →
                      BKMLogSobolevAffinePointwiseInequalityOn
                        W.velocity T C0 C1 Ω H →
                        0 ≤ t →
                          t ≤ T →
                            Integrable
                              (fun x => vorticityEnstrophyDensity W.velocity t x) →
                              vorticityEnstrophyGradientControlledAt ν W.velocity t
                                (C0 + C1 * bkmLogSobolevLogFactor Ω H t)

/-- Proof of the velocity-only Schwartz-slice finite-time witness affine-log
enstrophy growth package. -/
theorem BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed_proved :
    BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed := by
  intro ν T C0 C1 u₀ W Ω H t hν hEq hVelocitySlices hInt hTime hC0 hC1
    hΩ hH hAffine ht0 htT hEnstrophyInt
  exact
    vorticityEnstrophyGradientControlledAt_of_finiteTimeWitness_velocitySchwartz_affinePointwiseInequality
      W hν hEq hVelocitySlices hInt hTime hC0 hC1 hΩ hH hAffine ht0 htT
      hEnstrophyInt

/-- The downstream BKM growth estimates are closed once the analytic
log-Sobolev/Biot-Savart gradient control is supplied as an explicit
hypothesis. -/
def BKMLogSobolevGrowthEstimateClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T C : ℝ) (Ω H : NSTime → ℝ),
    concreteVorticityEquationOn ν u T →
      BKMLogSobolevGradientControlOn u T C Ω H →
        vorticityEnvelopeOn u T Ω →
          spatialGradientOperatorEnvelopeOn u T
              (bkmLogSobolevGradientEnvelope C Ω H) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              ‖vorticityMaterialDiffusionRemainder ν u t x‖ ≤
                bkmLogSobolevGradientEnvelope C Ω H t * Ω t) ∧
            (∀ t x, 0 ≤ t → t ≤ T →
              |vorticityMaterialDiffusionPower ν u t x| ≤
                bkmLogSobolevGradientEnvelope C Ω H t * (Ω t * Ω t))

/-- Checked proof of the log-Sobolev-control-to-growth package. -/
theorem BKMLogSobolevGrowthEstimateClosed_proved :
    BKMLogSobolevGrowthEstimateClosed := by
  intro ν u T C Ω H hEq hLog hΩ
  exact
    ⟨BKMLogSobolevGradientControlOn.to_spatialGradientOperatorEnvelopeOn hLog,
      fun t x ht0 htT =>
        norm_vorticityMaterialDiffusionRemainder_le_of_logSobolev_control
          hEq hLog hΩ ht0 htT,
      fun t x ht0 htT =>
        abs_vorticityMaterialDiffusionPower_le_of_logSobolev_control
          hEq hLog hΩ ht0 htT⟩

/-- Checked affine-log normalization package: the conventional two-constant
Biot-Savart/log-Sobolev pointwise estimate is enough to provide the exact
one-constant gradient-control predicate consumed by the BKM growth route. -/
def BKMLogSobolevAffineReductionClosed : Prop :=
  ∀ (u : NSVelocityField) (T C C0 C1 : ℝ) (Ω H : NSTime → ℝ),
    0 ≤ C →
      C0 ≤ C →
        C1 ≤ C →
          (∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t) →
            (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) →
              BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H →
                BKMLogSobolevGradientControlOn u T C Ω H

/-- Checked proof of the affine-log normalization package. -/
theorem BKMLogSobolevAffineReductionClosed_proved :
    BKMLogSobolevAffineReductionClosed := by
  intro u T C C0 C1 Ω H hC hC0 hC1 hΩ hH hAffine
  exact
    BKMLogSobolevGradientControlOn.of_affinePointwiseInequality
      hC hC0 hC1 hΩ hH hAffine

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
