import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMAnalyticReduction
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# BKM high-norm continuation assembly

The checked BKM route now has pointwise stretching estimates, the residual-curl
surface, the residual-curl expansion algebra, and the supplied-log-Sobolev
growth interface.  This module splits the remaining analytic continuation
lemma into the three concrete ingredients still needed by the classical BKM
argument.
-/

set_option autoImplicit false

noncomputable section

open scoped SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Sharper analytic log-Sobolev/Biot-Savart ingredient in the conventional
affine form: from BKM vorticity-envelope data, produce constants and a
nonnegative high-norm envelope satisfying
`||grad u|| <= C0 + C1 * Omega log(exp(1) + H)`.

The checked algebra in `NavierStokesBKMLogSobolevControl` normalizes this into
the one-constant gradient envelope used downstream. -/
def BKMLogSobolevAffinePointwiseFromEnvelope : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                vorticityEnvelopeOn W.velocity T Ω →
                  integrableVorticityEnvelopeOn Ω T B →
                    ∃ C0 : ℝ, ∃ C1 : ℝ, ∃ H : NSTime → ℝ,
                      0 ≤ C0 ∧
                        0 ≤ C1 ∧
                          (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
                            BKMLogSobolevAffinePointwiseInequalityOn
                              W.velocity T C0 C1 Ω H

/-- Concrete high-norm envelope used by the Biot-Savart/log-Sobolev proof
attempt.  At each time in the slab, the velocity slice must be represented by a
Schwartz map whose fourth Schwartz seminorm is bounded by `H`.

This is stronger than the current arbitrary finite-energy witness surface; it
is recorded only to expose the exact analytic theorem needed for the
Biot-Savart estimate. -/
def BKMLogSobolevSchwartzHighNormEnvelopeOn
    (u : NSVelocityField) (T : ℝ) (H : NSTime → ℝ) : Prop :=
  (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
    ∀ t, 0 ≤ t → t ≤ T →
      ∃ f : 𝓢(NSSpace, NSSpace),
        (∀ x, f x = u t x) ∧
          SchwartzMap.seminorm ℝ 0 4 f ≤ H t

/-- The extra high-norm-envelope extraction needed before the Schwartz-slice
Biot-Savart estimate can be applied to an arbitrary finite-energy witness. -/
def BKMFiniteTimeWitnessSchwartzHighNormEnvelopeFromBKMData : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                vorticityEnvelopeOn W.velocity T Ω →
                  integrableVorticityEnvelopeOn Ω T B →
                    ∃ H : NSTime → ℝ,
                      BKMLogSobolevSchwartzHighNormEnvelopeOn W.velocity T H

/-- Exact singular-integral theorem exposed by the Biot-Savart attempt:
for divergence-free whole-space velocity fields with a vorticity envelope and a
Schwartz high-norm envelope, prove the affine logarithmic pointwise gradient
bound.

The local proof search found Fourier/Schwartz/Sobolev infrastructure in
mathlib, but not the Biot-Savart/Riesz-transform/Calderon-Zygmund/BMO layer
needed to prove this theorem directly. -/
def BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate : Prop :=
  ∃ C0 : ℝ, ∃ C1 : ℝ,
    0 ≤ C0 ∧
      0 ≤ C1 ∧
        ∀ (u : NSVelocityField) (T : ℝ) (Ω H : NSTime → ℝ),
          smoothSpaceTimeVelocity u →
            (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) →
              vorticityEnvelopeOn u T Ω →
                BKMLogSobolevSchwartzHighNormEnvelopeOn u T H →
                  BKMLogSobolevAffinePointwiseInequalityOn u T C0 C1 Ω H

/-- Exact slice-level singular-integral theorem missing from mathlib for the
BKM route.  For one divergence-free Schwartz velocity slice on `ℝ^3`, a
uniform vorticity bound and a fourth Schwartz-seminorm bound must control the
spatial gradient by the conventional affine-log Biot-Savart estimate.

This is deliberately stated as a one-slice theorem: proving it requires the
Biot-Savart/Riesz-transform/Calderon-Zygmund/log-Sobolev machinery, while the
checked theorem below handles only the packaging from slices to the current
space-time BKM interface. -/
def BKMSchwartzSliceVorticityToGradientAffineLogEstimate : Prop :=
  ∃ C0 : ℝ, ∃ C1 : ℝ,
    0 ≤ C0 ∧
      0 ≤ C1 ∧
        ∀ (f : 𝓢(NSSpace, NSSpace)) (Ω H : ℝ),
          0 ≤ Ω →
            0 ≤ H →
              (∀ x,
                spatialDivergence
                  (fun _ : NSTime => fun y : NSSpace => f y) 0 x = 0) →
                (∀ x,
                  ‖spatialVorticity
                    (fun _ : NSTime => fun y : NSSpace => f y) 0 x‖ ≤ Ω) →
                  SchwartzMap.seminorm ℝ 0 4 f ≤ H →
                    ∀ x,
                      ‖spatialFDeriv
                        (fun _ : NSTime => fun y : NSSpace => f y) 0 x‖ ≤
                        C0 + C1 * (Ω * Real.log (Real.exp (1 : ℝ) + H))

/-- The exact one-slice singular-integral theorem implies the current
space-time Biot-Savart interface once a Schwartz representative and high-norm
envelope are supplied at each time. -/
theorem BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate_of_vorticityToGradient
    (hSlice : BKMSchwartzSliceVorticityToGradientAffineLogEstimate) :
    BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate := by
  rcases hSlice with ⟨C0, C1, hC0, hC1, hPointwise⟩
  refine ⟨C0, C1, hC0, hC1, ?_⟩
  intro u T Ω H _hu hdiv hΩ hH t x ht0 htT
  rcases hH.2 t ht0 htT with ⟨f, hf_eq, hf_seminorm⟩
  have hdiv_f :
      ∀ y,
        spatialDivergence
          (fun _ : NSTime => fun z : NSSpace => f z) 0 y = 0 := by
    intro y
    simpa [spatialDivergence, spatialFDeriv, hf_eq] using
      hdiv t y ht0 htT
  have hω_f :
      ∀ y,
        ‖spatialVorticity
          (fun _ : NSTime => fun z : NSSpace => f z) 0 y‖ ≤ Ω t := by
    intro y
    simpa [spatialVorticity, spatialDerivativeComponent, spatialFDeriv, hf_eq] using
      hΩ.2 t y ht0 htT
  have hgrad :=
    hPointwise f (Ω t) (H t) (hΩ.1 t ht0 htT) (hH.1 t ht0 htT)
      hdiv_f hω_f hf_seminorm x
  simpa [spatialFDeriv, hf_eq, bkmLogSobolevLogFactor] using hgrad

/-- A concrete Schwartz-slice high-norm extraction theorem plus the
Biot-Savart/Riesz affine-log pointwise estimate imply the first current open
BKM analytic lemma. -/
theorem BKMLogSobolevAffinePointwiseFromEnvelope_of_schwartzHighNormEnvelope_and_biotSavart
    (hHighNorm : BKMFiniteTimeWitnessSchwartzHighNormEnvelopeFromBKMData)
    (hBiotSavart : BKMSchwartzSliceBiotSavartAffineLogPointwiseEstimate) :
    BKMLogSobolevAffinePointwiseFromEnvelope := by
  intro ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt
  rcases hHighNorm ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨H, hH⟩
  rcases hBiotSavart with ⟨C0, C1, hC0, hC1, hPointwise⟩
  exact
    ⟨C0, C1, H, hC0, hC1, hH.1,
      hPointwise W.velocity T Ω H W.smooth_velocity
        (fun t x ht0 htT => W.incompressible_on t x ht0 htT) hΩ hH⟩

/-- Analytic log-Sobolev/Biot-Savart ingredient: once the standard vorticity
equation and BKM envelope data are available on a slab, produce a logarithmic
gradient-control envelope for the witness velocity. -/
def BKMLogSobolevGradientControlFromEnvelope : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                vorticityEnvelopeOn W.velocity T Ω →
                  integrableVorticityEnvelopeOn Ω T B →
                    ∃ C : ℝ, ∃ H : NSTime → ℝ,
                      BKMLogSobolevGradientControlOn W.velocity T C Ω H

/-- The sharper affine pointwise log-Sobolev component implies the older
one-constant gradient-control component. -/
theorem BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope) :
    BKMLogSobolevGradientControlFromEnvelope := by
  intro ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt
  rcases hAffine ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨C0, C1, H, hC0, hC1, hH, hAffinePointwise⟩
  refine ⟨max C0 C1, H, ?_⟩
  exact
    BKMLogSobolevGradientControlOn.of_affinePointwiseInequality_max
      hC0 hC1 hΩ.1 hH hAffinePointwise

/-- Analytic high-norm continuation ingredient: the standard vorticity equation,
an integrable vorticity envelope, and the corresponding logarithmic gradient
control extend the finite-time witness to the existing explicit global-output
surface. -/
def BKMHighNormContinuationFromLogControl : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B C : ℝ) (H : NSTime → ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              vorticityEnvelopeOn W.velocity T Ω →
                integrableVorticityEnvelopeOn Ω T B →
                  concreteVorticityEquationOn ν W.velocity T →
                    BKMLogSobolevGradientControlOn W.velocity T C Ω H →
                      ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- The normalized vorticity enstrophy is nonnegative on the unguarded integral
surface. -/
theorem normalizedVorticityEnstrophyAt_nonneg
    (u : NSVelocityField) (t : NSTime) :
    0 ≤ normalizedVorticityEnstrophyAt u t := by
  unfold normalizedVorticityEnstrophyAt
  nlinarith [vorticityEnstrophyAt_nonneg u t]

/-- The gradient-growth coefficient can be enlarged, since vorticity enstrophy
is nonnegative. -/
theorem vorticityEnstrophyGradientControlledAt.mono_coefficient
    {ν G K : ℝ} {u : NSVelocityField} {t : NSTime}
    (h : vorticityEnstrophyGradientControlledAt ν u t G)
    (hGK : G ≤ K) :
    vorticityEnstrophyGradientControlledAt ν u t K := by
  rcases h with ⟨D, hDderiv, hDle⟩
  refine ⟨D, hDderiv, ?_⟩
  exact hDle.trans
    (mul_le_mul_of_nonneg_right hGK (vorticityEnstrophyAt_nonneg u t))

/-- Constant-coefficient scalar Gronwall closure for the checked BKM
enstrophy-growth inequality.  This is the real ODE part of the high-norm
continuation step; it still needs a separate PDE continuation/local-existence
bridge to produce `ExplicitConcreteNavierStokesGlobalOutput`. -/
theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant
    {ν G T : ℝ} {u : NSVelocityField}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t G) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * G) 0 (t - 0) := by
  let D : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Ico 0 T then
      Classical.choose (hGrowth t ht)
    else
      0
  refine
    le_gronwallBound_of_liminf_deriv_right_le
      (f := fun t => normalizedVorticityEnstrophyAt u t)
      (f' := D)
      (δ := normalizedVorticityEnstrophyAt u 0)
      (K := 2 * G)
      (ε := 0)
      (a := 0)
      (b := T)
      hcont ?_ le_rfl ?_
  · intro t ht r hr
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have hderiv : HasDerivWithinAt
        (fun s => normalizedVorticityEnstrophyAt u s) (D t) (Set.Ici t) t := by
      rw [hD]
      exact hspec.1.hasDerivWithinAt
    exact hderiv.liminf_right_slope_le hr
  · intro t ht
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have hDle : D t ≤ G * vorticityEnstrophyAt u t := by
      rw [hD]
      exact hspec.2
    calc
      D t ≤ G * vorticityEnstrophyAt u t := hDle
      _ = (2 * G) * normalizedVorticityEnstrophyAt u t + 0 := by
            rw [normalizedVorticityEnstrophyAt]
            ring

/-- Constant-majorant version of the scalar Gronwall closure.  It is useful
when a time-dependent gradient envelope has already been bounded above by a
single slab constant. -/
theorem normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_majorized
    {ν K T : ℝ} {u : NSVelocityField} {G : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t))
    (hGle : ∀ t, t ∈ Set.Ico 0 T → G t ≤ K) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        gronwallBound (normalizedVorticityEnstrophyAt u 0) (2 * K) 0 (t - 0) :=
  normalizedVorticityEnstrophyAt_le_gronwallBound_of_gradientControlled_constant
    hcont
    (fun t ht =>
      (hGrowth t ht).mono_coefficient (hGle t ht))

/-- Variable-coefficient scalar Gronwall in integrating-factor form.  If `A`
is a right primitive of `2 * G`, then
`(1 / 2) * int |omega|^2 * exp (-A)` cannot increase on the slab.

This is the exact ODE comparison shape needed before instantiating `A` as an
integral primitive of the logarithmic BKM growth coefficient. -/
theorem normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t * Real.exp (-(A t)) ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (-(A 0)) := by
  let F : ℝ → ℝ := fun t => normalizedVorticityEnstrophyAt u t
  let D : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Ico 0 T then
      Classical.choose (hGrowth t ht)
    else
      0
  let Q : ℝ → ℝ := F * fun t => Real.exp (-(A t))
  let QD : ℝ → ℝ := fun t =>
    D t * Real.exp (-(A t)) + F t * (Real.exp (-(A t)) * (-(2 * G t)))
  have hQcont : ContinuousOn Q (Set.Icc 0 T) := by
    dsimp [Q, F]
    exact hcont.mul (Real.continuous_exp.comp_continuousOn hAcont.neg)
  have hQderiv :
      ∀ t, t ∈ Set.Ico 0 T → HasDerivWithinAt Q (QD t) (Set.Ici t) t := by
    intro t ht
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have hFderiv : HasDerivWithinAt F (D t) (Set.Ici t) t := by
      dsimp [F]
      rw [hD]
      exact hspec.1.hasDerivWithinAt
    have hExpDeriv :
        HasDerivWithinAt (fun s => Real.exp (-(A s)))
          (Real.exp (-(A t)) * (-(2 * G t))) (Set.Ici t) t := by
      exact ((hAderiv t ht).neg).exp
    have hprod := hFderiv.mul hExpDeriv
    simpa [Q, QD] using hprod
  have hQbound : ∀ t, t ∈ Set.Ico 0 T → QD t ≤ 0 := by
    intro t ht
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have hDle : D t ≤ G t * vorticityEnstrophyAt u t := by
      rw [hD]
      exact hspec.2
    have hDle_norm : D t ≤ (2 * G t) * F t := by
      calc
        D t ≤ G t * vorticityEnstrophyAt u t := hDle
        _ = (2 * G t) * F t := by
              dsimp [F]
              rw [normalizedVorticityEnstrophyAt]
              ring
    have hsub : D t - (2 * G t) * F t ≤ 0 := sub_nonpos.mpr hDle_norm
    have hexp_nonneg : 0 ≤ Real.exp (-(A t)) := Real.exp_nonneg _
    have hQD_eq :
        QD t = (D t - (2 * G t) * F t) * Real.exp (-(A t)) := by
      dsimp [QD]
      ring
    rw [hQD_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hsub hexp_nonneg
  have hcomp :
      ∀ t, t ∈ Set.Icc 0 T → Q t ≤ Q 0 := by
    simpa [gronwallBound_K0] using
      le_gronwallBound_of_liminf_deriv_right_le
        (f := Q)
        (f' := QD)
        (δ := Q 0)
        (K := 0)
        (ε := 0)
        (a := 0)
        (b := T)
        hQcont
        (fun t ht r hr => (hQderiv t ht).liminf_right_slope_le hr)
        le_rfl
        (by simpa using hQbound)
  exact hcomp

/-- Variable-coefficient scalar Gronwall in exponential form.  Supplying a
right primitive `A' = 2 * G` yields the usual bound
`E(t) <= E(0) * exp (A(t) - A(0))` for normalized vorticity enstrophy. -/
theorem normalizedVorticityEnstrophyAt_le_initial_mul_exp_antiderivative
    {ν T : ℝ} {u : NSVelocityField} {G A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * G t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t (G t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        normalizedVorticityEnstrophyAt u 0 * Real.exp (A t - A 0) := by
  intro t ht
  have hmul :=
    normalizedVorticityEnstrophyAt_mul_exp_neg_antiderivative_le_initial
      hcont hAcont hAderiv hGrowth t ht
  have hexp_pos : 0 < Real.exp (A t) := Real.exp_pos _
  have hscaled :=
    mul_le_mul_of_nonneg_right hmul (le_of_lt hexp_pos)
  have hcancel_t : Real.exp (-(A t)) * Real.exp (A t) = 1 := by
    rw [← Real.exp_add]
    have harg : -(A t) + A t = 0 := by ring
    rw [harg, Real.exp_zero]
  have hcombine :
      Real.exp (-(A 0)) * Real.exp (A t) = Real.exp (A t - A 0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    normalizedVorticityEnstrophyAt u t
        = normalizedVorticityEnstrophyAt u t * Real.exp (-(A t)) *
            Real.exp (A t) := by
          calc
            normalizedVorticityEnstrophyAt u t =
                normalizedVorticityEnstrophyAt u t * 1 := by ring
            _ = normalizedVorticityEnstrophyAt u t *
                (Real.exp (-(A t)) * Real.exp (A t)) := by
                  rw [hcancel_t]
            _ = normalizedVorticityEnstrophyAt u t * Real.exp (-(A t)) *
                Real.exp (A t) := by ring
    _ ≤ normalizedVorticityEnstrophyAt u 0 * Real.exp (-(A 0)) *
          Real.exp (A t) := hscaled
    _ = normalizedVorticityEnstrophyAt u 0 * Real.exp (A t - A 0) := by
          calc
            normalizedVorticityEnstrophyAt u 0 * Real.exp (-(A 0)) *
                Real.exp (A t) =
                normalizedVorticityEnstrophyAt u 0 *
                  (Real.exp (-(A 0)) * Real.exp (A t)) := by ring
            _ = normalizedVorticityEnstrophyAt u 0 * Real.exp (A t - A 0) := by
                  rw [hcombine]

/-- Scalar logarithmic Gronwall in BKM form.  If a nonnegative controlling
quantity `F` satisfies
`F' <= R(t) * (1 + log(exp(1) + F)) * F`, and `A' = R`, then the logarithmic
factor `1 + log(exp(1) + F)` times the integrating factor `exp(-A)` cannot
increase.

This is the ODE hard core behind the high-norm/BKM continuation step.  It does
not by itself construct the PDE continuation output. -/
theorem bkmScalarLogGronwallFactor_mul_exp_neg_antiderivative_le_initial
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      (1 + Real.log (Real.exp (1 : ℝ) + F t)) * Real.exp (-(A t)) ≤
        (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (-(A 0)) := by
  let Y : ℝ → ℝ := fun t => 1 + Real.log (Real.exp (1 : ℝ) + F t)
  let D : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Ico 0 T then
      Classical.choose (hGrowth t ht)
    else
      0
  let YD : ℝ → ℝ := fun t => D t / (Real.exp (1 : ℝ) + F t)
  let Q : ℝ → ℝ := Y * fun t => Real.exp (-(A t))
  let QD : ℝ → ℝ := fun t =>
    YD t * Real.exp (-(A t)) + Y t * (Real.exp (-(A t)) * (-(R t)))
  have hLogcont :
      ContinuousOn (fun t => Real.log (Real.exp (1 : ℝ) + F t))
        (Set.Icc 0 T) := by
    refine Real.continuousOn_log.comp' ?_ ?_
    · exact continuousOn_const.add hFcont
    · intro t ht
      have harg_pos : 0 < Real.exp (1 : ℝ) + F t := by
        linarith [Real.exp_pos (1 : ℝ), hFnonneg t ht]
      exact harg_pos.ne'
  have hYcont : ContinuousOn Y (Set.Icc 0 T) := by
    dsimp [Y]
    exact continuousOn_const.add hLogcont
  have hQcont : ContinuousOn Q (Set.Icc 0 T) := by
    dsimp [Q]
    exact hYcont.mul (Real.continuous_exp.comp_continuousOn hAcont.neg)
  have hYderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt Y (YD t) (Set.Ici t) t := by
    intro t ht
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have hFderiv : HasDerivWithinAt F (D t) (Set.Ici t) t := by
      rw [hD]
      exact hspec.1
    have hArgDeriv :
        HasDerivWithinAt (fun s => Real.exp (1 : ℝ) + F s) (D t)
          (Set.Ici t) t := by
      simpa using hFderiv.const_add (Real.exp (1 : ℝ))
    have harg_pos : 0 < Real.exp (1 : ℝ) + F t := by
      have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
      linarith [Real.exp_pos (1 : ℝ), hFnonneg t htIcc]
    have hLogDeriv :
        HasDerivWithinAt
          (fun s => Real.log (Real.exp (1 : ℝ) + F s))
          (D t / (Real.exp (1 : ℝ) + F t)) (Set.Ici t) t :=
      hArgDeriv.log harg_pos.ne'
    simpa [Y, YD] using hLogDeriv.const_add 1
  have hYDerivBound :
      ∀ t, t ∈ Set.Ico 0 T → YD t ≤ R t * Y t := by
    intro t ht
    have hspec := Classical.choose_spec (hGrowth t ht)
    have hD : D t = Classical.choose (hGrowth t ht) := by
      unfold D
      rw [dif_pos ht]
    have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
    have hF_nonneg_t : 0 ≤ F t := hFnonneg t htIcc
    have harg_pos : 0 < Real.exp (1 : ℝ) + F t := by
      linarith [Real.exp_pos (1 : ℝ), hF_nonneg_t]
    have hDle : D t ≤ R t * Y t * F t := by
      rw [hD]
      simpa [Y, mul_assoc] using hspec.2
    have hlog_nonneg :
        0 ≤ Real.log (Real.exp (1 : ℝ) + F t) := by
      have hexp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      have harg_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) + F t := by
        linarith
      exact Real.log_nonneg harg_one
    have hY_nonneg : 0 ≤ Y t := by
      dsimp [Y]
      linarith
    have hRY_nonneg : 0 ≤ R t * Y t :=
      mul_nonneg (hRnonneg t ht) hY_nonneg
    have hF_le_arg : F t ≤ Real.exp (1 : ℝ) + F t := by
      linarith [Real.exp_pos (1 : ℝ)]
    have hmul_le :
        (R t * Y t) * F t ≤
          (R t * Y t) * (Real.exp (1 : ℝ) + F t) :=
      mul_le_mul_of_nonneg_left hF_le_arg hRY_nonneg
    calc
      YD t = D t / (Real.exp (1 : ℝ) + F t) := rfl
      _ ≤ (R t * Y t * F t) / (Real.exp (1 : ℝ) + F t) :=
          div_le_div_of_nonneg_right hDle (le_of_lt harg_pos)
      _ ≤ R t * Y t := by
        rw [div_le_iff₀ harg_pos]
        nlinarith [hmul_le]
  have hQderiv :
      ∀ t, t ∈ Set.Ico 0 T → HasDerivWithinAt Q (QD t) (Set.Ici t) t := by
    intro t ht
    have hExpDeriv :
        HasDerivWithinAt (fun s => Real.exp (-(A s)))
          (Real.exp (-(A t)) * (-(R t))) (Set.Ici t) t := by
      exact ((hAderiv t ht).neg).exp
    have hprod := (hYderiv t ht).mul hExpDeriv
    simpa [Q, QD] using hprod
  have hQbound : ∀ t, t ∈ Set.Ico 0 T → QD t ≤ 0 := by
    intro t ht
    have hsub : YD t - R t * Y t ≤ 0 := sub_nonpos.mpr (hYDerivBound t ht)
    have hexp_nonneg : 0 ≤ Real.exp (-(A t)) := Real.exp_nonneg _
    have hQD_eq :
        QD t = (YD t - R t * Y t) * Real.exp (-(A t)) := by
      dsimp [QD]
      ring
    rw [hQD_eq]
    exact mul_nonpos_of_nonpos_of_nonneg hsub hexp_nonneg
  have hcomp :
      ∀ t, t ∈ Set.Icc 0 T → Q t ≤ Q 0 := by
    simpa [gronwallBound_K0] using
      le_gronwallBound_of_liminf_deriv_right_le
        (f := Q)
        (f' := QD)
        (δ := Q 0)
        (K := 0)
        (ε := 0)
        (a := 0)
        (b := T)
        hQcont
        (fun t ht r hr => (hQderiv t ht).liminf_right_slope_le hr)
        le_rfl
        (by simpa using hQbound)
  exact hcomp

/-- Exponential form of the scalar BKM logarithmic Gronwall estimate. -/
theorem bkmScalarLogGronwallFactor_le_initial_mul_exp_antiderivative
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      1 + Real.log (Real.exp (1 : ℝ) + F t) ≤
        (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (A t - A 0) := by
  intro t ht
  have hmul :=
    bkmScalarLogGronwallFactor_mul_exp_neg_antiderivative_le_initial
      hFcont hAcont hFnonneg hRnonneg hAderiv hGrowth t ht
  have hexp_pos : 0 < Real.exp (A t) := Real.exp_pos _
  have hscaled :=
    mul_le_mul_of_nonneg_right hmul (le_of_lt hexp_pos)
  have hcancel_t : Real.exp (-(A t)) * Real.exp (A t) = 1 := by
    rw [← Real.exp_add]
    have harg : -(A t) + A t = 0 := by ring
    rw [harg, Real.exp_zero]
  have hcombine :
      Real.exp (-(A 0)) * Real.exp (A t) = Real.exp (A t - A 0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    1 + Real.log (Real.exp (1 : ℝ) + F t)
        = (1 + Real.log (Real.exp (1 : ℝ) + F t)) *
            Real.exp (-(A t)) * Real.exp (A t) := by
          calc
            1 + Real.log (Real.exp (1 : ℝ) + F t) =
                (1 + Real.log (Real.exp (1 : ℝ) + F t)) * 1 := by ring
            _ = (1 + Real.log (Real.exp (1 : ℝ) + F t)) *
                (Real.exp (-(A t)) * Real.exp (A t)) := by
                  rw [hcancel_t]
            _ = (1 + Real.log (Real.exp (1 : ℝ) + F t)) *
                Real.exp (-(A t)) * Real.exp (A t) := by ring
    _ ≤ (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (-(A 0)) * Real.exp (A t) := hscaled
    _ = (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (A t - A 0) := by
          calc
            (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
                Real.exp (-(A 0)) * Real.exp (A t) =
                (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
                  (Real.exp (-(A 0)) * Real.exp (A t)) := by ring
            _ = (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
                Real.exp (A t - A 0) := by
                  rw [hcombine]

/-- Direct value bound derived from the scalar BKM logarithmic Gronwall
estimate.  The right side is intentionally coarse but has the expected BKM
shape: finite primitive `A` gives a finite exponential bound for the
controlling quantity `F`. -/
theorem bkmScalarLogGronwallValue_le_exp_initial_logFactor_mul_exp_antiderivative
    {T : ℝ} {F R A : NSTime → ℝ}
    (hFcont : ContinuousOn F (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hFnonneg : ∀ t, t ∈ Set.Icc 0 T → 0 ≤ F t)
    (hRnonneg : ∀ t, t ∈ Set.Ico 0 T → 0 ≤ R t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (R t) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        ∃ D : ℝ,
          HasDerivWithinAt F D (Set.Ici t) t ∧
            D ≤ R t *
              (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t) :
    ∀ t, t ∈ Set.Icc 0 T →
      F t ≤
        Real.exp
          ((1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
            Real.exp (A t - A 0)) := by
  intro t ht
  have hlogFactor :=
    bkmScalarLogGronwallFactor_le_initial_mul_exp_antiderivative
      hFcont hAcont hFnonneg hRnonneg hAderiv hGrowth t ht
  have harg_pos : 0 < Real.exp (1 : ℝ) + F t := by
    linarith [Real.exp_pos (1 : ℝ), hFnonneg t ht]
  have hlog_le :
      Real.log (Real.exp (1 : ℝ) + F t) ≤
        (1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
          Real.exp (A t - A 0) := by
    linarith
  have harg_le :
      Real.exp (1 : ℝ) + F t ≤
        Real.exp
          ((1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
            Real.exp (A t - A 0)) :=
    (Real.log_le_iff_le_exp harg_pos).mp hlog_le
  calc
    F t ≤ Real.exp (1 : ℝ) + F t := by
      linarith [Real.exp_pos (1 : ℝ)]
    _ ≤ Real.exp
          ((1 + Real.log (Real.exp (1 : ℝ) + F 0)) *
            Real.exp (A t - A 0)) := harg_le

/-- BKM log-Sobolev coefficient instantiation of scalar logarithmic Gronwall
for normalized vorticity enstrophy.  The remaining analytic PDE work is to
produce the continuity, growth, primitive, and high-norm-domination hypotheses
from an arbitrary finite-time witness and then use the resulting finite bound
in a continuation/local-existence bridge. -/
theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevGradientControlled
    {ν T C : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hGrowth :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyGradientControlledAt ν u t
          (bkmLogSobolevGradientEnvelope C Ω H t)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (A t - A 0)) := by
  let F : NSTime → ℝ := fun t => normalizedVorticityEnstrophyAt u t
  let R : NSTime → ℝ := fun t => 2 * C * (1 + Ω t)
  refine
    bkmScalarLogGronwallValue_le_exp_initial_logFactor_mul_exp_antiderivative
      (F := F) (R := R) (A := A)
      hcont hAcont
      (fun t _ht => normalizedVorticityEnstrophyAt_nonneg u t)
      ?_ ?_ ?_
  · intro t ht
    have hΩt : 0 ≤ Ω t := hΩ_nonneg t ht.1 (le_of_lt ht.2)
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (by linarith)
  · intro t ht
    exact hAderiv t ht
  · intro t ht
    rcases hGrowth t ht with ⟨D, hDderiv, hDle⟩
    refine ⟨D, hDderiv.hasDerivWithinAt, ?_⟩
    have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
    have hΩt : 0 ≤ Ω t := hΩ_nonneg t ht.1 (le_of_lt ht.2)
    have hHt : 0 ≤ H t := hH_nonneg t ht.1 (le_of_lt ht.2)
    have hFnonneg : 0 ≤ F t := normalizedVorticityEnstrophyAt_nonneg u t
    have hCoeff :
        bkmLogSobolevGradientEnvelope C Ω H t ≤
          C * (1 + Ω t) *
            (1 + Real.log (Real.exp (1 : ℝ) + F t)) :=
      bkmLogSobolevGradientEnvelope_le_scalarLogGrowthCoefficient
        hC hΩt hHt (hH_le_enstrophy t htIcc)
    have hEnstrophy_eq : vorticityEnstrophyAt u t = 2 * F t := by
      dsimp [F]
      rw [normalizedVorticityEnstrophyAt]
      ring
    have htwoF_nonneg : 0 ≤ 2 * F t := by
      nlinarith
    calc
      D ≤ bkmLogSobolevGradientEnvelope C Ω H t *
            vorticityEnstrophyAt u t := hDle
      _ = bkmLogSobolevGradientEnvelope C Ω H t * (2 * F t) := by
            rw [hEnstrophy_eq]
      _ ≤ (C * (1 + Ω t) *
              (1 + Real.log (Real.exp (1 : ℝ) + F t))) *
            (2 * F t) :=
            mul_le_mul_of_nonneg_right hCoeff htwoF_nonneg
      _ = R t * (1 + Real.log (Real.exp (1 : ℝ) + F t)) * F t := by
            dsimp [R]
            ring

/-- Version of
`normalizedVorticityEnstrophyAt_le_exp_of_logSobolevGradientControlled` that
uses the checked BKM enstrophy-growth theorem from a supplied log-Sobolev
gradient control plus the local enstrophy balance and integrability data. -/
theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance
    {ν T C : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hν : 0 ≤ ν)
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hBal :
      ∀ t, t ∈ Set.Ico 0 T → vorticityEnstrophyBalanceAt ν u t)
    (hStretchInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (A t - A 0)) := by
  exact
    normalizedVorticityEnstrophyAt_le_exp_of_logSobolevGradientControlled
      hcont hAcont hC hΩ_nonneg hH_nonneg hH_le_enstrophy hAderiv
      (fun t ht =>
        vorticityEnstrophyGradientControlledAt_of_balance_logSobolev_control
          hν (hBal t ht) hLog ht.1 (le_of_lt ht.2)
          (hStretchInt t ht) (hEnstrophyInt t ht))

/-- Bounded-primitive form of the BKM log-Sobolev enstrophy estimate.  Once a
right primitive of `2*C*(1+Omega)` is bounded above on the slab, the previous
scalar log-Gronwall estimate gives a single finite scalar bound for normalized
vorticity enstrophy on the whole slab. -/
theorem normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance_of_antiderivative_bounded
    {ν T C Amax : ℝ} {u : NSVelocityField} {Ω H A : NSTime → ℝ}
    (hcont :
      ContinuousOn (fun t => normalizedVorticityEnstrophyAt u t)
        (Set.Icc 0 T))
    (hAcont : ContinuousOn A (Set.Icc 0 T))
    (hν : 0 ≤ ν)
    (hC : 0 ≤ C)
    (hΩ_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ Ω t)
    (hH_nonneg : ∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t)
    (hH_le_enstrophy :
      ∀ t, t ∈ Set.Icc 0 T → H t ≤ normalizedVorticityEnstrophyAt u t)
    (hAderiv :
      ∀ t, t ∈ Set.Ico 0 T →
        HasDerivWithinAt A (2 * C * (1 + Ω t)) (Set.Ici t) t)
    (hA_le : ∀ t, t ∈ Set.Icc 0 T → A t ≤ Amax)
    (hLog : BKMLogSobolevGradientControlOn u T C Ω H)
    (hBal :
      ∀ t, t ∈ Set.Ico 0 T → vorticityEnstrophyBalanceAt ν u t)
    (hStretchInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityStretchingPower u t x))
    (hEnstrophyInt :
      ∀ t, t ∈ Set.Ico 0 T →
        MeasureTheory.Integrable (fun x => vorticityEnstrophyDensity u t x)) :
    ∀ t, t ∈ Set.Icc 0 T →
      normalizedVorticityEnstrophyAt u t ≤
        Real.exp
          ((1 + Real.log
              (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
            Real.exp (Amax - A 0)) := by
  intro t ht
  have hbase :=
    normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance
      hcont hAcont hν hC hΩ_nonneg hH_nonneg hH_le_enstrophy
      hAderiv hLog hBal hStretchInt hEnstrophyInt t ht
  have hF0 : 0 ≤ normalizedVorticityEnstrophyAt u 0 :=
    normalizedVorticityEnstrophyAt_nonneg u 0
  have hlog_nonneg :
      0 ≤ Real.log
        (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0) := by
    have hexp_one : (1 : ℝ) ≤ Real.exp (1 : ℝ) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    have harg_one :
        (1 : ℝ) ≤ Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0 := by
      linarith
    exact Real.log_nonneg harg_one
  have hfactor_nonneg :
      0 ≤ 1 + Real.log
        (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0) := by
    linarith
  have hAexp_le :
      Real.exp (A t - A 0) ≤ Real.exp (Amax - A 0) :=
    Real.exp_le_exp.mpr (by linarith [hA_le t ht])
  have hinner_le :
      (1 + Real.log
          (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
        Real.exp (A t - A 0) ≤
      (1 + Real.log
          (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt u 0)) *
        Real.exp (Amax - A 0) :=
    mul_le_mul_of_nonneg_left hAexp_le hfactor_nonneg
  exact hbase.trans (Real.exp_le_exp.mpr hinner_le)

/-- Exact residual needed to turn supplied BKM log-Sobolev control on an
arbitrary finite-time witness into the hypotheses of the checked scalar
log-Gronwall enstrophy estimate.  This includes continuity of the normalized
enstrophy scalar, a bounded primitive for `2*C*(1+Omega)`, high-norm envelope
domination by that scalar, and the local balance/integrability inputs.  The
nonnegativity of `Omega` is not part of this residual: it is already carried by
`vorticityEnvelopeOn`. -/
def BKMLogControlWitnessEnstrophyGronwallDataFromWitness : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B C : ℝ) (H : NSTime → ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              vorticityEnvelopeOn W.velocity T Ω →
                integrableVorticityEnvelopeOn Ω T B →
                  concreteVorticityEquationOn ν W.velocity T →
                    BKMLogSobolevGradientControlOn W.velocity T C Ω H →
                      ∃ A : NSTime → ℝ, ∃ Amax : ℝ,
                        ContinuousOn
                          (fun t => normalizedVorticityEnstrophyAt W.velocity t)
                          (Set.Icc 0 T) ∧
                        ContinuousOn A (Set.Icc 0 T) ∧
                        0 ≤ C ∧
                        (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
                        (∀ t, t ∈ Set.Icc 0 T →
                          H t ≤ normalizedVorticityEnstrophyAt W.velocity t) ∧
                        (∀ t, t ∈ Set.Ico 0 T →
                          HasDerivWithinAt A (2 * C * (1 + Ω t))
                            (Set.Ici t) t) ∧
                        (∀ t, t ∈ Set.Icc 0 T → A t ≤ Amax) ∧
                        (∀ t, t ∈ Set.Ico 0 T →
                          vorticityEnstrophyBalanceAt ν W.velocity t) ∧
                        (∀ t, t ∈ Set.Ico 0 T →
                          MeasureTheory.Integrable
                            (fun x => vorticityStretchingPower W.velocity t x)) ∧
                        (∀ t, t ∈ Set.Ico 0 T →
                          MeasureTheory.Integrable
                            (fun x => vorticityEnstrophyDensity W.velocity t x))

/-- Sharper scalar-data residual for the high-norm Gronwall route.  The
balance and integrability hypotheses are no longer bundled here: they are
derived below from velocity Schwartz slices and the time-pairing derivative.
What remains is the genuinely scalar part of the witness extraction, namely
continuity of normalized enstrophy, signs, high-norm domination by normalized
enstrophy, and a bounded right primitive for `2*C*(1+Omega)`. -/
def BKMLogControlWitnessScalarGronwallDataFromWitness : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B C : ℝ) (H : NSTime → ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              vorticityEnvelopeOn W.velocity T Ω →
                integrableVorticityEnvelopeOn Ω T B →
                  concreteVorticityEquationOn ν W.velocity T →
                    BKMLogSobolevGradientControlOn W.velocity T C Ω H →
                      finiteTimeWitnessVelocitySchwartzSlices W →
                        (∀ t, t ∈ Set.Ico 0 T →
                          vorticityEnstrophyTimePairingDerivativeAt W.velocity t) →
                          ∃ A : NSTime → ℝ, ∃ Amax : ℝ,
                            ContinuousOn
                              (fun t => normalizedVorticityEnstrophyAt W.velocity t)
                              (Set.Icc 0 T) ∧
                            ContinuousOn A (Set.Icc 0 T) ∧
                            0 ≤ C ∧
                            (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
                            (∀ t, t ∈ Set.Icc 0 T →
                              H t ≤ normalizedVorticityEnstrophyAt W.velocity t) ∧
                            (∀ t, t ∈ Set.Ico 0 T →
                              HasDerivWithinAt A (2 * C * (1 + Ω t))
                                (Set.Ici t) t) ∧
                            (∀ t, t ∈ Set.Icc 0 T → A t ≤ Amax)

/-- Velocity Schwartz slices plus the time-pairing derivative discharge the
balance and integrability parts of
`BKMLogControlWitnessEnstrophyGronwallDataFromWitness`.  This isolates the
remaining high-norm/Gronwall extraction work to scalar continuity, primitive,
sign, and domination data. -/
theorem BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_scalarGronwallData_velocitySchwartz
    (hScalar : BKMLogControlWitnessScalarGronwallDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Ico 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t) :
    BKMLogControlWitnessEnstrophyGronwallDataFromWitness := by
  intro ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite hΩ hInt hEq hLog
  have hSlices : finiteTimeWitnessVelocitySchwartzSlices W :=
    hVelocitySlices ν u₀ T W hT hν hsmooth hdiv hfinite
  have hTime :
      ∀ t, t ∈ Set.Ico 0 T →
        vorticityEnstrophyTimePairingDerivativeAt W.velocity t := by
    intro t ht
    exact hTimePairing ν u₀ T W t hT hν hsmooth hdiv hfinite ht
  rcases hScalar ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite hΩ hInt hEq hLog
      hSlices hTime with
    ⟨A, Amax, hcont, hAcont, hC, hH_nonneg, hH_le_enstrophy, hAderiv,
      hA_le⟩
  refine
    ⟨A, Amax, hcont, hAcont, hC, hH_nonneg, hH_le_enstrophy, hAderiv,
      hA_le, ?_, ?_, ?_⟩
  · intro t ht
    have htT : t ≤ T := le_of_lt ht.2
    have hRawInt :
        vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t :=
      vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocitySchwartzSlices
        W hSlices ht.1 htT
    have hRaw : vorticityEnstrophyRawBalanceAt ν W.velocity t :=
      vorticityEnstrophyRawBalanceAt_of_timePairingDerivative_concreteVorticityEquationOn
        hEq hRawInt (hTime t ht) ht.1 htT
    exact
      vorticityEnstrophyBalanceAt_of_rawBalance_finiteTimeWitnessVelocitySchwartzSlices
        W hSlices hRaw ht.1 htT
  · intro t ht
    have htT : t ≤ T := le_of_lt ht.2
    have hRawInt :
        vorticityRawBalanceIntegralComponentsIntegrableAt W.velocity t :=
      vorticityRawBalanceIntegralComponentsIntegrableAt_of_finiteTimeWitnessVelocitySchwartzSlices
        W hSlices ht.1 htT
    exact hRawInt.2.2
  · intro t ht
    exact
      integrable_vorticityEnstrophyDensity_of_finiteTimeWitnessVelocitySchwartzSlices
        W hSlices ht.1 (le_of_lt ht.2)

/-- Exact PDE continuation bridge still missing after the scalar high-norm
work: a finite scalar bound for normalized vorticity enstrophy on the witness
slab must be converted into the existing fully explicit global-output surface.
This is deliberately stated over the current witness and output APIs. -/
def BKMBoundedEnstrophyContinuationBridge : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (M : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                0 ≤ M →
                  (∀ t, t ∈ Set.Icc 0 T →
                    normalizedVorticityEnstrophyAt W.velocity t ≤ M) →
                    ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- The high-norm continuation component follows once the arbitrary-witness
Gronwall data are extracted and finite bounded enstrophy is connected to the
existing global-output surface.  This proves the scalar/Gronwall half of the
high-norm route while keeping the remaining PDE continuation bridge explicit. -/
theorem BKMHighNormContinuationFromLogControl_of_enstrophyGronwallData_and_boundedEnstrophyBridge
    (hData : BKMLogControlWitnessEnstrophyGronwallDataFromWitness)
    (hBridge : BKMBoundedEnstrophyContinuationBridge) :
    BKMHighNormContinuationFromLogControl := by
  intro ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite hΩ hInt hEq hLog
  rcases hData ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite hΩ hInt hEq hLog with
    ⟨A, Amax, hcont, hAcont, hC, hH_nonneg, hH_le_enstrophy,
      hAderiv, hA_le, hBal, hStretchInt, hEnstrophyInt⟩
  let M : ℝ :=
    Real.exp
      ((1 + Real.log
          (Real.exp (1 : ℝ) + normalizedVorticityEnstrophyAt W.velocity 0)) *
        Real.exp (Amax - A 0))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact Real.exp_nonneg _
  have hBound :
      ∀ t, t ∈ Set.Icc 0 T →
        normalizedVorticityEnstrophyAt W.velocity t ≤ M := by
    dsimp [M]
    exact
      normalizedVorticityEnstrophyAt_le_exp_of_logSobolevControl_balance_of_antiderivative_bounded
        hcont hAcont (le_of_lt hν) hC hΩ.1 hH_nonneg
        hH_le_enstrophy hAderiv hA_le hLog hBal hStretchInt hEnstrophyInt
  exact
    hBridge ν u₀ T W M hT hν hsmooth hdiv hfinite hEq hM_nonneg hBound

/-- Direct sharpened high-norm route: after the checked scalar/log-Gronwall
layer, velocity-slice and time-pairing extraction discharge the balance and
integrability hypotheses; the only remaining inputs are scalar Gronwall data
and the bounded-enstrophy continuation bridge. -/
theorem BKMHighNormContinuationFromLogControl_of_scalarGronwallData_velocitySchwartz_and_boundedEnstrophyBridge
    (hScalar : BKMLogControlWitnessScalarGronwallDataFromWitness)
    (hVelocitySlices :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  finiteTimeWitnessVelocitySchwartzSlices W)
    (hTimePairing :
      ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
          (W : ExplicitFiniteTimeRegularityWitness ν u₀ T) (t : NSTime),
        0 ≤ T →
          0 < ν →
            smoothInitialVelocityData u₀ →
              (∀ x, initialSpatialDivergence u₀ x = 0) →
                finiteInitialKineticEnergy u₀ →
                  t ∈ Set.Ico 0 T →
                    vorticityEnstrophyTimePairingDerivativeAt W.velocity t)
    (hBridge : BKMBoundedEnstrophyContinuationBridge) :
    BKMHighNormContinuationFromLogControl := by
  exact
    BKMHighNormContinuationFromLogControl_of_enstrophyGronwallData_and_boundedEnstrophyBridge
      (BKMLogControlWitnessEnstrophyGronwallDataFromWitness_of_scalarGronwallData_velocitySchwartz
        hScalar hVelocitySlices hTimePairing)
      hBridge

/-- Componentized form of the remaining BKM analytic route.  The first
component is the residual-curl expansion identity, the second supplies the
logarithmic gradient envelope from BKM data, and the third closes the high-norm
continuation step. -/
def BKMAnalyticComponentsClosed : Prop :=
  BKMResidualCurlExpansionDefectVanishes ∧
    BKMLogSobolevGradientControlFromEnvelope ∧
      BKMHighNormContinuationFromLogControl

/-- Componentized BKM route with the log-Sobolev ingredient stated in the
conventional affine pointwise form. -/
def BKMAffineLogSobolevAnalyticComponentsClosed : Prop :=
  BKMResidualCurlExpansionDefectVanishes ∧
    BKMLogSobolevAffinePointwiseFromEnvelope ∧
      BKMHighNormContinuationFromLogControl

/-- Single named analytic lemma left after the checked BKM scaffolding.

For an arbitrary genuine finite-energy finite-time witness with the standard
vorticity equation and an integrable vorticity envelope, the classical analytic
work must produce both:
* affine Biot-Savart/log-Sobolev pointwise gradient constants and high-norm
  envelope, and
* the high-norm/Gronwall continuation output.

This is not a new witness class: it quantifies over
`ExplicitFiniteTimeRegularityWitness` directly. -/
def BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma : Prop :=
  ∀ (ν : ℝ) (u₀ : NSInitialVelocity) (T : ℝ)
      (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
      (Ω : NSTime → ℝ) (B : ℝ),
    0 ≤ T →
      0 < ν →
        smoothInitialVelocityData u₀ →
          (∀ x, initialSpatialDivergence u₀ x = 0) →
            finiteInitialKineticEnergy u₀ →
              concreteVorticityEquationOn ν W.velocity T →
                vorticityEnvelopeOn W.velocity T Ω →
                  integrableVorticityEnvelopeOn Ω T B →
                    ∃ C0 : ℝ, ∃ C1 : ℝ, ∃ H : NSTime → ℝ,
                      0 ≤ C0 ∧
                        0 ≤ C1 ∧
                          (∀ t, 0 ≤ t → t ≤ T → 0 ≤ H t) ∧
                            BKMLogSobolevAffinePointwiseInequalityOn
                              W.velocity T C0 C1 Ω H ∧
                              ExplicitConcreteNavierStokesGlobalOutput ν u₀

/-- The affine-log component bundle implies the older component bundle. -/
theorem BKMAffineLogSobolevAnalyticComponentsClosed.implies_BKMAnalyticComponentsClosed
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    BKMAnalyticComponentsClosed := by
  exact
    ⟨h.1,
      BKMLogSobolevGradientControlFromEnvelope_of_affinePointwiseFromEnvelope h.2.1,
      h.2.2⟩

/-- The three analytic components imply the previous single continuation
lemma. -/
theorem BKMAnalyticContinuationLemma_of_components
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticContinuationLemma := by
  intro ν u₀ T hT hν hsmooth hdiv hfinite W hCurl hEnv
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  have hEq : concreteVorticityEquationOn ν W.velocity T :=
    hDefect.implies_concreteVorticityEquationOn W.smooth_velocity
      (fun t x ht0 htT => W.incompressible_on t x ht0 htT)
      hCurl
  rcases hLog ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨C, H, hLogControl⟩
  exact hHigh ν u₀ T W Ω B C H hT hν hsmooth hdiv hfinite
    hΩ hInt hEq hLogControl

/-- Bundled component form implies the previous single continuation lemma. -/
theorem BKMAnalyticComponentsClosed.implies_BKMAnalyticContinuationLemma
    (h : BKMAnalyticComponentsClosed) :
    BKMAnalyticContinuationLemma := by
  exact BKMAnalyticContinuationLemma_of_components h.1 h.2.1 h.2.2

/-- The repaired nonnegative-horizon BKM target follows from the componentized
analytic route. -/
theorem BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : BKMAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons :=
  BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    h.implies_BKMAnalyticContinuationLemma

/-- The affine-log component bundle implies the repaired nonnegative-horizon
BKM target through the checked affine normalization. -/
theorem BKMAffineLogSobolevAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (h : BKMAffineLogSobolevAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons :=
  BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (BKMAffineLogSobolevAnalyticComponentsClosed.implies_BKMAnalyticComponentsClosed h)

/-- The previous two-component analytic route implies the single direct
arbitrary-witness lemma. -/
theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma_of_components
    (hAffine : BKMLogSobolevAffinePointwiseFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma := by
  intro ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt
  rcases hAffine ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨C0, C1, H, hC0, hC1, hH, hAffinePointwise⟩
  have hLog :
      BKMLogSobolevGradientControlOn W.velocity T (max C0 C1) Ω H :=
    BKMLogSobolevGradientControlOn.of_affinePointwiseInequality_max
      hC0 hC1 hΩ.1 hH hAffinePointwise
  exact
    ⟨C0, C1, H, hC0, hC1, hH, hAffinePointwise,
      hHigh ν u₀ T W Ω B (max C0 C1) H
        hT hν hsmooth hdiv hfinite hΩ hInt hEq hLog⟩

/-- The repaired nonnegative-horizon BKM target follows from the single named
arbitrary-witness affine-log/Biot-Savart/Gronwall continuation lemma once the
residual-curl defect closure is supplied. -/
theorem BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (h : BKMArbitraryWitnessAffineLogBiotSavartGronwallContinuationLemma) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  intro ν u₀ T hT hν hsmooth hdiv hfinite W hEnv
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  have hEq : concreteVorticityEquationOn ν W.velocity T :=
    hDefect.implies_concreteVorticityEquationOn W.smooth_velocity
      (fun t x ht0 htT => W.incompressible_on t x ht0 htT)
      W.vorticityResidualCurlEquationOn
  rcases h ν u₀ T W Ω B hT hν hsmooth hdiv hfinite hEq hΩ hInt with
    ⟨_C0, _C1, _H, _hC0, _hC1, _hH, _hAffine, hOut⟩
  exact hOut

/-- Route-facing packet: the local BKM estimates are checked, and the remaining
target follows from the componentized analytic ingredients. -/
theorem BKMContinuation_reduced_to_analytic_components :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityPointwiseEnstrophyDerivativeClosed ∧
            BKMVorticityRawBalanceIntegrabilitySchwartzClosed ∧
              BKMVorticityScalarSchwartzTimePairingDerivativeClosed ∧
                BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed ∧
                  BKMVorticityRawBalanceFromStandardEquationClosed ∧
                    BKMVorticityTransportCancellationAlgebraClosed ∧
                      BKMVorticityTransportCancellationSchwartzClosed ∧
                        BKMVorticityDiffusionIntegrationByPartsSchwartzClosed ∧
                          BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed ∧
                            BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed ∧
                              BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed ∧
                                BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed ∧
                                  BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed ∧
                                    BKMVorticityEnstrophyBalanceAssemblyClosed ∧
                            BKMVorticityEnstrophyAprioriEstimateClosed ∧
                                BKMVorticityEnstrophyGradientGrowthClosed ∧
                                BKMVorticityEnstrophyLogSobolevGrowthClosed ∧
                                  BKMVorticityEnstrophyAffineLogGrowthClosed ∧
                                    BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed ∧
                                      BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed ∧
                                        BKMVorticityStretchingAffineLogIntegralBoundClosed ∧
                                          BKMLogSobolevAffineReductionClosed ∧
                                            BKMLogSobolevGrowthEstimateClosed ∧
                                              (BKMAnalyticComponentsClosed →
                                                ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) ∧
                                                (BKMAffineLogSobolevAnalyticComponentsClosed →
                                                  ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact
    ⟨BKMVorticityStretchingEstimateClosed_proved,
      BKMResidualCurlExpansionAlgebraClosed_proved,
      BKMStandardVorticityGrowthEstimateClosed_proved,
      BKMVorticityPointwiseEnstrophyDerivativeClosed_proved,
      BKMVorticityRawBalanceIntegrabilitySchwartzClosed_proved,
      BKMVorticityScalarSchwartzTimePairingDerivativeClosed_proved,
      BKMVorticityTwoProfileSchwartzTimePairingDerivativeClosed_proved,
      BKMVorticityRawBalanceFromStandardEquationClosed_proved,
      BKMVorticityTransportCancellationAlgebraClosed_proved,
      BKMVorticityTransportCancellationSchwartzClosed_proved,
      BKMVorticityDiffusionIntegrationByPartsSchwartzClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzEnstrophyIntegrableClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzRawBalanceIntegrabilityClosed_proved,
      BKMVorticityFiniteTimeWitnessSchwartzSliceAprioriClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocityVorticitySchwartzAprioriClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzAprioriClosed_proved,
      BKMVorticityEnstrophyBalanceAssemblyClosed_proved,
      BKMVorticityEnstrophyAprioriEstimateClosed_proved,
      BKMVorticityEnstrophyGradientGrowthClosed_proved,
      BKMVorticityEnstrophyLogSobolevGrowthClosed_proved,
      BKMVorticityEnstrophyAffineLogGrowthClosed_proved,
      BKMVorticityFiniteTimeWitnessAffineLogGrowthClosed_proved,
      BKMVorticityFiniteTimeWitnessVelocitySchwartzAffineLogGrowthClosed_proved,
      BKMVorticityStretchingAffineLogIntegralBoundClosed_proved,
      BKMLogSobolevAffineReductionClosed_proved,
      BKMLogSobolevGrowthEstimateClosed_proved,
      BKMAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons,
      BKMAffineLogSobolevAnalyticComponentsClosed.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
