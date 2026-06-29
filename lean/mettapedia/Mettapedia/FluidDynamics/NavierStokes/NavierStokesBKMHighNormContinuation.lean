import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMAnalyticReduction
import Mathlib.Analysis.ODE.Gronwall

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
