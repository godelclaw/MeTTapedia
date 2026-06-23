import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeCore

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: SchwartzPressure

Pressure-slice finite-time and BKM-premise witnesses, including canonical anti-profile zero-witness packaging.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The bounded two-mode divergence-free Schwartz ansatz also produces an
exact finite-time witness for arbitrary time-indexed Schwartz pressure slices,
once the pressure field is smooth and the pointwise momentum equation is
supplied.  This is the pressure-slice analogue of the affine-plus-localized
pressure witness above. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = (fun s : NSTime => fun y : NSSpace => q s y) := by
  simpa [twoModeSchwartzDivergenceFreeInitialVelocity, twoModeSchwartzInitialVelocity] using
    (show ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = (fun s : NSTime => fun y : NSSpace => q s y) from
      ⟨ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_schwartzPressureSlice
          (ν := ν) (T := T)
          (u₀ := twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
          a (deriv a) b (deriv b) f g A B q
          (by simpa [twoModeSchwartzVelocity] using
            smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g)
          hp
          (by simpa [twoModeSchwartzVelocity] using
            MatchesInitialVelocity_twoModeSchwartzVelocity a b f g)
          hν haBound hbBound
          (hasDerivAt_deriv_of_contDiff ha)
          (hasDerivAt_deriv_of_contDiff hb)
          (by
            intro t x
            simpa [twoModeSchwartzVelocity] using heq t x)
          (by
            intro t x
            simpa [twoModeSchwartzVelocity] using
              spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv t x),
        rfl, rfl⟩)

/-- For the same pressure-slice class, bounded scalar amplitudes provide the
BKM-envelope part internally through the finite-mode vorticity estimate.  Thus
the BKM premise is reduced to smooth pressure, bounded amplitudes,
profile-level divergence freedom, and the pointwise momentum equation. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
        ha hb f g A B q hp hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a b f g A B T haBound hbBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The pressure-slice BKM premise can be driven by an explicit finite-mode
residual closure instead of an opaque pointwise momentum-equation hypothesis.
This exposes the exact remaining closure obligation for the two-mode Schwartz
ansatz: scalar amplitude derivatives, the four self/mixed convection terms, the
pressure-slice gradient, and the two linear Laplacian terms. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (q : NSTime → 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (hp : smoothSpaceTimePressure (fun s : NSTime => fun y : NSSpace => q s y))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
      deriv a t • f x + deriv b t • g x +
            ((a t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
              (a t * b t) •
                spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
              (b t ^ (2 : ℕ)) •
                spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x) +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_schwartzPressureSlice
      ha hb f g A B q hp hν haBound hbBound hfDiv hgDiv
      (momentumEquation_twoModeSchwartzVelocity_schwartzPressureSlice_of_explicitClosure
        ha hb ν f g q hclosure)

/-- The anti-profile cancellation baseline reaches the pressure-slice BKM
premise through the expanded residual-closure route.  The resulting initial
datum is zero, but the theorem records that the explicit closure bridge accepts
the cancellation pair `f, -f` whenever `f` is divergence-free. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_oneOneAntiProfile_schwartzPressureSlice_zeroPressure
    {ν T : ℝ} (hν : 0 ≤ ν) (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hPremise :=
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := fun _ : NSTime => 1)
      (b := fun _ : NSTime => 1)
      (f := f)
      (g := -f)
      (A := 1)
      (B := 1)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := ν)
      (T := T)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      hp
      hν
      (by intro t; simp)
      (by intro t; simp)
      hfDiv
      hgDiv
      (by
        intro t x
        simpa using
          explicitClosure_oneOneAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
            ν f t x)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity 1 1 f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hPremise
  simpa using hPremise

/-- The anti-profile pressure-slice BKM baseline remains valid for any smooth
equal amplitude with a uniform scalar bound.  The datum and velocity still
cancel to zero; the theorem records that the expanded residual-closure route
does not depend on the artificial constant-one amplitude choice. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hPremise :=
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_explicitClosure_schwartzPressureSlice
      (a := a)
      (b := a)
      (f := f)
      (g := -f)
      (A := A)
      (B := A)
      (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
      (ν := ν)
      (T := T)
      ha
      ha
      hp
      hν
      haBound
      haBound
      hfDiv
      hgDiv
      (by
        intro t x
        simpa using
          explicitClosure_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
            ha ν f t x)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hPremise
  simpa using hPremise

/-- Sharpened audit form of the equal-amplitude anti-profile pressure-slice
BKM baseline: the witness produced by the finite-mode bridge is itself the
zero velocity with the zero pressure slice.  Thus this branch of the repaired
BKM premise is explicitly a zero-flow cancellation artifact. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hp :
      smoothSpaceTimePressure
        (fun s : NSTime => fun y : NSSpace =>
          (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  have hWitness :
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            ((twoModeSchwartzDivergenceFreeInitialVelocity
              (a 0) (a 0) f (-f) hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) := by
    exact
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation_schwartzPressureSlice
        (a := a)
        (b := a)
        (f := f)
        (g := -f)
        (A := A)
        (B := A)
        (q := fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ)))
        (ν := ν)
        (T := T)
        ha
        ha
        hp
        hν
        haBound
        haBound
        hfDiv
        hgDiv
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_schwartzPressureSlice_zeroPressure
          a ν f)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hWitness
  rcases hWitness with ⟨W, hWvel, hWpress⟩
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a a f (-f) A A T haBound haBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWzero, hWpress, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- Exact BKM-data audit for the equal-amplitude anti-profile branch: the
finite-time witness can be chosen with zero velocity, zero pressure, the zero
vorticity envelope, and zero integral budget.  Thus no nontrivial BKM content
is hidden in this cancellation baseline. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          (fun s : NSTime => fun y : NSSpace =>
            (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
        vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness
        ha A hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  refine ⟨W, hWzero, hWpress, ?_, integrableVorticityEnvelopeOn_zero T⟩
  simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Canonical-witness form of the equal-amplitude anti-profile audit.  The
finite-mode bridge does not merely produce some zero-flow witness: its output
is propositionally equal to the canonical zero finite-time witness, equipped
with the zero BKM envelope and zero integral budget. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_canonicalZeroWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W = zeroFiniteTimeRegularityWitness ν T ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            (fun s : NSTime => fun y : NSSpace =>
              (fun _ : NSTime => (0 : 𝓢(NSSpace, ℝ))) s y) ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_schwartzPressureSlice_zeroPressure_zeroWitness_zeroEnvelope
        ha A hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, hEnv, hInt⟩
  have hWcanon : W = zeroFiniteTimeRegularityWitness ν T := by
    have hvel : W.velocity = (zeroFiniteTimeRegularityWitness ν T).velocity := by
      simpa [zeroFiniteTimeRegularityWitness] using hWzero
    have hpress : W.pressure = (zeroFiniteTimeRegularityWitness ν T).pressure := by
      simpa [zeroFiniteTimeRegularityWitness] using hWpress
    cases W
    cases hvel
    cases hpress
    simp [zeroFiniteTimeRegularityWitness]
    constructor <;> rfl
  exact ⟨W, hWcanon, hWzero, hWpress, hEnv, hInt⟩

/-- Time-only pressure-gauge audit for the equal-amplitude anti-profile branch.
Allowing a nonzero time-dependent pressure gauge in the affine-plus-Schwartz
pressure class still produces only zero velocity, the stated gauge pressure,
the zero vorticity envelope, and zero integral budget. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
          integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  have hgDiv :
      ∀ x,
        initialSpatialDivergence (((-f : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
    intro x
    simpa [hfDiv x] using
      initialSpatialDivergence_const_smul (-1) (f : NSInitialVelocity) x
  have hWitness :
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            ((twoModeSchwartzDivergenceFreeInitialVelocity
              (a 0) (a 0) f (-f) hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q := by
    exact
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        (a := a)
        (b := a)
        (f := f)
        (g := -f)
        (A := A)
        (B := A)
        (c := fun _ : NSTime => 0)
        (π := π)
        (ρ := fun _ : NSTime => 0)
        (q := q)
        (ν := ν)
        (T := T)
        ha
        ha
        contDiff_const
        hπ
        contDiff_const
        hν
        haBound
        haBound
        hfDiv
        hgDiv
        (momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineTimeOnlyPressure
          a ν π f q)
  have hinit :
      ((twoModeSchwartzDivergenceFreeInitialVelocity (a 0) (a 0) f (-f) hfDiv hgDiv).1 :
          NSInitialVelocity) =
        0 := by
    funext x
    simp [twoModeSchwartzDivergenceFreeInitialVelocity]
  rw [hinit] at hWitness
  rcases hWitness with ⟨W, hWvel, hWpress⟩
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    calc
      W.velocity = twoModeSchwartzVelocity a a f (-f) := hWvel
      _ = (0 : NSVelocityField) := equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  refine ⟨W, hWzero, hWpress, ?_, integrableVorticityEnvelopeOn_zero T⟩
  simpa [hWzero] using (vorticityEnvelopeOn_zero T)

/-- Canonical gauge-witness form of the time-only pressure audit.  The
equal-amplitude anti-profile bridge with a time-only affine-plus-Schwartz
pressure gauge is propositionally the canonical zero finite-time witness after
adding that same smooth time-only pressure gauge. -/
theorem twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_canonicalGaugeWitness
    {a : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (A : ℝ)
    (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ} (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (f : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W = (zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ ∧
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q ∧
          vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
            integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_equalAmplitudeAntiProfile_affineTimeOnlyPressure_zeroWitness_zeroEnvelope
        ha A π hπ q hν haBound f hfDiv with
    ⟨W, hWzero, hWpress, hEnv, hInt⟩
  have hWcanon :
      W = (zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ := by
    have hvel :
        W.velocity =
          ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).velocity := by
      simpa [ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
        ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
        zeroFiniteTimeRegularityWitness] using hWzero
    have hpress :
        W.pressure =
          ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).pressure := by
      calc
        W.pressure =
            affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q := hWpress
        _ = ((zeroFiniteTimeRegularityWitness ν T).addTimeOnlyPressure π hπ).pressure := by
          funext t x
          simp [affineAddScalarSchwartzPressure,
            ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
            ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
            zeroFiniteTimeRegularityWitness]
    cases W
    cases hvel
    cases hpress
    simp [ExplicitFiniteTimeRegularityWitness.addTimeOnlyPressure,
      ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient,
      zeroFiniteTimeRegularityWitness]
    rfl
  exact ⟨W, hWcanon, hWzero, hWpress, hEnv, hInt⟩
end NavierStokes
end FluidDynamics
end Mettapedia
