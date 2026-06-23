import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyContinuationBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzData
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Navier-Stokes finite-mode bounded-energy core

Two-mode Schwartz velocity, pressure, smoothness, divergence, Laplacian,
convection, and pointwise momentum identities used by the finite-mode bounded
energy construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Two spatial Schwartz profiles with scalar time amplitudes, viewed as a
finite-mode velocity field on `ℝ × ℝ^3`. -/
def twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) :
    NSVelocityField :=
  fun t x => a t • f x + b t • g x

/-- The initial velocity slice associated to two Schwartz profiles and fixed
scalar amplitudes. -/
def twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    NSInitialVelocity :=
  fun x => a0 • f x + b0 • g x

/-- The pressure class used by the existing two-mode energy bridge: an affine
gauge plus one localized Schwartz pressure profile. -/
def affineAddScalarSchwartzPressure
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) :
    NSPressureField :=
  (fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) +
    fun t : NSTime => fun x : NSSpace => ρ t * q x

/-- Smooth time amplitudes multiplying Schwartz spatial profiles give a smooth
two-mode concrete space-time velocity field. -/
theorem smoothSpaceTimeVelocity_twoModeSchwartzVelocity
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) := by
  have haTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => a tx.1) :=
    ha.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hbTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => b tx.1) :=
    hb.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hfSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => (f : NSSpace → NSSpace) tx.2) :=
    f.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  have hgSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => (g : NSSpace → NSSpace) tx.2) :=
    g.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  simpa [smoothSpaceTimeVelocity, spaceTimeVelocityMap, twoModeSchwartzVelocity] using
    (haTime.smul hfSpace).add (hbTime.smul hgSpace)

/-- Smooth affine pressure coefficients and a smooth scalar amplitude on a
Schwartz pressure profile give a smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_affineAddScalarSchwartzPressure
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q) := by
  simpa [affineAddScalarSchwartzPressure] using
    smoothSpaceTimePressure_affine_add_scalar_smul_schwartzPressure hc hπ hρ q

/-- Smooth scalar amplitudes have the expected derivative witnesses with
`deriv`; this removes separate derivative bookkeeping from finite-mode
constructors. -/
theorem hasDerivAt_deriv_of_contDiff {a : NSTime → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    ∀ t, HasDerivAt a (deriv a t) t := by
  intro t
  exact ((ha.differentiable (by simp)) t).hasDerivAt

/-- Two-mode Schwartz initial data have finite kinetic energy on `ℝ^3`. -/
theorem finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    finiteInitialKineticEnergy (twoModeSchwartzInitialVelocity a0 b0 f g) := by
  simpa [twoModeSchwartzInitialVelocity] using
    finiteInitialKineticEnergy_of_schwartzInitialVelocity
      ((a0 • f + b0 • g : NSSchwartzInitialVelocity))

/-- Two-mode Schwartz initial data are smooth on `ℝ^3`. -/
theorem smoothInitialVelocityData_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) :
    smoothInitialVelocityData (twoModeSchwartzInitialVelocity a0 b0 f g) := by
  simpa [twoModeSchwartzInitialVelocity] using
    smoothInitialVelocityData_of_schwartzInitialVelocity
      ((a0 • f + b0 • g : NSSchwartzInitialVelocity))

/-- The divergence of a two-mode Schwartz initial slice is the corresponding
scalar combination of the profile divergences. -/
theorem initialSpatialDivergence_twoModeSchwartzInitialVelocity
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity) (x : NSSpace) :
    initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x =
      a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
        b0 * initialSpatialDivergence (g : NSInitialVelocity) x := by
  calc
    initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x =
        initialSpatialDivergence
          (a0 • (f : NSInitialVelocity) + b0 • (g : NSInitialVelocity)) x := by
          rfl
    _ =
        initialSpatialDivergence (a0 • (f : NSInitialVelocity)) x +
          initialSpatialDivergence (b0 • (g : NSInitialVelocity)) x := by
          rw [initialSpatialDivergence_add
            (f.differentiableAt.const_smul a0)
            (g.differentiableAt.const_smul b0)]
    _ =
        a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
          initialSpatialDivergence (b0 • (g : NSInitialVelocity)) x := by
          rw [initialSpatialDivergence_const_smul]
    _ =
        a0 * initialSpatialDivergence (f : NSInitialVelocity) x +
          b0 * initialSpatialDivergence (g : NSInitialVelocity) x := by
          rw [initialSpatialDivergence_const_smul]

/-- Two-mode Schwartz initial data built from divergence-free profiles are
divergence-free themselves. -/
theorem initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
    (a0 b0 : ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    ∀ x, initialSpatialDivergence (twoModeSchwartzInitialVelocity a0 b0 f g) x = 0 := by
  intro x
  rw [initialSpatialDivergence_twoModeSchwartzInitialVelocity a0 b0 f g x, hfDiv x, hgDiv x]
  simp

/-- The two-mode space-time field matches its declared initial slice. -/
theorem MatchesInitialVelocity_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) :
    MatchesInitialVelocity
      (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (twoModeSchwartzVelocity a b f g) := by
  intro x
  rfl

/-- The time derivative of a smooth two-mode Schwartz velocity is the
two-mode velocity built from the scalar derivatives. -/
theorem timeVelocityDerivative_twoModeSchwartzVelocity_deriv
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x =
        deriv a t • f x + deriv b t • g x := by
  intro t x
  simpa [twoModeSchwartzVelocity] using
    timeVelocityDerivative_add_scalar_smul
      a (deriv a) b (deriv b) (f : NSSpace → NSSpace) (g : NSSpace → NSSpace)
      (hasDerivAt_deriv_of_contDiff ha)
      (hasDerivAt_deriv_of_contDiff hb) t x

/-- The spatial Laplacian of a two-mode Schwartz velocity expands modewise. -/
theorem spatialLaplacian_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialLaplacian (twoModeSchwartzVelocity a b f g) t x =
      a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  have hf2 :
      ContDiffAt ℝ 2
        (fun y : NSSpace => (timeIndependentVelocity (f : NSInitialVelocity)) t y) x := by
    exact (f.smooth'.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  have hg2 :
      ContDiffAt ℝ 2
        (fun y : NSSpace => (timeIndependentVelocity (g : NSInitialVelocity)) t y) x := by
    exact (g.smooth'.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  change
    spatialLaplacian
        ((a t) • timeIndependentVelocity (f : NSInitialVelocity) +
          (b t) • timeIndependentVelocity (g : NSInitialVelocity)) t x =
      a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x
  rw [spatialLaplacian_add (hf2.const_smul (a t)) (hg2.const_smul (b t))]
  rw [spatialLaplacian_const_smul (a t) hf2,
    spatialLaplacian_const_smul (b t) hg2]

/-- The nonlinear convection term of a two-mode Schwartz velocity expands into
the two self-interactions and the two mixed directional-derivative terms. -/
theorem spatialConvection_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialConvection (twoModeSchwartzVelocity a b f g) t x =
      (a t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
        (a t * b t) •
          spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
        (b t ^ (2 : ℕ)) •
          spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x := by
  have hf :
      DifferentiableAt ℝ
        (fun y : NSSpace => (timeIndependentVelocity (f : NSInitialVelocity)) t y) x := by
    simpa [timeIndependentVelocity] using f.differentiableAt
  have hg :
      DifferentiableAt ℝ
        (fun y : NSSpace => (timeIndependentVelocity (g : NSInitialVelocity)) t y) x := by
    simpa [timeIndependentVelocity] using g.differentiableAt
  simpa [twoModeSchwartzVelocity, timeIndependentVelocity] using
    spatialConvection_linearCombination (a t) (b t) hf hg

/-- Expanded residual closure implies the pointwise Navier-Stokes momentum
equation for arbitrary two-mode Schwartz amplitudes.  This is the nonzero-mode
version of the momentum slot: the nonlinear term is exposed as the full
self/mixed convection expansion rather than hidden inside the old `heq`
hypothesis. -/
theorem momentumEquation_twoModeSchwartzVelocity_of_explicitClosure
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
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
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (a t • spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            b t • spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv ha hb f g t x,
    spatialConvection_twoModeSchwartzVelocity a b f g t x,
    spatialLaplacian_twoModeSchwartzVelocity a b f g t x]
  exact hclosure t x

/-- Expanded residual closure implies the pointwise Navier-Stokes momentum
equation for arbitrary two-mode Schwartz amplitudes and arbitrary
time-indexed Schwartz pressure slices.  This is the pressure-slice analogue of
`momentumEquation_twoModeSchwartzVelocity_of_explicitClosure`; it exposes the
same derivative, convection, and Laplacian terms while replacing the
affine-plus-localized pressure ansatz by the actual pressure-slice field. -/
theorem momentumEquation_twoModeSchwartzVelocity_schwartzPressureSlice_of_explicitClosure
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : NSTime → 𝓢(NSSpace, ℝ))
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
    ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv ha hb f g t x,
    spatialConvection_twoModeSchwartzVelocity a b f g t x,
    spatialLaplacian_twoModeSchwartzVelocity a b f g t x]
  exact hclosure t x

/-- Constant nonzero amplitudes `a(t)=b(t)=1` are a direct specialization of
the expanded two-mode momentum theorem.  The closure hypothesis is the explicit
nonlinear self/mixed convection balance for the two spatial Schwartz profiles. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_of_explicitClosure
    (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    momentumEquation_twoModeSchwartzVelocity_of_explicitClosure
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const ν c π ρ f g q ?_
  intro t x
  simpa using hclosure t x

/-- In the inviscid zero-pressure specialization, constant nonzero amplitudes
`a(t)=b(t)=1` satisfy the pointwise momentum equation as soon as the explicit
two-profile convection expansion vanishes.  This isolates the exact remaining
profile-level closure burden for nonzero finite-energy Schwartz modes. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_inviscid_zeroPressure_of_convectionClosure
    (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (0 : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialPressureGradient_zero]
  simpa using hclosure t x

/-- Conversely, a constant-one two-mode Schwartz velocity with zero pressure
can satisfy the pointwise momentum equation only if the expanded convection
residual equals the viscous Laplacian residual.  This exposes the precise
extra condition that is absent from the inviscid zero-pressure branch. -/
theorem explicitClosure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_momentumEquation
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (hmom : ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x) :
    ∀ t x,
        spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  intro t x
  have h := hmom t x
  rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      contDiff_const contDiff_const f g t x,
    spatialConvection_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialLaplacian_twoModeSchwartzVelocity
      (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
    spatialPressureGradient_zero] at h
  simpa using h

/-- The inviscid zero-pressure one-one branch cannot be reused as a
positive-viscosity zero-pressure Navier--Stokes branch unless the summed
profile Laplacian vanishes everywhere.  A single nonzero Laplacian-sum point
contradicts the momentum equation. -/
theorem not_momentumEquation_oneOneTwoMode_zeroPressure_of_inviscidClosure_lapSum_ne_zero
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hlap : ∃ t x,
        spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x ≠
        (0 : NSSpace)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (0 : NSPressureField) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hlap with ⟨t, x, hlap_ne⟩
  have hresidual :=
    explicitClosure_oneOneTwoModeSchwartzVelocity_zeroPressure_of_momentumEquation
      ν f g hmom t x
  have hsmul :
      (ν : ℝ) •
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) =
        0 := by
    rw [← hresidual, hclosure t x]
  exact hlap_ne ((smul_eq_zero.mp hsmul).resolve_left hν.ne')

/-- Once the constant-one two-mode branch has inviscid convection closure,
the full positive-viscosity momentum equation is exactly the assertion that
the pressure gradient supplies the missing viscous Laplacian residual.  This
is the minimal pressure-repair condition left after the zero-pressure
obstruction. -/
theorem momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
    (ν : ℝ) (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x) ↔
      ∀ t x,
        spatialPressureGradient p t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
  constructor
  · intro hmom t x
    have h := hmom t x
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at h
    simpa [hclosure t x] using h
  · intro hpressure t x
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x]
    simpa [hclosure t x] using hpressure t x

/-- Pointwise mismatch with the viscous Laplacian residual blocks every
pressure-repaired positive-viscosity realization of the same inviscid
constant-one two-mode branch. -/
theorem not_momentumEquation_oneOneTwoMode_of_inviscidClosure_pressureGradient_lapSum_mismatch
    (ν : ℝ) (p : NSPressureField) (f g : NSSchwartzInitialVelocity)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x,
        spatialPressureGradient p t x ≠
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient p t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hbad with ⟨t, x, hbad⟩
  exact hbad
    ((momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
      ν p f g hclosure).1 hmom t x)

/-- A constant-one two-mode Schwartz velocity is genuinely nonzero whenever the
two spatial profiles do not cancel everywhere. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero
    (f g : NSSchwartzInitialVelocity)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0) :
    ∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace) := by
  rcases hfg with ⟨x, hx⟩
  refine ⟨0, x, ?_⟩
  simpa [twoModeSchwartzVelocity] using hx

/-- The zero-amplitude member of the two-mode Schwartz class is literally the
zero velocity field, independently of the chosen spatial Schwartz profiles. -/
theorem twoModeSchwartzVelocity_zero_zero
    (f g : NSSchwartzInitialVelocity) :
    twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g =
      (0 : NSVelocityField) := by
  funext t x
  simp [twoModeSchwartzVelocity]

/-- If the affine coefficient and localized Schwartz pressure amplitude both
vanish, the affine-plus-Schwartz pressure class reduces to a time-only pressure
gauge. -/
theorem affineAddScalarSchwartzPressure_zero_timeOnly
    (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) :
    affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
        (fun _ : NSTime => 0) q =
      fun t : NSTime => fun _ : NSSpace => π t := by
  funext t x
  simp [affineAddScalarSchwartzPressure]

/-- The spatial gradient of an affine-in-space pressure gauge
`p(t,x)=⟪c(t),x⟫+π(t)` is exactly the affine coefficient `c(t)`. -/
theorem spatialPressureGradient_affinePressure
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s) t x =
      c t := by
  unfold spatialPressureGradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    ((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const (π t)

/-- In the affine-plus-Schwartz pressure class, if the localized Schwartz
amplitude is zero, the spatial pressure gradient is exactly the spatial affine
coefficient.  The time-only scalar gauge and unused Schwartz profile do not
contribute. -/
theorem spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) t x =
      c t := by
  have hpress :
      affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q =
        fun s : NSTime => fun y : NSSpace => ⟪c s, y⟫ + π s := by
    funext s y
    simp [affineAddScalarSchwartzPressure]
  rw [hpress]
  exact spatialPressureGradient_affinePressure c π t x

/-- Any finite-time witness with zero velocity and pure spatial-affine pressure
has zero affine pressure coefficient throughout its certified time slab.  Thus a
nonzero spatial affine pressure gradient cannot be hidden as pressure gauge on a
zero-flow finite-time witness. -/
theorem ExplicitFiniteTimeRegularityWitness.zeroVelocity_spatialAffinePressure_implies_zeroAffineCoeffOn
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (W : ExplicitFiniteTimeRegularityWitness ν u0 T)
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hWvel : W.velocity = (0 : NSVelocityField))
    (hWpress :
      W.pressure = affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q) :
    ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  intro t ht0 htT
  have hmom := W.momentum_equation_on t (0 : NSSpace) ht0 htT
  have hlap : spatialLaplacian (0 : NSVelocityField) t (0 : NSSpace) = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t (0 : NSSpace)
  simpa [hWvel, hWpress, timeVelocityDerivative_zero, spatialConvection_zero,
    hlap,
    spatialPressureGradient_affineAddScalarSchwartzPressure_spatialAffine c π q t
      (0 : NSSpace)] using hmom

/-- The zero-amplitude two-mode Schwartz velocity satisfies the pointwise
Navier-Stokes momentum equation against any time-only pressure gauge represented
inside the affine-plus-Schwartz pressure class.  This closes the momentum
identity for a finite-energy Schwartz member of the construction without an
external `heq` hypothesis. -/
theorem momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
    (ν : ℝ) (π : NSTime → ℝ)
    (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x +
          spatialPressureGradient
            (affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
              (fun _ : NSTime => 0) q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 0) (fun _ : NSTime => 0) f g) t x := by
  intro t x
  simpa [twoModeSchwartzVelocity_zero_zero f g,
    affineAddScalarSchwartzPressure_zero_timeOnly π q] using
    momentumEquation_zeroVelocityField_timeOnlyPressure ν π t x
end NavierStokes
end FluidDynamics
end Mettapedia
