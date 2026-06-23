import Mathlib.Analysis.Calculus.MeanValue
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMUniformBridges
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeVorticity
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzDivergenceFreeBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionZero
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionTimeIndependent
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionPressureGauge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesWitnessConstructionBoxed

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: BridgeCore

Core finite-time witness and BKM-premise packaging for bounded two-mode Schwartz data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
  simpa [twoModeSchwartzDivergenceFreeInitialVelocity, twoModeSchwartzInitialVelocity] using
    (show ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T,
        W.velocity = twoModeSchwartzVelocity a b f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q from
      ⟨ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
          (ν := ν) (T := T)
          a b f g A B c π ρ q
          ha hb hc hπ hρ hfDiv hgDiv hν haBound hbBound heq,
        rfl, rfl⟩)

/-- With a slabwise uniform vorticity bound in hand, the same exact two-mode
divergence-free Schwartz witness already inhabits the repaired BKM continuation
premise. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation_and_uniformVorticityBound
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T K : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hω : uniformVorticityBoundUpTo (twoModeSchwartzVelocity a b f g) T K) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      uniformVorticityBoundUpTo_implies_BKMEnvelope
        (u := twoModeSchwartzVelocity a b f g) (T := T) (B := K) hω with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The bounded two-mode divergence-free Schwartz ansatz already carries its
own BKM envelope once the scalar amplitudes are uniformly bounded, so the BKM
premise does not need an extra vorticity hypothesis on top of the momentum and
boundedness inputs. -/
theorem
    twoModeSchwartzDivergenceFreeInitialVelocity_exhibits_BKMContinuationPremise_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    {ν T : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ∃ W :
        ExplicitFiniteTimeRegularityWitness ν
          ((twoModeSchwartzDivergenceFreeInitialVelocity
            (a 0) (b 0) f g hfDiv hgDiv).1 : NSInitialVelocity) T,
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  rcases
      twoModeSchwartzDivergenceFreeInitialVelocity_finiteTimeWitness_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ hν haBound hbBound hfDiv hgDiv heq with
    ⟨W, hWvel, _hWpress⟩
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        a b f g A B T haBound hbBound with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- The constant-one two-profile inviscid zero-pressure branch leaves the
cancelled anti-profile cell: if the two Schwartz profiles do not cancel
pointwise everywhere and their explicit convection closure vanishes, then the
branch is genuinely nonzero and its finite-time witness already carries a BKM
envelope. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  refine
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg, ?_⟩
  let W :=
    ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
      f g hfDiv hgDiv hclosure (T := T)
  have hWvel :
      W.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
    rfl
  have hWpressure : W.pressure = (0 : NSPressureField) := by
    have hWpressureAffine :
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) := by
      rfl
    have hAffineZero :
        affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
          (0 : NSPressureField) := by
      funext t x
      simp [affineAddScalarSchwartzPressure]
    exact hWpressureAffine.trans hAffineZero
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp) (by intro t; simp) with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWvel, hWpressure, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv

/-- Positive-viscosity version of the non-cancelling constant-one branch with
the exact compensating pressure-gradient hypothesis.  The previous zero
pressure theorem is blocked by the viscous Laplacian residual; this theorem
records the minimal pressure repair that makes the same nonzero finite-mode
velocity and its internally supplied BKM envelope available again. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_posViscosity_BKMPremise_of_inviscidClosure_pressureGradient
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hpressure : ∀ t x,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x)) :
    (∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness ν
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  refine
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg, ?_⟩
  have hmom :
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
    exact
      (momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
        ν (affineAddScalarSchwartzPressure c π ρ q) f g hclosure).2 hpressure
  let W :=
    ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (a := fun _ : NSTime => 1)
      (b := fun _ : NSTime => 1)
      (f := f)
      (g := g)
      (A := 1)
      (B := 1)
      (c := c)
      (π := π)
      (ρ := ρ)
      (q := q)
      (ν := ν)
      (T := T)
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (1 : ℝ)))
      hc
      hπ
      hρ
      hfDiv
      hgDiv
      hν.le
      (by intro t; simp)
      (by intro t; simp)
      hmom
  have hWvel :
      W.velocity =
        twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g := by
    rfl
  have hWpressure : W.pressure = affineAddScalarSchwartzPressure c π ρ q := by
    rfl
  rcases
      twoModeSchwartzVelocity_exhibits_BKMEnvelope_of_abs_le
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g 1 1 T
        (by intro t; simp) (by intro t; simp) with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨W, hWvel, hWpressure, Ω, Bint, ?_, hInt⟩
  simpa [hWvel] using hEnv
end NavierStokes
end FluidDynamics
end Mettapedia
