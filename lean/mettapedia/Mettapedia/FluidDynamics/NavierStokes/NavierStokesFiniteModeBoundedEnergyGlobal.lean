import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergyCore

/-!
# Navier-Stokes finite-mode bounded-energy global packages

Divergence, bounded-energy, global-output, and finite-time witness packaging
for two-mode Schwartz finite-mode velocities.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The divergence of a two-mode Schwartz velocity is the scalar-amplitude
combination of the initial divergences of its spatial profiles. -/
theorem spatialDivergence_twoModeSchwartzVelocity
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (t : NSTime) (x : NSSpace) :
    spatialDivergence (twoModeSchwartzVelocity a b f g) t x =
      a t * initialSpatialDivergence (f : NSInitialVelocity) x +
        b t * initialSpatialDivergence (g : NSInitialVelocity) x := by
  have hf :
      spatialDivergence (fun s : NSTime => fun y : NSSpace => a s • f y) t x =
        a t * initialSpatialDivergence (f : NSInitialVelocity) x := by
    simpa [spatialDivergence, spatialFDeriv, timeIndependentVelocity,
      initialSpatialDivergence] using
      spatialDivergence_const_smul
        (a t) (timeIndependentVelocity (f : NSInitialVelocity)) t x
  have hg :
      spatialDivergence (fun s : NSTime => fun y : NSSpace => b s • g y) t x =
        b t * initialSpatialDivergence (g : NSInitialVelocity) x := by
    simpa [spatialDivergence, spatialFDeriv, timeIndependentVelocity,
      initialSpatialDivergence] using
      spatialDivergence_const_smul
        (b t) (timeIndependentVelocity (g : NSInitialVelocity)) t x
  change
    spatialDivergence
      ((fun s : NSTime => fun y : NSSpace => a s • f y) +
        fun s : NSTime => fun y : NSSpace => b s • g y) t x =
      a t * initialSpatialDivergence (f : NSInitialVelocity) x +
        b t * initialSpatialDivergence (g : NSInitialVelocity) x
  rw [spatialDivergence_add]
  · rw [hf, hg]
  · exact f.differentiableAt.const_smul (a t)
  · exact g.differentiableAt.const_smul (b t)

/-- Two-mode Schwartz velocities built from divergence-free spatial profiles
are incompressible for all times. -/
theorem spatialDivergence_twoModeSchwartzVelocity_zero
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    ∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0 := by
  intro t x
  rw [spatialDivergence_twoModeSchwartzVelocity a b f g t x, hfDiv x, hgDiv x]
  simp

/-- Uniformly bounded scalar amplitudes give global bounded kinetic energy for
the two-mode Schwartz finite-mode velocity. -/
theorem boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergy (twoModeSchwartzVelocity a b f g) := by
  simpa [twoModeSchwartzVelocity] using
    boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
      a b f g A B haBound hbBound

/-- The same two-mode Schwartz finite-mode velocity has bounded kinetic energy
on every finite time slab. -/
theorem boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T :=
  boundedKineticEnergy_implies_boundedKineticEnergyUpTo
    (boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
      a b f g A B haBound hbBound)

/-- A compact positive package for bounded-energy finite-mode exploration:
the initial slice is finite-energy, the space-time field matches it, and the
velocity has slab-bounded kinetic energy. -/
theorem twoModeSchwartzVelocity_finiteInitial_matches_boundedEnergyUpTo_of_abs_le
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- The same positive finite-mode package, now also discharging space-time
smoothness from smooth scalar amplitudes. -/
theorem twoModeSchwartzVelocity_finiteInitial_smooth_matches_boundedEnergyUpTo_of_abs_le
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- The positive finite-mode package with both smoothness and
incompressibility discharged from profile-level divergence freeness. -/
theorem twoModeSchwartzVelocity_finiteInitial_smooth_matches_divergenceFree_boundedEnergyUpTo_of_abs_le
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B T : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0) :
    finiteInitialKineticEnergy
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) ∧
      smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g) ∧
      MatchesInitialVelocity
        (twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
        (twoModeSchwartzVelocity a b f g) ∧
      (∀ t x, spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) ∧
      boundedKineticEnergyUpTo (twoModeSchwartzVelocity a b f g) T := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv
  · exact
      boundedKineticEnergyUpTo_twoModeSchwartzVelocity_of_abs_le
        a b f g A B T haBound hbBound

/-- A bounded two-mode Schwartz ansatz satisfying the full pointwise
Navier--Stokes equation gives a genuine global explicit output on `ℝ^3`. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitConcreteNavierStokesGlobalOutput
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) := by
  refine ⟨twoModeSchwartzVelocity a b f g, affineAddScalarSchwartzPressure c π ρ q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_twoModeSchwartzVelocity ha hb f g
  · exact smoothSpaceTimePressure_affineAddScalarSchwartzPressure hc hπ hρ q
  · exact heq
  · exact spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv
  · exact MatchesInitialVelocity_twoModeSchwartzVelocity a b f g
  · exact
      boundedKineticEnergy_twoModeSchwartzVelocity_of_abs_le
        a b f g A B haBound hbBound

/-- The same bounded two-mode Schwartz ansatz therefore satisfies the repaired
explicit finite-energy whole-space clause. -/
theorem
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

/-- On a positive-viscosity datum, the same bounded two-mode Schwartz ansatz
also inhabits the repaired structured fully concrete clause. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
    {a b : NSTime → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν : ℝ}
    (hν : 0 < ν)
    (hc : ContDiff ℝ ∞ c)
    (hπ : ContDiff ℝ ∞ π)
    (hρ : ContDiff ℝ ∞ ρ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := twoModeSchwartzInitialVelocity (a 0) (b 0) f g
         smooth_initial :=
           smoothInitialVelocityData_twoModeSchwartzInitialVelocity (a 0) (b 0) f g
         divergence_free_initial :=
           initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
             (a 0) (b 0) f g hfDiv hgDiv
         finite_initial_energy :=
           finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_implies_finiteEnergyConcreteNavierStokesGlobalRegularityClause_of_finiteInitialKineticEnergy
      hν
      (smoothInitialVelocityData_twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
        (a 0) (b 0) f g hfDiv hgDiv)
      (finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
      (ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
        ha hb f g A B c π ρ q hc hπ hρ haBound hbBound hfDiv hgDiv heq)

/-- Finite-time witness constructor for the two-mode Schwartz finite-mode
velocity and affine-plus-Schwartz pressure class.  The bounded-energy field is
supplied by the proved two-profile energy bridge; the momentum, smoothness and
incompressibility hypotheses remain explicit. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (hu : smoothSpaceTimeVelocity (twoModeSchwartzVelocity a b f g))
    (hp : smoothSpaceTimePressure (affineAddScalarSchwartzPressure c π ρ q))
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_add_scalar_smul_schwartz_of_abs_le_of_spatialDivergence_zero_affine_add_scalarSchwartzPressure
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    (by simpa [twoModeSchwartzVelocity] using hu)
    (by simpa [affineAddScalarSchwartzPressure] using hp)
    (by simpa [twoModeSchwartzVelocity] using hinit)
    hν haBound hbBound ha hb
    (by
      intro t x
      simpa [twoModeSchwartzVelocity, affineAddScalarSchwartzPressure] using heq t x)
    (by
      intro t x
      simpa [twoModeSchwartzVelocity] using hdiv t x)

/-- Finite-time witness constructor for the same two-mode Schwartz class that
derives velocity and pressure smoothness from smooth coefficient curves.  The
remaining analytic obligations are the pointwise momentum equation,
incompressibility, coefficient bounds and initial matching. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x)
    (hdiv :
      ∀ t x,
        spatialDivergence (twoModeSchwartzVelocity a b f g) t x = 0) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    (smoothSpaceTimeVelocity_twoModeSchwartzVelocity haSmooth hbSmooth f g)
    (smoothSpaceTimePressure_affineAddScalarSchwartzPressure
      hcSmooth hπSmooth hρSmooth q)
    hinit hν haBound hbBound ha hb heq hdiv

/-- Finite-time witness constructor for the two-mode Schwartz class that
derives both smoothness and incompressibility from smooth coefficient curves
and divergence-free Schwartz spatial profiles. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
    (a a' b b' : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    {u₀ : NSInitialVelocity}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hinit : MatchesInitialVelocity u₀ (twoModeSchwartzVelocity a b f g))
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteTimeRegularityWitness ν u₀ T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
    (ν := ν) (T := T) (u₀ := u₀)
    a a' b b' f g A B c π ρ q
    haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν haBound hbBound ha hb heq
    (spatialDivergence_twoModeSchwartzVelocity_zero a b f g hfDiv hgDiv)

/-- Canonical-initial finite-time witness constructor for the smooth
divergence-free two-mode Schwartz class.  The scalar derivative witnesses and
initial matching proof are derived internally from smoothness and the
definition of the initial slice. -/
def ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
    (a b : NSTime → ℝ) (f g : NSSchwartzInitialVelocity) (A B : ℝ)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) {ν T : ℝ}
    (haSmooth : ContDiff ℝ ∞ a)
    (hbSmooth : ContDiff ℝ ∞ b)
    (hcSmooth : ContDiff ℝ ∞ c)
    (hπSmooth : ContDiff ℝ ∞ π)
    (hρSmooth : ContDiff ℝ ∞ ρ)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hν : 0 ≤ ν)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B)
    (heq : ∀ t x,
      timeVelocityDerivative (twoModeSchwartzVelocity a b f g) t x +
          spatialConvection (twoModeSchwartzVelocity a b f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a b f g) t x) :
    ExplicitFiniteTimeRegularityWitness ν
      (twoModeSchwartzInitialVelocity (a 0) (b 0) f g) T :=
  ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
    (ν := ν) (T := T)
    (u₀ := twoModeSchwartzInitialVelocity (a 0) (b 0) f g)
    a (deriv a) b (deriv b) f g A B c π ρ q
    haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv
    (MatchesInitialVelocity_twoModeSchwartzVelocity a b f g)
    hν haBound hbBound
    (hasDerivAt_deriv_of_contDiff haSmooth)
    (hasDerivAt_deriv_of_contDiff hbSmooth)
    heq

/-- A finite-time regularity witness for the inviscid zero-pressure
constant-amplitude two-mode Schwartz construction.  All smoothness, initial
matching, bounded-energy and incompressibility obligations are discharged by
the finite-mode infrastructure; the only remaining analytic input is the
explicit two-profile convection closure. -/
def ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
    (f g : NSSchwartzInitialVelocity) {T : ℝ}
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0) :
    ExplicitFiniteTimeRegularityWitness 0
      (twoModeSchwartzInitialVelocity 1 1 f g) T := by
  refine
    ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
      (f := f) (g := g) (A := 1) (B := 1)
      (c := fun _ : NSTime => 0) (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0) (q := (0 : 𝓢(NSSpace, ℝ)))
      (ν := 0) (T := T)
      contDiff_const contDiff_const contDiff_const contDiff_const contDiff_const
      hfDiv hgDiv (by norm_num) ?_ ?_ ?_
  · intro t
    simp
  · intro t
    simp
  · intro t x
    have hp :
        affineAddScalarSchwartzPressure (fun _ : NSTime => 0) (fun _ : NSTime => 0)
            (fun _ : NSTime => 0) (0 : 𝓢(NSSpace, ℝ)) =
          (0 : NSPressureField) := by
      funext s y
      simp [affineAddScalarSchwartzPressure]
    simpa [hp] using
      momentumEquation_oneOneTwoModeSchwartzVelocity_inviscid_zeroPressure_of_convectionClosure
        f g hclosure t x

/-- The inviscid zero-pressure constant-amplitude package is genuinely
nonzero whenever the two spatial Schwartz profiles do not cancel everywhere. -/
theorem oneOneTwoModeSchwartzVelocity_nonzero_inviscidWitness_of_convectionClosure
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
      Nonempty
        (ExplicitFiniteTimeRegularityWitness 0
          (twoModeSchwartzInitialVelocity 1 1 f g) T) := by
  exact
    ⟨oneOneTwoModeSchwartzVelocity_nonzero_of_exists_profile_sum_ne_zero f g hfg,
      ⟨ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
        f g hfDiv hgDiv hclosure⟩⟩
end NavierStokes
end FluidDynamics
end Mettapedia
