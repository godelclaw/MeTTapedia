import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeBoundedEnergyRegressionPart1

/-!
# Navier-Stokes Finite-Mode Bounded-Energy Regression

Regression checks for the positive bounded-energy two-mode Schwartz finite-mode
construction.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeBoundedEnergyRegression


def one_one_two_mode_schwartz_inviscid_zero_pressure_witness_regression
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
  exact
    ExplicitFiniteTimeRegularityWitness.of_oneOneTwoModeSchwartzVelocity_inviscidZeroPressure
      f g hfDiv hgDiv hclosure

theorem one_one_two_mode_schwartz_nonzero_inviscid_witness_regression
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
    oneOneTwoModeSchwartzVelocity_nonzero_inviscidWitness_of_convectionClosure
      f g hfg hfDiv hgDiv hclosure

theorem two_mode_schwartz_finite_time_witness_velocity_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q hu hp hinit hν haBound hbBound ha hb heq hdiv).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_smooth_coefficients_witness_velocity_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν
      haBound hbBound ha hb heq hdiv).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_smooth_coefficients_witness_pressure_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothCoefficients
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hinit hν
      haBound hbBound ha hb heq hdiv).pressure =
      affineAddScalarSchwartzPressure c π ρ q := by
  rfl

theorem two_mode_schwartz_smooth_divergence_free_witness_velocity_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_smoothDivergenceFree
      (ν := ν) (T := T) (u₀ := u₀)
      a a' b b' f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hinit hν
      haBound hbBound ha hb heq).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_canonical_initial_witness_velocity_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (ν := ν) (T := T)
      a b f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hν
      haBound hbBound heq).velocity =
      twoModeSchwartzVelocity a b f g := by
  rfl

theorem two_mode_schwartz_canonical_initial_witness_pressure_regression
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
    (ExplicitFiniteTimeRegularityWitness.of_twoModeSchwartzVelocity_affineAddScalarSchwartzPressure_canonicalInitial
      (ν := ν) (T := T)
      a b f g A B c π ρ q
      haSmooth hbSmooth hcSmooth hπSmooth hρSmooth hfDiv hgDiv hν
      haBound hbBound heq).pressure =
      affineAddScalarSchwartzPressure c π ρ q := by
  rfl

private theorem initialSpatialDivergence_zero_schwartz_regression
    (x : NSSpace) :
    initialSpatialDivergence (((0 : NSSchwartzInitialVelocity) : NSInitialVelocity)) x = 0 := by
  change initialSpatialDivergence (0 : NSInitialVelocity) x = 0
  exact initialSpatialDivergence_zero x

theorem two_mode_schwartz_zero_profile_global_output_regression
    (ν : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)) := by
  exact
    ExplicitConcreteNavierStokesGlobalOutput_twoModeSchwartzVelocity_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      contDiff_const contDiff_const
      (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
      0 0
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (0 : 𝓢(NSSpace, ℝ))
      contDiff_const contDiff_const contDiff_const
      (by intro t; simp)
      (by intro t; simp)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by
        intro t x
        simpa using
          momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
            ν (fun _ : NSTime => 0)
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (0 : 𝓢(NSSpace, ℝ)) t x)

theorem two_mode_schwartz_zero_profile_finite_energy_clause_regression
    (ν : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν
      (twoModeSchwartzInitialVelocity 0 0
        (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      contDiff_const contDiff_const
      (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
      0 0
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (0 : 𝓢(NSSpace, ℝ))
      contDiff_const contDiff_const contDiff_const
      (by intro t; simp)
      (by intro t; simp)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by
        intro t x
        simpa using
          momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
            ν (fun _ : NSTime => 0)
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (0 : 𝓢(NSSpace, ℝ)) t x)

theorem two_mode_schwartz_zero_profile_structured_clause_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := twoModeSchwartzInitialVelocity 0 0
           (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
         smooth_initial :=
           smoothInitialVelocityData_twoModeSchwartzInitialVelocity 0 0
             (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
         divergence_free_initial :=
           initialSpatialDivergence_twoModeSchwartzInitialVelocity_zero
             0 0
             (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
             (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
             (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
         finite_initial_energy :=
           finiteInitialKineticEnergy_twoModeSchwartzInitialVelocity 0 0
             (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity) } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_twoModeSchwartzInitialVelocity_of_momentumEquation
      (a := fun _ : NSTime => 0)
      (b := fun _ : NSTime => 0)
      contDiff_const contDiff_const
      (0 : NSSchwartzInitialVelocity) (0 : NSSchwartzInitialVelocity)
      0 0
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (fun _ : NSTime => 0)
      (0 : 𝓢(NSSpace, ℝ))
      hν
      contDiff_const contDiff_const contDiff_const
      (by intro t; simp)
      (by intro t; simp)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by intro x; exact initialSpatialDivergence_zero_schwartz_regression x)
      (by
        intro t x
        simpa using
          momentumEquation_zeroTwoModeSchwartzVelocity_affineTimeOnlyPressure
            ν (fun _ : NSTime => 0)
            (0 : NSSchwartzInitialVelocity)
            (0 : NSSchwartzInitialVelocity)
            (0 : 𝓢(NSSpace, ℝ)) t x)

end NavierStokesFiniteModeBoundedEnergyRegression
end NavierStokes
end FluidDynamics
end Mettapedia
