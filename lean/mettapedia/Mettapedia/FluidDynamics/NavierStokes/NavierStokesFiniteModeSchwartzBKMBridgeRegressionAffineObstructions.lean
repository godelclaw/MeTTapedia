import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeRegressionZeroBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMAffinePressureObstructions

/-!
# Affine-Pressure BKM Bridge Obstruction Regressions

This module checks affine pressure mismatch, scalar-laplacian, and repeated
gradient obstruction regressions for two-mode Schwartz bridges.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem one_one_two_mode_affine_pressure_lapSum_pair_mismatch_obstruction_regression
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          ρ t •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure hbad

theorem one_one_two_mode_affine_pressure_zero_localized_amplitude_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        ρ t = 0 ∧
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_zeroLocalizedAmplitude_lapSum_pair_ne
      hν f g c π ρ q hclosure hbad

theorem one_one_two_mode_affine_pressure_no_scalar_lapSum_pair_fit_obstruction_regression
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t, ∀ r : ℝ, ∃ x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          r •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure hbad

theorem one_one_two_mode_affine_pressure_same_pressureGradient_pair_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
        ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne
      hν f g q hclosure hbad

theorem one_one_two_mode_inviscid_BKM_and_pos_viscosity_affine_pressure_BKM_data_obstruction_regression
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ((∃ t x,
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
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
        ∃ W : ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    oneOneTwoModeSchwartzVelocity_inviscidBKM_and_not_exists_posViscosity_BKMData_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
      hν f g q hfg hfDiv hgDiv hclosure hbad

theorem one_one_two_mode_affine_pressure_repeated_gradient_lapSum_pair_obstruction_regression
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y ∧
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  exact
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_pressureGradient_pair_eq_lapSum_pair_ne
      hν f g q hclosure hbad

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
