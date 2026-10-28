import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMBridgeRegressionSchwartzPressureSlices
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMZeroVelocityLocalizedPressure

/-!
# Zero-Velocity Affine-Pressure BKM Bridge Regressions

This module checks zero-velocity BKM data classification and affine-add-scalar
Schwartz-pressure balance regressions.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesFiniteModeSchwartzBKMBridgeRegression

theorem zero_velocity_BKM_data_nonzero_spatial_affine_pressure_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_exists_nonzeroAffineCoeffOn
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      ?_
  refine ⟨0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_spatial_affine_pressure_exact_classification_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure c π (fun _ : NSTime => 0) q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧ ∀ t, 0 ≤ t → t ≤ T → c t = 0 := by
  exact
    BKMData_zeroVelocity_spatialAffinePressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn
      c π q hc hπ

theorem zero_velocity_BKM_data_spatial_affine_pressure_zero_coeff_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_spatialAffinePressure_of_affineCoeff_zeroOn
      (ν := ν)
      (T := T)
      (fun _ : NSTime => 0)
      π q
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      hπ
      (by intro t _ht0 _htT; rfl)

theorem zero_velocity_BKM_data_spatial_affine_pressure_nonzero_initial_or_coeff_impossible_regression :
    ¬
      (∃ W :
        ExplicitFiniteTimeRegularityWitness 0
          (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_spatialAffinePressure_of_initialVelocity_ne_zero_or_exists_nonzeroAffineCoeffOn
      (ν := 0)
      (T := 0)
      (u0 := constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (contDiff_const :
        ContDiff ℝ ∞ (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      ?_
  refine Or.inr ?_
  refine ⟨0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    exact congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem spatial_pressure_gradient_scalar_schwartz_pressure_regression
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
      ρ t • spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  exact spatialPressureGradient_scalarSchwartzPressure ρ q t x

theorem spatial_pressure_gradient_affine_add_scalar_schwartz_pressure_regression
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
      c t + ρ t •
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  exact spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_exact_balance_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        ∀ t x, 0 ≤ t → t ≤ T →
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_pressureGradientBalanceOn
      c π ρ q hc hπ hρ

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_balanced_exists_regression
    {ν T : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π)
    (q : 𝓢(NSSpace, ℝ)) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      W.velocity = (0 : NSVelocityField) ∧
        W.pressure =
          affineAddScalarSchwartzPressure (fun _ : NSTime => 0) π
            (fun _ : NSTime => 0) q ∧
        ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
          vorticityEnvelopeOn W.velocity T Ω ∧
            integrableVorticityEnvelopeOn Ω T Bint := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_pressureGradientBalanceOn
      (ν := ν)
      (T := T)
      (fun _ : NSTime => 0)
      π
      (fun _ : NSTime => 0)
      q
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : NSSpace)))
      hπ
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (by intro t x _ht0 _htT; simp)

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_balance_failure_impossible_regression :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness 0 (0 : NSInitialVelocity) 0,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure =
            affineAddScalarSchwartzPressure
              (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
              (fun _ : NSTime => 0) (fun _ : NSTime => 0)
              (0 : 𝓢(NSSpace, ℝ)) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity 0 Ω ∧
              integrableVorticityEnvelopeOn Ω 0 Bint) := by
  refine
    not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_pressureGradientBalanceFailureOn
      (ν := 0)
      (T := 0)
      (u0 := (0 : NSInitialVelocity))
      (c := fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ))
      (π := fun _ : NSTime => 0)
      (ρ := fun _ : NSTime => 0)
      (q := (0 : 𝓢(NSSpace, ℝ)))
      (contDiff_const :
        ContDiff ℝ ∞ (fun _ : NSTime => EuclideanSpace.single nsCoord0 (1 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSTime => (0 : ℝ)))
      ?_
  refine Or.inr ?_
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro hzero
  have hcoordZero :
      (EuclideanSpace.single nsCoord0 (1 : ℝ) : NSSpace) nsCoord0 =
        (0 : NSSpace) nsCoord0 := by
    simpa [nsCoord0] using congrArg (fun v : NSSpace => v nsCoord0) hzero
  simp [nsCoord0] at hcoordZero

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonconstant_gradient_impossible_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hfail :
      u0 ≠ 0 ∨
        ∃ t, ∃ x, ∃ y, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0 ∧
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x ≠
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y) :
    ¬
      (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) := by
  exact
    not_exists_BKMData_zeroVelocity_affineAddScalarSchwartzPressure_of_initialVelocity_ne_zero_or_exists_nonconstant_schwartzPressureGradientOn
      c π ρ q hc hπ hρ hfail

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_constant_gradient_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_constantOn_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem schwartz_map_constant_gradient_zero_regression
    (q : 𝓢(NSSpace, ℝ))
    (hconst : ∀ x : NSSpace,
      gradient (fun z : NSSpace => q z) x =
        gradient (fun z : NSSpace => q z) (0 : NSSpace)) :
    ∀ x : NSSpace, gradient (fun z : NSSpace => q z) x = 0 := by
  exact schwartzMap_gradient_constant_eq_zero q hconst

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_zero_gradient_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 →
      ∀ x,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_schwartzPressureGradient_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_nonzero_amplitude_forces_affine_coeff_zero_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (hData :
      ∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) :
    ∀ t, 0 ≤ t → t ≤ T → ρ t ≠ 0 → c t = 0 := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_implies_affineCoeff_zero_of_nonzeroAmplitude
      c π ρ q hc hπ hρ hData

theorem zero_velocity_BKM_data_affine_add_scalar_schwartz_pressure_exact_collapsed_regression
    {ν T : ℝ} {u0 : NSInitialVelocity}
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ) :
    (∃ W : ExplicitFiniteTimeRegularityWitness ν u0 T,
        W.velocity = (0 : NSVelocityField) ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ↔
      u0 = 0 ∧
        (∀ t, 0 ≤ t → t ≤ T → c t = 0) ∧
        ((∃ t, 0 ≤ t ∧ t ≤ T ∧ ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  exact
    BKMData_zeroVelocity_affineAddScalarSchwartzPressure_iff_initialVelocity_zero_and_affineCoeff_zeroOn_and_schwartzPressureGradient_zero_if_nonzeroAmplitudeOn
      c π ρ q hc hπ hρ

end NavierStokesFiniteModeSchwartzBKMBridgeRegression
end NavierStokes
end FluidDynamics
end Mettapedia
