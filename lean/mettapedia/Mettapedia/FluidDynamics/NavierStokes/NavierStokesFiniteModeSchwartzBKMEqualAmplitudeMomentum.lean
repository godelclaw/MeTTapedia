import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMZeroVelocityLocalizedPressure

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: EqualAmplitudeMomentum

Momentum-equation and finite-time witness classification for equal-amplitude anti-profile velocities.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- Arbitrary-pressure momentum-equation classification for the
equal-amplitude anti-profile branch.  Since the velocity is identically zero,
the full pointwise momentum equation holds exactly when the pressure has zero
spatial gradient everywhere. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_iff_spatialPressureGradient_zero
    (a : NSTime → ℝ) (ν : ℝ) (f : NSSchwartzInitialVelocity)
    (p : NSPressureField) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient p t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      ∀ t x, spatialPressureGradient p t x = 0 := by
  constructor
  · intro hME t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap] using hME t x
  · intro hgrad t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap, hgrad t x]

/-- Finite-time witness classification for the cancelled equal-amplitude
anti-profile branch with an arbitrary smooth pressure.  Once the actual
finite-time witness structure is required to use the cancelled two-mode
velocity and the given pressure, its built-in slabwise momentum equation is
equivalent to vanishing spatial pressure gradient on the certified slab. -/
theorem exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_iff_spatialPressureGradient_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField} (hp : smoothSpaceTimePressure p) :
    (∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p) ↔
      ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient p t x = 0 := by
  constructor
  · rintro ⟨W, hWvel, hWpress⟩ t x ht0 htT
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    simpa [hWvel, hWpress, hvel, timeVelocityDerivative_zero,
      spatialConvection_zero, hlap] using W.momentum_equation_on t x ht0 htT
  · intro hgrad
    let W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T :=
      { velocity := twoModeSchwartzVelocity a a f (-f)
        pressure := p
        smooth_velocity := by
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).smooth_velocity
        smooth_pressure := hp
        momentum_equation_on := by
          intro t x ht0 htT
          have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
            equalAmplitudeAntiProfileSchwartzVelocity_zero a f
          have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
            simpa [constantVelocityField] using
              spatialLaplacian_constantVelocityField (0 : NSSpace) t x
          simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap,
            hgrad t x ht0 htT]
        incompressible_on := by
          intro t x ht0 htT
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            spatialDivergence_zero t x
        initial_condition := by
          simpa [equalAmplitudeAntiProfileSchwartzInitialVelocity_zero (a 0) f,
            equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).initial_condition
        bounded_energy_on := by
          simpa [equalAmplitudeAntiProfileSchwartzVelocity_zero a f] using
            (zeroFiniteTimeRegularityWitness ν T).bounded_energy_on }
    exact ⟨W, rfl, rfl⟩

/-- Internal-pressure witness obstruction for the cancelled equal-amplitude
anti-profile branch.  If a finite-time witness itself uses the cancelled
two-mode velocity, then its own pressure field has zero spatial gradient on
the certified slab.  This closes the variant where the pressure is not fixed in
advance but is carried hidden inside the witness record. -/
theorem ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    ∀ t x, 0 ≤ t → t ≤ T → spatialPressureGradient W.pressure t x = 0 := by
  intro t x ht0 htT
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  simpa [hWvel, hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap]
    using W.momentum_equation_on t x ht0 htT

/-- Same-witness BKM envelope for the cancelled equal-amplitude anti-profile
branch.  If an actual finite-time witness uses the cancelled two-mode velocity,
then its vorticity envelope can be chosen to be identically zero with zero
integral budget.  Thus the BKM packaging adds no further analytic burden on
this branch once the witness velocity is fixed. -/
theorem ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_has_zero_vorticityEnvelope
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    (W :
      ExplicitFiniteTimeRegularityWitness
        ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T)
    (hWvel : W.velocity = twoModeSchwartzVelocity a a f (-f)) :
    vorticityEnvelopeOn W.velocity T (fun _ : NSTime => 0) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => 0) T 0 := by
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hWzero : W.velocity = (0 : NSVelocityField) := by
    simpa [hvel] using hWvel
  exact
    ⟨by simpa [hWzero] using vorticityEnvelopeOn_zero T,
      integrableVorticityEnvelopeOn_zero T⟩

/-- Internal-pressure no-go for the cancelled equal-amplitude anti-profile
branch.  There is no finite-time witness whose velocity is the cancelled
two-mode field and whose own stored pressure has a nonzero spatial-gradient
point inside the certified slab. -/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_of_exists_pressure_spatialPressureGradient_ne_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧
          ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient W.pressure t x ≠ 0 := by
  rintro ⟨W, hWvel, t, x, ht0, htT, hgrad_ne⟩
  exact hgrad_ne
    (ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_implies_spatialPressureGradient_pressure_zero_on
      a f W hWvel t x ht0 htT)

/-- Witness-level arbitrary-pressure no-go for the cancelled equal-amplitude
anti-profile branch.  A single nonzero pressure-gradient point inside the
certified slab rules out any finite-time witness whose velocity is the
cancelled two-mode field and whose pressure is the proposed arbitrary pressure.
-/
theorem not_exists_ExplicitFiniteTimeRegularityWitness_equalAmplitudeAntiProfileInitialVelocity_velocity_pressure_of_exists_spatialPressureGradient_ne_zero_on
    {ν T : ℝ} (a : NSTime → ℝ) (f : NSSchwartzInitialVelocity)
    {p : NSPressureField}
    (hbad :
      ∃ t, ∃ x, 0 ≤ t ∧ t ≤ T ∧ spatialPressureGradient p t x ≠ 0) :
    ¬ ∃ W :
        ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity (a 0) (a 0) f (-f)) T,
        W.velocity = twoModeSchwartzVelocity a a f (-f) ∧ W.pressure = p := by
  rintro ⟨W, hWvel, hWpress⟩
  rcases hbad with ⟨t, x, ht0, htT, hgrad_ne⟩
  have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
    equalAmplitudeAntiProfileSchwartzVelocity_zero a f
  have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
    simpa [constantVelocityField] using
      spatialLaplacian_constantVelocityField (0 : NSSpace) t x
  exact hgrad_ne
    (by
      simpa [hWvel, hWpress, hvel, timeVelocityDerivative_zero,
        spatialConvection_zero, hlap] using W.momentum_equation_on t x ht0 htT)

/-- Momentum-equation classification for the equal-amplitude anti-profile
branch with the full affine-plus-localized Schwartz pressure class.  Since the
velocity is identically zero, the full pointwise momentum equation can hold
only in the same collapsed pressure cases as the zero-flow BKM classification:
the affine spatial coefficient is zero for every time, and any nonzero
localized amplitude forces the fixed Schwartz pressure gradient to vanish
everywhere. -/
theorem momentumEquation_equalAmplitudeAntiProfileSchwartzVelocity_affineAddScalarSchwartzPressure_iff_affineCoeff_zero_and_schwartzPressureGradient_zero_if_nonzeroAmplitude
    (a : NSTime → ℝ) (ν : ℝ) (c : NSTime → NSSpace) (π ρ : NSTime → ℝ)
    (f : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ)) :
    (∀ t x,
        timeVelocityDerivative (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialConvection (twoModeSchwartzVelocity a a f (-f)) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian (twoModeSchwartzVelocity a a f (-f)) t x) ↔
      (∀ t, c t = 0) ∧
        ((∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0) := by
  constructor
  · intro hME
    have hbalance :
        ∀ t x,
          c t + ρ t •
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x = 0 := by
      intro t x
      have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
        equalAmplitudeAntiProfileSchwartzVelocity_zero a f
      have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
        simpa [constantVelocityField] using
          spatialLaplacian_constantVelocityField (0 : NSSpace) t x
      simpa [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap,
        spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x]
        using hME t x
    have hgradZeroOfNonzero :
        (∃ t, ρ t ≠ 0) →
          ∀ s x,
            spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) s x = 0 := by
      rintro ⟨t0, hρne⟩ s x
      let g0 :=
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t0
          (0 : NSSpace)
      have hconstGradient :
          ∀ x : NSSpace,
            gradient (fun y : NSSpace => q y) x =
              gradient (fun y : NSSpace => q y) (0 : NSSpace) := by
        intro x
        let gx :=
          spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t0 x
        have hx : c t0 + ρ t0 • gx = 0 := hbalance t0 x
        have h0 : c t0 + ρ t0 • g0 = 0 := hbalance t0 (0 : NSSpace)
        have hsmul : ρ t0 • (gx - g0) = 0 := by
          calc
            ρ t0 • (gx - g0) = (c t0 + ρ t0 • gx) - (c t0 + ρ t0 • g0) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            _ = 0 := by
              rw [hx, h0]
              simp
        rcases smul_eq_zero.mp hsmul with hρzero | hdiff
        · exact False.elim (hρne hρzero)
        · simpa [gx, g0, spatialPressureGradient] using sub_eq_zero.mp hdiff
      have hzero := schwartzMap_gradient_constant_eq_zero q hconstGradient
      simpa [spatialPressureGradient] using hzero x
    refine ⟨?_, hgradZeroOfNonzero⟩
    intro t
    by_cases hρzero : ρ t = 0
    · have hbal0 := hbalance t (0 : NSSpace)
      simpa [hρzero] using hbal0
    · have hgradZero := hgradZeroOfNonzero ⟨t, hρzero⟩ t (0 : NSSpace)
      have hbal0 := hbalance t (0 : NSSpace)
      simpa [hgradZero] using hbal0
  · rintro ⟨hcZero, hgradZeroOfNonzero⟩ t x
    have hvel : twoModeSchwartzVelocity a a f (-f) = (0 : NSVelocityField) :=
      equalAmplitudeAntiProfileSchwartzVelocity_zero a f
    have hlap : spatialLaplacian (0 : NSVelocityField) t x = 0 := by
      simpa [constantVelocityField] using
        spatialLaplacian_constantVelocityField (0 : NSSpace) t x
    have hpress :
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x = 0 := by
      rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x]
      by_cases hρzero : ρ t = 0
      · simp [hcZero t, hρzero]
      · have hgradZero := hgradZeroOfNonzero ⟨t, hρzero⟩ t x
        simp [hcZero t, hgradZero]
    simp [hvel, timeVelocityDerivative_zero, spatialConvection_zero, hlap, hpress]
end NavierStokes
end FluidDynamics
end Mettapedia
