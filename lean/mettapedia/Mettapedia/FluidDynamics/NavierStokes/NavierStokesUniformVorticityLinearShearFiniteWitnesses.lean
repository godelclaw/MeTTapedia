import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearContinuation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroFiniteEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroWitness

/-!
# Linear-shear finite-energy and finite-time witness exactness

This module isolates the whole-space finite-energy and finite-time witness
inhabitedness facts for the affine linear-shear family.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Full-drift affine linear shear has finite whole-space kinetic energy exactly
in the zero-data case. -/
theorem finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
    {a b c : ℝ} :
    finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hE
    have ha : a = 0 := by
      by_contra ha
      exact (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity ha) hE
    subst ha
    have hconst :
        EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c =
          (0 : NSSpace) := by
      by_contra hconst
      exact
        (not_finiteInitialKineticEnergy_constantInitialVelocity
          (c := EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c) hconst)
          (by
            simpa [linearShearFullDriftInitialVelocity_zero_shear] using hE)
    rcases single_nsCoord1_add_single_nsCoord2_eq_zero_iff.mp hconst with ⟨hb, hc⟩
    exact ⟨rfl, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hzero :
        EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0 =
          (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord1, nsCoord2]
    simpa [linearShearFullDriftInitialVelocity_zero_shear, hzero] using
      finiteInitialKineticEnergy_zero

/-- Base linear shear has finite whole-space kinetic energy exactly in the
zero-shear case. -/
theorem finiteInitialKineticEnergy_linearShearInitialVelocity_iff
    {a : ℝ} :
    finiteInitialKineticEnergy (linearShearInitialVelocity a) ↔
      a = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
      (a := a) (b := 0) (c := 0))

/-- Vertical-drift affine linear shear has finite whole-space kinetic energy
exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity_iff
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
      (a := a) (b := 0) (c := b))

/-- Horizontal-drift affine linear shear has finite whole-space kinetic energy
exactly in the zero-data case. -/
theorem finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity_iff
    {a b : ℝ} :
    finiteInitialKineticEnergy (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
      (a := a) (b := b) (c := 0))

/-- On nonnegative slabs, the full-drift linear-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a b c : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearFullDriftInitialVelocity a b c) T) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hW
    rcases hW with ⟨W⟩
    exact
      (finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
        (a := a) (b := b) (c := c)).1
        (finiteInitialKineticEnergy_of_matchesInitialVelocity_of_boundedKineticEnergyUpTo
          W.initial_condition W.bounded_energy_on hT)
  · rintro ⟨rfl, rfl, rfl⟩
    have hzero :
        EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0 =
          (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord1, nsCoord2]
    simpa [linearShearFullDriftInitialVelocity_zero_shear, hzero] using
      (show Nonempty (ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T) from
        ⟨zeroFiniteTimeRegularityWitness ν T⟩)

/-- On nonnegative slabs, the base linear-shear witness type is inhabited
exactly in the zero-shear case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_linearShearInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearInitialVelocity a) T) ↔
      a = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (b := 0) (c := 0))

/-- On nonnegative slabs, the vertical-drift linear-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_linearShearVerticalDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearVerticalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (b := 0) (c := b))

/-- On nonnegative slabs, the horizontal-drift linear-shear witness type is
inhabited exactly in the zero-data case. -/
theorem nonempty_ExplicitFiniteTimeRegularityWitness_linearShearHorizontalDriftInitialVelocity_iff
    {ν T : ℝ} (hT : 0 ≤ T) {a b : ℝ} :
    Nonempty (ExplicitFiniteTimeRegularityWitness
        ν (linearShearHorizontalDriftInitialVelocity a b) T) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (nonempty_ExplicitFiniteTimeRegularityWitness_linearShearFullDriftInitialVelocity_iff
      (ν := ν) (T := T) hT (a := a) (b := b) (c := 0))

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
