import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBounds
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityEnergyObstructions

/-!
# Uniform-Vorticity Constant-Field Candidates

This module contains the constant-field candidate, gap, and exactness
lemmas for the concrete uniform-vorticity continuation surface.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Any explicit slab candidate with a uniform-vorticity bound and missing only
the bounded-energy slot remains such a candidate after adding a smooth
slice-wise zero-spatial-gradient pressure gauge. The velocity, vorticity
control, initial matching, and bounded-energy obstruction are unchanged. -/
theorem exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (h :
      ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
        smoothSpaceTimeVelocity u ∧
        smoothSpaceTimePressure p ∧
        (∀ t x, 0 ≤ t → t ≤ T →
          timeVelocityDerivative u t x + spatialConvection u t x +
              spatialPressureGradient p t x =
            ν • spatialLaplacian u t x) ∧
        (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
        MatchesInitialVelocity u₀ u ∧
        uniformVorticityBoundUpTo u T B ∧
        ¬ boundedKineticEnergyUpTo u T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x +
            spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity u₀ u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  rcases h with ⟨u, p, B, hu, hp, hmom, hdiv, hinit, hω, hE⟩
  refine ⟨u, p + q, B, hu, smoothSpaceTimePressure_add hp hq, ?_, hdiv, hinit, hω, hE⟩
  intro t x ht0 htT
  have hp' : DifferentiableAt ℝ (fun y : NSSpace => p t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hp t x
  have hq' : DifferentiableAt ℝ (fun y : NSSpace => q t y) x :=
    smoothSpaceTimePressure_differentiableAt_spatialSlice hq t x
  exact
    momentumEquation_addPressureOfZeroSpatialGradient
      (u := u) (p := p) (q := q) hp' hq' (hq_zero t x) (hmom t x ht0 htT)

/-- A nonzero constant velocity field is an exact smooth incompressible
Navier--Stokes candidate on every nonnegative slab, with the explicit uniform
zero vorticity bound; the only missing finite-time witness slot is bounded
kinetic energy on `ℝ^3`. -/
theorem constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  refine ⟨constantVelocityField c, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact smoothSpaceTimeVelocity_constantVelocityField c
  · simpa using smoothSpaceTimePressure_const (0 : ℝ)
  · intro t x ht0 htT
    simp [timeVelocityDerivative_constantVelocityField,
      spatialConvection_constantVelocityField, spatialPressureGradient_zero,
      spatialLaplacian_constantVelocityField]
  · intro t x ht0 htT
    simpa using spatialDivergence_constantVelocityField c t x
  · exact matchesInitialVelocity_constantVelocityField c
  · exact uniformVorticityBoundUpTo_constantVelocityField c T
  · exact not_boundedKineticEnergyUpTo_constantVelocityField hc hT

/-- The same nonzero constant-field slab candidate remains valid after adding
any smooth slice-wise zero-spatial-gradient pressure gauge. The honest
obstruction on `ℝ^3` is still only the bounded-energy slot. -/
theorem constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T := by
  exact
    exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
      (u₀ := constantInitialVelocity c)
      (constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
        (ν := ν) (T := T) (c := c) hc hT)
      q hq hq_zero

/-- Constant initial data expose the same honest gap on the concrete
uniform-vorticity surface as the shear families: there is an exact smooth
incompressible slab candidate with uniform zero vorticity, but the finite-time
witness type is empty because bounded kinetic energy fails on `ℝ^3`. -/
theorem constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy
      (ν := ν) (T := T) hc hT
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- The same honest constant-data gap persists after adding any smooth
zero-spatial-gradient pressure gauge to the explicit constant-field slab
candidate. -/
theorem constantInitialVelocity_exhibits_uniformCandidate_without_finiteTimeWitness_addPressureOfZeroSpatialGradient
    {ν T : ℝ} {c : NSSpace}
    (hc : c ≠ 0)
    (hT : 0 ≤ T)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    (∃ u : NSVelocityField, ∃ p : NSPressureField, ∃ B : ℝ,
      smoothSpaceTimeVelocity u ∧
      smoothSpaceTimePressure p ∧
      (∀ t x, 0 ≤ t → t ≤ T →
        timeVelocityDerivative u t x + spatialConvection u t x + spatialPressureGradient p t x =
          ν • spatialLaplacian u t x) ∧
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) ∧
      MatchesInitialVelocity (constantInitialVelocity c) u ∧
      uniformVorticityBoundUpTo u T B ∧
      ¬ boundedKineticEnergyUpTo u T) ∧
      ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν (constantInitialVelocity c) T) := by
  refine ⟨?_, ?_⟩
  · exact
      constantVelocityField_exhibits_uniformCandidate_except_boundedEnergy_addPressureOfZeroSpatialGradient
        (ν := ν) (T := T) hc hT q hq hq_zero
  · exact not_nonempty_ExplicitFiniteTimeRegularityWitness_constantInitialVelocity
      (ν := ν) (T := T) hc hT

/-- If the concrete finite-time witness type is empty on a slab, then the
uniform-vorticity continuation clause is true there only vacuously. -/
theorem ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
    {ν T : ℝ} {u₀ : NSInitialVelocity}
    (hEmpty : ¬ Nonempty (ExplicitFiniteTimeRegularityWitness ν u₀ T)) :
    ExplicitUniformVorticityContinuationClause ν u₀ T := by
  intro hν hsmooth hdiv W hω
  exfalso
  exact hEmpty ⟨W⟩

/-- The fully explicit global-output surface is likewise impossible for nonzero
constant initial data, independent of what pressure field is used later. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (constantInitialVelocity c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_constantInitialVelocity
      (u := u) hc hinit hbd

/-- The explicit whole-space output surface is exact on constant initial data:
it is inhabited precisely in the zero-data case. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
    {ν : ℝ} {c : NSSpace} :
    ExplicitConcreteNavierStokesGlobalOutput ν (constantInitialVelocity c) ↔ c = 0 := by
  constructor
  · intro hOut
    by_contra hc
    exact not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity hc hOut
  · intro hc
    subst hc
    refine ⟨constantVelocityField 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact smoothSpaceTimeVelocity_constantVelocityField 0
    · simpa using smoothSpaceTimePressure_const (0 : ℝ)
    · intro t x
      simp [timeVelocityDerivative_constantVelocityField,
        spatialConvection_constantVelocityField, spatialPressureGradient_zero,
        spatialLaplacian_constantVelocityField]
    · intro t x
      simpa using spatialDivergence_constantVelocityField (0 : NSSpace) t x
    · simpa using matchesInitialVelocity_constantVelocityField (0 : NSSpace)
    · refine ⟨0, le_rfl, ?_⟩
      intro t
      constructor
      · have hzeroDensity :
            kineticEnergyDensity (constantVelocityField (0 : NSSpace)) t =
              fun _ : NSSpace => (0 : ℝ) := by
          funext x
          simp [kineticEnergyDensity, constantVelocityField]
        rw [hzeroDensity]
        exact
          MeasureTheory.integrable_zero NSSpace ℝ
            (MeasureTheory.volume : MeasureTheory.Measure NSSpace)
      · simp [kineticEnergyAt, kineticEnergyDensity, constantVelocityField]

/-- At positive viscosity, the concrete global-regularity clause is therefore
also impossible for nonzero constant initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (constantInitialVelocity c) :=
    smoothInitialVelocityData_constantInitialVelocity c
  have hdiv : ∀ x, initialSpatialDivergence (constantInitialVelocity c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_constantInitialVelocity c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity hc
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the explicit concrete regularity clause is exact on
constant initial data: it holds precisely in the zero-data case. -/
theorem ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) ↔ c = 0 := by
  constructor
  · intro hClause
    by_contra hc
    exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc hClause
  · intro hc
    subst hc
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitConcreteNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν) (c := (0 : NSSpace))).2 rfl)

/-- The repaired explicit regularity clause is vacuous on nonzero constant
initial data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (constantInitialVelocity c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := constantInitialVelocity c)
      (not_finiteInitialKineticEnergy_constantInitialVelocity hc)

/-- The repaired explicit regularity clause can therefore be true on nonzero
constant initial data while the unrepaired concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_without_regularity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (constantInitialVelocity c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (constantInitialVelocity c) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity
      (ν := ν) hc
  · exact not_ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity hν hc

/-- The structured fully concrete clause also rejects nonzero constant initial
data.  This is the same obstruction as on the explicit surface, transported
through the concrete equivalence theorem. -/
theorem not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity
    {ν : ℝ} {c : NSSpace}
    (hν : 0 < ν)
    (hc : c ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity c
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_constantInitialVelocity c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity hc
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := constantInitialVelocity c)
        hν
        (smoothInitialVelocityData_constantInitialVelocity c)
        (by
          intro x
          simpa using initialSpatialDivergence_constantInitialVelocity c x)).mp hClause)

/-- The structured fully concrete clause is likewise exact on constant initial
data: it holds precisely in the zero-data case. -/
theorem concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := constantInitialVelocity c
          smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_constantInitialVelocity c x } ↔
      c = 0 := by
  constructor
  · intro hClause
    by_contra hc
    exact not_concreteNavierStokesGlobalRegularityClause_constantInitialVelocity hν hc hClause
  · intro hc
    subst hc
    exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_concreteNavierStokesGlobalRegularityClause
        hν
        (smoothInitialVelocityData_constantInitialVelocity (0 : NSSpace))
        (by
          intro x
          simpa using initialSpatialDivergence_constantInitialVelocity (0 : NSSpace) x)
        ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν) (c := (0 : NSSpace))).2 rfl)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
