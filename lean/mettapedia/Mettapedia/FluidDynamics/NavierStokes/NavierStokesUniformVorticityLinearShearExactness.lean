import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBaseShearWitnessObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityConstantCandidates
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearCandidates
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms

/-!
# Linear-Shear Exactness for Uniform-Vorticity Continuation

This module contains the exactness lemmas for linear-shear initial data on
the explicit and fully concrete Navier--Stokes regularity surfaces.  The
finite-energy and candidate obstructions live in the upstream linear-shear
modules; this file assembles them into iff/without-regularity surfaces.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The fully explicit global-output surface is likewise impossible for nonzero
linear shear initial data, independent of what pressure field is used later. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearInitialVelocity
      (u := u) ha hinit hbd

/-- Zero shear coefficient collapses the linear-shear datum to the zero initial
datum. -/
theorem linearShearInitialVelocity_zero :
    linearShearInitialVelocity 0 = (0 : NSInitialVelocity) := by
  funext x
  simp [linearShearInitialVelocity_apply]

/-- When the shear coefficient vanishes, the affine full-drift family reduces to
constant initial data. -/
theorem linearShearFullDriftInitialVelocity_zero_shear
    (b c : ℝ) :
    linearShearFullDriftInitialVelocity 0 b c =
      constantInitialVelocity
        (EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c) := by
  funext x
  simp [linearShearFullDriftInitialVelocity, linearShearHorizontalDriftInitialVelocity,
    constantInitialVelocity, linearShearInitialVelocity_zero]

/-- The horizontal-plus-vertical drift vector vanishes exactly when both drift
coefficients vanish. -/
theorem single_nsCoord1_add_single_nsCoord2_eq_zero_iff
    {b c : ℝ} :
    EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c =
        (0 : NSSpace) ↔
      b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hneq12 : nsCoord1 ≠ nsCoord2 := by decide
    have hneq21 : nsCoord2 ≠ nsCoord1 := by decide
    refine ⟨?_, ?_⟩
    · have h1 := congrArg (fun v : NSSpace => v nsCoord1) h
      simpa [hneq12] using h1
    · have h2 := congrArg (fun v : NSSpace => v nsCoord2) h
      simpa [hneq21] using h2
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;> simp [nsCoord1, nsCoord2]

/-- The fully explicit global-output surface is exact on the base linear-shear
family: it is inhabited precisely at zero shear. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity_iff
    {ν : ℝ} {a : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν (linearShearInitialVelocity a) ↔ a = 0 := by
  constructor
  · intro hOut
    by_contra ha
    exact not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity ha hOut
  · intro ha
    subst ha
    simpa [linearShearInitialVelocity_zero] using
      ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
        (ν := ν) (c := (0 : NSSpace))).2 rfl)

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, 0, b)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearVerticalDriftInitialVelocity a b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearVerticalDriftInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearHorizontalDriftInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is likewise impossible for nonzero
affine shear initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesGlobalOutput ν (linearShearFullDriftInitialVelocity a b c) := by
  intro hOut
  rcases hOut with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_boundedKineticEnergy_of_matchesInitialVelocity_linearShearFullDriftInitialVelocity
      (u := u) ha hinit hbd

/-- The fully explicit global-output surface is exact on the affine full-drift
linear-shear family: it is inhabited exactly at the zero datum. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff
    {ν : ℝ} {a b c : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hOut
    have ha : a = 0 := by
      by_contra ha
      exact not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity ha hOut
    subst ha
    have hconst :
        EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c =
          (0 : NSSpace) := by
      exact
        (ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν)
          (c := EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c)).1
          (by
            simpa [linearShearFullDriftInitialVelocity_zero_shear] using hOut)
    rcases single_nsCoord1_add_single_nsCoord2_eq_zero_iff.mp hconst with ⟨hb, hc⟩
    exact ⟨rfl, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hzero :
        EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0 =
          (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord1, nsCoord2]
    simpa [linearShearFullDriftInitialVelocity_zero_shear] using
      ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
        (ν := ν) (c := EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0)).2
        hzero)

/-- The fully explicit global-output surface is exact on the vertical-drift
linear-shear subfamily: it is inhabited precisely at the zero datum. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (b := 0) (c := b))

/-- The fully explicit global-output surface is exact on the horizontal-drift
linear-shear subfamily: it is inhabited precisely at the zero datum. -/
theorem ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity_iff
    {ν : ℝ} {a b : ℝ} :
    ExplicitConcreteNavierStokesGlobalOutput ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff
      (ν := ν) (a := a) (b := b) (c := 0))

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero linear shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearInitialVelocity a) :=
    smoothInitialVelocityData_linearShearInitialVelocity a
  have hdiv : ∀ x, initialSpatialDivergence (linearShearInitialVelocity a) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity a x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the base linear-shear family: it holds precisely at zero shear. -/
theorem ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) ↔ a = 0 := by
  constructor
  · intro hClause
    by_contra ha
    exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha hClause
  · intro ha
    subst ha
    simpa [linearShearInitialVelocity_zero] using
      ((ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff
        (ν := ν) hν (c := (0 : NSSpace))).2 rfl)

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data on `ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearVerticalDriftInitialVelocity a b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearVerticalDriftInitialVelocity a b) :=
    smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
  have hdiv : ∀ x, initialSpatialDivergence (linearShearVerticalDriftInitialVelocity a b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearHorizontalDriftInitialVelocity a b) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearHorizontalDriftInitialVelocity a b) :=
    smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
  have hdiv : ∀ x, initialSpatialDivergence (linearShearHorizontalDriftInitialVelocity a b) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the concrete global-regularity clause is likewise
impossible for nonzero affine shear initial data `x ↦ (a * x₁, b, c)` on
`ℝ^3`. -/
theorem not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ ExplicitConcreteNavierStokesRegularityClause ν
      (linearShearFullDriftInitialVelocity a b c) := by
  intro hClause
  have hsmooth : smoothInitialVelocityData (linearShearFullDriftInitialVelocity a b c) :=
    smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
  have hdiv : ∀ x, initialSpatialDivergence (linearShearFullDriftInitialVelocity a b c) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x
  rcases hClause hν hsmooth hdiv with ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity ha
      ⟨u, p, hu, hp, hmom, hinc, hinit, hbd⟩

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the affine full-drift linear-shear family: it holds exactly at the zero datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearFullDriftInitialVelocity a b c) ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hClause
    have ha : a = 0 := by
      by_contra ha
      exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity hν ha hClause
    subst ha
    have hconst :
        EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c =
          (0 : NSSpace) := by
      exact
        (ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff
          (ν := ν) hν
          (c := EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c)).1
          (by
            simpa [linearShearFullDriftInitialVelocity_zero_shear] using hClause)
    rcases single_nsCoord1_add_single_nsCoord2_eq_zero_iff.mp hconst with ⟨hb, hc⟩
    exact ⟨rfl, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hzero :
        EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0 =
          (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord1, nsCoord2]
    simpa [linearShearFullDriftInitialVelocity_zero_shear] using
      ((ExplicitConcreteNavierStokesRegularityClause_constantInitialVelocity_iff
        (ν := ν) hν
        (c := EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0)).2 hzero)

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the vertical-drift linear-shear subfamily: it holds precisely at the zero
datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearVerticalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (b := 0) (c := b))

/-- At positive viscosity, the explicit concrete regularity clause is exact on
the horizontal-drift linear-shear subfamily: it holds precisely at the zero
datum. -/
theorem ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    ExplicitConcreteNavierStokesRegularityClause ν
        (linearShearHorizontalDriftInitialVelocity a b) ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (b := b) (c := 0))

/-- The repaired explicit regularity clause is vacuous on nonzero linear shear
data because the repaired finite-energy hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearInitialVelocity a) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearInitialVelocity a)
      (not_finiteInitialKineticEnergy_linearShearInitialVelocity ha)

/-- The repaired explicit regularity clause can therefore be true on nonzero
linear shear initial data while the unrepaired concrete regularity clause is
false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity_without_regularity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearInitialVelocity a) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (linearShearInitialVelocity a) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity
      (ν := ν) ha
  · exact not_ExplicitConcreteNavierStokesRegularityClause_linearShearInitialVelocity hν ha

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data because the repaired finite-energy hypothesis already fails.
-/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearVerticalDriftInitialVelocity a b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearVerticalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearVerticalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data `x ↦ (a * x₁, b, 0)` because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearHorizontalDriftInitialVelocity a b) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearHorizontalDriftInitialVelocity a b)
      (not_finiteInitialKineticEnergy_linearShearHorizontalDriftInitialVelocity
        (a := a) (b := b) ha)

/-- The repaired explicit regularity clause is likewise vacuous on nonzero
affine shear data `x ↦ (a * x₁, b, c)` because the repaired finite-energy
hypothesis already fails. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearFullDriftInitialVelocity a b c) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := linearShearFullDriftInitialVelocity a b c)
      (not_finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity
        (a := a) (b := b) (c := c) ha)

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data while the unrepaired concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearVerticalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        (ν := ν) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity
        hν ha

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data `x ↦ (a * x₁, b, 0)` while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearHorizontalDriftInitialVelocity a b) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        (ν := ν) (a := a) (b := b) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity
        hν ha

/-- The repaired explicit regularity clause can therefore also be true on
nonzero affine shear initial data `x ↦ (a * x₁, b, c)` while the unrepaired
concrete regularity clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_without_regularity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (linearShearFullDriftInitialVelocity a b c) := by
  refine ⟨?_, ?_⟩
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        (ν := ν) (a := a) (b := b) (c := c) ha
  · exact
      not_ExplicitConcreteNavierStokesRegularityClause_linearShearFullDriftInitialVelocity
        hν ha



/-- The structured fully concrete clause also rejects nonzero linear shear
initial data.  Again this is the explicit obstruction transported through the
concrete equivalence theorem. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity
    {ν : ℝ} {a : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity a
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity a
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity a x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearInitialVelocity a)
        hν
      (smoothInitialVelocityData_linearShearInitialVelocity a)
      (by
          intro x
          simpa using initialSpatialDivergence_linearShearInitialVelocity a x)).mp hClause)

/-- The structured fully concrete clause is exact on the base linear-shear
family: it holds precisely at zero shear. -/
theorem concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearInitialVelocity a
          smooth_initial := smoothInitialVelocityData_linearShearInitialVelocity a
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearInitialVelocity a x } ↔
      a = 0 := by
  constructor
  · intro hClause
    by_contra ha
    exact not_concreteNavierStokesGlobalRegularityClause_linearShearInitialVelocity hν ha hClause
  · intro ha
    subst ha
    simpa [linearShearInitialVelocity_zero] using
      ((concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff
        (ν := ν) hν (c := (0 : NSSpace))).2 rfl)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearVerticalDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearVerticalDriftInitialVelocity a b)
        hν
        (smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x)).mp hClause)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data `x ↦ (a * x₁, b, 0)`. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity
    {ν : ℝ} {a b : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearHorizontalDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearHorizontalDriftInitialVelocity a b)
        hν
        (smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x)).mp hClause)

/-- The structured fully concrete clause also rejects nonzero affine shear
initial data `x ↦ (a * x₁, b, c)`. -/
theorem not_concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity
    {ν : ℝ} {a b c : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity a b c
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity ha
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := linearShearFullDriftInitialVelocity a b c)
        hν
        (smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c)
        (by
          intro x
          simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x)).mp hClause)

/-- The structured fully concrete clause is exact on the affine full-drift
linear-shear family: it holds exactly at the zero datum. -/
theorem concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearFullDriftInitialVelocity a b c
          smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x } ↔
      a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hClause
    have ha : a = 0 := by
      by_contra ha
      exact not_concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity hν ha hClause
    subst ha
    have hconst :
        EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c =
          (0 : NSSpace) := by
      exact
        (concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff
          (ν := ν) hν
          (c := EuclideanSpace.single nsCoord1 b + EuclideanSpace.single nsCoord2 c)).1
          (by
            simpa [linearShearFullDriftInitialVelocity_zero_shear] using hClause)
    rcases single_nsCoord1_add_single_nsCoord2_eq_zero_iff.mp hconst with ⟨hb, hc⟩
    exact ⟨rfl, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    have hzero :
        EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0 =
          (0 : NSSpace) := by
      ext i
      fin_cases i <;> simp [nsCoord1, nsCoord2]
    simpa [linearShearFullDriftInitialVelocity_zero_shear] using
      ((concreteNavierStokesGlobalRegularityClause_constantInitialVelocity_iff
        (ν := ν) hν
        (c := EuclideanSpace.single nsCoord1 0 + EuclideanSpace.single nsCoord2 0)).2 hzero)

/-- The structured fully concrete clause is exact on the vertical-drift
linear-shear subfamily: it holds precisely at the zero datum. -/
theorem concreteNavierStokesGlobalRegularityClause_linearShearVerticalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearVerticalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearVerticalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearVerticalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (b := 0) (c := b))

/-- The structured fully concrete clause is exact on the horizontal-drift
linear-shear subfamily: it holds precisely at the zero datum. -/
theorem concreteNavierStokesGlobalRegularityClause_linearShearHorizontalDriftInitialVelocity_iff
    {ν : ℝ} (hν : 0 < ν) {a b : ℝ} :
    NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := linearShearHorizontalDriftInitialVelocity a b
          smooth_initial := smoothInitialVelocityData_linearShearHorizontalDriftInitialVelocity a b
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_linearShearHorizontalDriftInitialVelocity a b x } ↔
      a = 0 ∧ b = 0 := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (concreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_iff
      (ν := ν) hν (a := a) (b := b) (c := 0))



end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
