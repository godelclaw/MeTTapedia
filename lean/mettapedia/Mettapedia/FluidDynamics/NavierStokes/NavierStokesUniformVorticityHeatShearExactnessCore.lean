import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBaseShearWitnessObstructions
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearFullDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearStreamwiseDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearVerticalDriftEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearEnergyTransport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearExactness
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
# Undrifted Heat-Shear Exactness for Uniform-Vorticity Continuation

This module contains the exactness and repaired-clause surfaces for the
undrifted heat-shear initial profile.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearInitialVelocity a k) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired explicit regularity clause can therefore also be true on
nontrivial heat-shear initial data while the unrepaired concrete regularity
clause is false there. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity_without_regularity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ν (heatShearInitialVelocity a k) ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause
        ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity
      (ν := ν) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The structured fully concrete clause also rejects nontrivial heat-shear
initial data. -/
theorem not_concreteNavierStokesGlobalRegularityClause_heatShearInitialVelocity
    {ν : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ¬ NavierStokesGlobalRegularityClause
        mkFullyConcreteNavierStokesSurface
        { viscosity := ν
          viscosity_pos := hν
          initialVelocity := heatShearInitialVelocity a k
          smooth_initial := smoothInitialVelocityData_heatShearInitialVelocity a k
          divergence_free_initial := by
            intro x
            simpa using initialSpatialDivergence_heatShearInitialVelocity a k x } := by
  intro hClause
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_heatShearInitialVelocity ha hk
      ((concreteNavierStokesGlobalRegularityClause_iff
        (ν := ν) (u₀ := heatShearInitialVelocity a k)
        hν
        (smoothInitialVelocityData_heatShearInitialVelocity a k)
        (by
          intro x
          simpa using initialSpatialDivergence_heatShearInitialVelocity a k x)).mp hClause)



/-- On nonnegative slabs, the explicit uniform-vorticity continuation clause is
also vacuous for nontrivial heat-shear initial data because the finite-time
witness type is already empty there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitUniformVorticityContinuationClause_of_not_nonempty_finiteTimeWitness
      (u₀ := heatShearInitialVelocity a k)
      (not_nonempty_ExplicitFiniteTimeRegularityWitness_heatShearInitialVelocity
        (ν := ν) (T := T) (a := a) (k := k) ha hk hT)

/-- The explicit uniform-vorticity continuation clause can therefore be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hT : 0 ≤ T) :
    ExplicitUniformVorticityContinuationClause ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitUniformVorticityContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk hT
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

/-- The repaired uniform-vorticity continuation clause is also vacuous on
nontrivial heat-shear data because the repaired finite-energy hypothesis
already fails. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity
    {ν T : ℝ} {a k : ℝ}
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
      ν (heatShearInitialVelocity a k) T := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_of_not_finiteInitialKineticEnergy
      (u₀ := heatShearInitialVelocity a k)
      (not_finiteInitialKineticEnergy_heatShearInitialVelocity ha hk)

/-- The repaired uniform-vorticity clause can therefore also be true on
nontrivial heat-shear data while the concrete regularity clause is false
there. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity_without_regularity
    {ν T : ℝ} {a k : ℝ}
    (hν : 0 < ν)
    (ha : a ≠ 0) (hk : k ≠ 0) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (heatShearInitialVelocity a k) T ∧
      ¬ ExplicitConcreteNavierStokesRegularityClause ν (heatShearInitialVelocity a k) := by
  refine ⟨?_, ?_⟩
  · exact ExplicitFiniteEnergyUniformVorticityContinuationClause_heatShearInitialVelocity
      (ν := ν) (T := T) (a := a) (k := k) ha hk
  · exact not_ExplicitConcreteNavierStokesRegularityClause_heatShearInitialVelocity hν ha hk

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
