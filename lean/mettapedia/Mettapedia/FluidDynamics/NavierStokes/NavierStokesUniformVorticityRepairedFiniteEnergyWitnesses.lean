import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityHeatShearExactnessTransport
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityLinearShearFiniteWitnesses

/-!
# Repaired finite-energy witnesses for uniform-vorticity examples

This module contains the repaired finite-energy regularity and structured
concrete clauses for constant, linear-shear, heat-shear, and transported
heat-shear data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- On constant initial data, the repaired explicit finite-energy regularity
clause always holds: it is realized at the zero datum and vacuous elsewhere. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_all
    {ν : ℝ} {c : NSSpace} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (constantInitialVelocity c) := by
  by_cases hfinite : finiteInitialKineticEnergy (constantInitialVelocity c)
  · exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_constantInitialVelocity_iff
          (ν := ν) (c := c)).2
          ((finiteInitialKineticEnergy_constantInitialVelocity_iff
            (c := c)).1 hfinite))
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
        (u₀ := constantInitialVelocity c) hfinite

/-- On the full affine linear-shear family, the repaired explicit finite-energy
regularity clause always holds: it is realized exactly on the zero datum and
vacuous elsewhere. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all
    {ν : ℝ} {a b c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearFullDriftInitialVelocity a b c) := by
  by_cases hfinite : finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c)
  · exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_linearShearFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (b := b) (c := c)).2
          ((finiteInitialKineticEnergy_linearShearFullDriftInitialVelocity_iff
            (a := a) (b := b) (c := c)).1 hfinite))
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
        (u₀ := linearShearFullDriftInitialVelocity a b c) hfinite

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the base linear-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearInitialVelocity_all
    {ν : ℝ} {a : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearInitialVelocity a) := by
  simpa [linearShearFullDriftInitialVelocity_zero_drifts] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (b := 0) (c := 0))

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the vertical-drift affine linear-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearVerticalDriftInitialVelocity_all
    {ν : ℝ} {a b : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearVerticalDriftInitialVelocity a b) := by
  simpa [linearShearFullDriftInitialVelocity_zero_horizontalDrift] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (b := 0) (c := b))

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the horizontal-drift affine linear-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearHorizontalDriftInitialVelocity_all
    {ν : ℝ} {a b : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (linearShearHorizontalDriftInitialVelocity a b) := by
  simpa [linearShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (b := b) (c := 0))

/-- On the full-drift heat-shear family, the repaired explicit finite-energy
regularity clause always holds: it is realized exactly on the zero datum and
vacuous elsewhere. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all
    {ν : ℝ} {a k d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearFullDriftInitialVelocity a k d c) := by
  by_cases hfinite : finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c)
  · exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (d := d) (c := c)).2
          ((finiteInitialKineticEnergy_heatShearFullDriftInitialVelocity_iff
            (a := a) (k := k) (d := d) (c := c)).1 hfinite))
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
        (u₀ := heatShearFullDriftInitialVelocity a k d c) hfinite

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the base heat-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearInitialVelocity_all
    {ν : ℝ} {a k : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearInitialVelocity a k) := by
  simpa [heatShearFullDriftInitialVelocity_zero_drifts] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (k := k) (d := 0) (c := 0))

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the vertical-drift heat-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearVerticalDriftInitialVelocity_all
    {ν : ℝ} {a k c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearVerticalDriftInitialVelocity a k c) := by
  simpa [heatShearFullDriftInitialVelocity_zero_streamwiseDrift] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (k := k) (d := 0) (c := c))

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the streamwise-drift heat-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearStreamwiseDriftInitialVelocity_all
    {ν : ℝ} {a k d : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearStreamwiseDriftInitialVelocity a k d) := by
  simpa [heatShearFullDriftInitialVelocity_zero_verticalDrift] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all
      (ν := ν) (a := a) (k := k) (d := d) (c := 0))

/-- On the transported full-drift heat-shear family, the repaired explicit
finite-energy regularity clause always holds: it is realized exactly on the
zero datum and vacuous elsewhere. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_all
    {ν : ℝ} {a k b d c : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportFullDriftInitialVelocity a k b d c) := by
  by_cases hfinite : finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c)
  · exact
      ExplicitConcreteNavierStokesGlobalOutput_implies_ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
        ((ExplicitConcreteNavierStokesGlobalOutput_heatShearTransportFullDriftInitialVelocity_iff
          (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c)).2
          ((finiteInitialKineticEnergy_heatShearTransportFullDriftInitialVelocity_iff
            (a := a) (k := k) (b := b) (d := d) (c := c)).1 hfinite))
  · exact
      ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_of_not_finiteInitialKineticEnergy
        (u₀ := heatShearTransportFullDriftInitialVelocity a k b d c) hfinite

/-- The repaired explicit finite-energy regularity clause is therefore
unconditional on the transported heat-shear family. -/
theorem ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportInitialVelocity_all
    {ν : ℝ} {a k b : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause
      ν (heatShearTransportInitialVelocity a k b) := by
  simpa [heatShearTransportFullDriftInitialVelocity_zero_drifts] using
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_all
      (ν := ν) (a := a) (k := k) (b := b) (d := 0) (c := 0))

/-- On constant admissible data, the repaired structured fully concrete clause
is automatic. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_constantInitialVelocity_all
    {ν : ℝ} (hν : 0 < ν) {c : NSSpace}
    (hfinite : finiteInitialKineticEnergy (constantInitialVelocity c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := constantInitialVelocity c
         smooth_initial := smoothInitialVelocityData_constantInitialVelocity c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_constantInitialVelocity c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν
      (smoothInitialVelocityData_constantInitialVelocity c)
      (by
        intro x
        simpa using initialSpatialDivergence_constantInitialVelocity c x)
      hfinite).2
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_constantInitialVelocity_all
        (ν := ν) (c := c))

/-- On admissible affine linear-shear data, the repaired structured fully
concrete clause is automatic. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_linearShearFullDriftInitialVelocity_all
    {ν : ℝ} (hν : 0 < ν) {a b c : ℝ}
    (hfinite : finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity a b c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := linearShearFullDriftInitialVelocity a b c
         smooth_initial := smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν
      (smoothInitialVelocityData_linearShearFullDriftInitialVelocity a b c)
      (by
        intro x
        simpa using initialSpatialDivergence_linearShearFullDriftInitialVelocity a b c x)
      hfinite).2
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_linearShearFullDriftInitialVelocity_all
        (ν := ν) (a := a) (b := b) (c := c))

/-- On admissible full-drift heat-shear data, the repaired structured fully
concrete clause is automatic. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearFullDriftInitialVelocity_all
    {ν : ℝ} (hν : 0 < ν) {a k d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearFullDriftInitialVelocity a k d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearFullDriftInitialVelocity a k d c
         smooth_initial := smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν
      (smoothInitialVelocityData_heatShearFullDriftInitialVelocity a k d c)
      (by
        intro x
        simpa using initialSpatialDivergence_heatShearFullDriftInitialVelocity a k d c x)
      hfinite).2
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearFullDriftInitialVelocity_all
        (ν := ν) (a := a) (k := k) (d := d) (c := c))

/-- On admissible transported full-drift heat-shear data, the repaired
structured fully concrete clause is automatic. -/
theorem finiteEnergyConcreteNavierStokesGlobalRegularityClause_heatShearTransportFullDriftInitialVelocity_all
    {ν : ℝ} (hν : 0 < ν) {a k b d c : ℝ}
    (hfinite : finiteInitialKineticEnergy (heatShearTransportFullDriftInitialVelocity a k b d c)) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := heatShearTransportFullDriftInitialVelocity a k b d c
         smooth_initial := smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c
         divergence_free_initial := by
           intro x
           simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x
         finite_initial_energy := hfinite } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact
    (finiteEnergyConcreteNavierStokesGlobalRegularityClause_iff
      hν
      (smoothInitialVelocityData_heatShearTransportFullDriftInitialVelocity a k b d c)
      (by
        intro x
        simpa using initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity a k b d c x)
      hfinite).2
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_heatShearTransportFullDriftInitialVelocity_all
        (ν := ν) (a := a) (k := k) (b := b) (d := d) (c := c))

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
