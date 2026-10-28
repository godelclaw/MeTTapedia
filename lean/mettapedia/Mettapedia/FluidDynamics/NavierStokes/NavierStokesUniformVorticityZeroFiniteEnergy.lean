import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityContinuationSurface

/-!
# Zero-data finite-energy fact for uniform-vorticity examples

This module isolates the whole-space finite-energy fact for zero initial data,
so downstream modules do not need to import concrete witness bundles just to use
the zero datum as an admissible finite-energy datum.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- Zero initial data satisfy the repaired finite-energy admissibility
hypothesis on `ℝ^3`. -/
theorem finiteInitialKineticEnergy_zero :
    finiteInitialKineticEnergy (0 : NSInitialVelocity) := by
  have hzero :
      initialKineticEnergyDensity (0 : NSInitialVelocity) =
        (fun _ : NSSpace => (0 : ℝ)) := by
    funext x
    simp [initialKineticEnergyDensity]
  rw [finiteInitialKineticEnergy, hzero]
  exact
    MeasureTheory.integrable_zero NSSpace ℝ
      (MeasureTheory.volume : MeasureTheory.Measure NSSpace)

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
