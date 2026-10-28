import Mettapedia.FluidDynamics.NavierStokes.NavierStokesStreamwiseInvariantFiniteEnergyObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLinearShearObstruction
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
# Navier-Stokes streamwise-invariant finite-energy obstruction regression

Focused theorem-level checks for the generic streamwise-invariant finite-energy
obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace NavierStokesStreamwiseInvariantFiniteEnergyObstructionRegression

theorem not_finiteInitialKineticEnergy_constant_streamwise_regression :
    ¬ finiteInitialKineticEnergy
        (constantInitialVelocity (EuclideanSpace.single nsCoord0 (1 : ℝ))) := by
  refine
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero ?_ ?_ ?_
  · simpa using
      smoothInitialVelocityData_constantInitialVelocity
        (EuclideanSpace.single nsCoord0 (1 : ℝ))
  · intro x s
    ext i
    fin_cases i <;> simp [constantInitialVelocity, nsCoord0]
  · intro hzero
    have hcoord :=
      congrArg
        (fun u : NSInitialVelocity => u 0 nsCoord0)
        hzero
    simp [constantInitialVelocity, nsCoord0] at hcoord

theorem not_finiteInitialKineticEnergy_linearShearFullDrift_regression :
    ¬ finiteInitialKineticEnergy (linearShearFullDriftInitialVelocity 1 1 1) := by
  refine
    not_finiteInitialKineticEnergy_of_translationInvariantAlong_streamwise_of_ne_zero ?_ ?_ ?_
  · simpa using smoothInitialVelocityData_linearShearFullDriftInitialVelocity 1 1 1
  · exact translationInvariantAlong_linearShearFullDriftInitialVelocity_streamwise 1 1 1
  · intro hzero
    have hdeg :=
      (linearShearFullDriftInitialVelocity_eq_zero_iff
        (a := 1) (b := 1) (c := 1)).mp hzero
    norm_num at hdeg

end NavierStokesStreamwiseInvariantFiniteEnergyObstructionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
