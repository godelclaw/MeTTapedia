import Mettapedia.Analysis.SignedCrossKernelRateDecomposition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularExplicitMean

/-!
# Strain, relative transport and viscosity in the actual signed source rate

The equality identifies algebraic channels of the actual material rate.
No sign or dissipativity is asserted for an individual channel. In
particular, the viscosity channel still requires spatial integration by
parts and a nonlinear estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularRateDecomposition

open Mettapedia.Analysis SignedCrossKernel UnitTorusProductTransport
open PeriodicFourierTriad LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalAnnularExplicitRate LocalAnnularSourcePathChainRule
open LocalAnnularStretchEvolution VorticityAnnularKernelTransport

local notation "T6" => UnitAddTorus (Fin 3 ⊕ Fin 3)

theorem explicitRate_eq (n N : ℕ) (L nu : ℝ) (u : FourierVelocity) (x : T6) :
    explicitRate n N L nu u x = (1 / 2 : ℝ) *
      (highAmplitudeStrainRate n L (fullStrainOperator u (leftPoint x))
          (fullStrainOperator u (rightPoint x))
          (PeriodicRieszPolynomial.kernel N (leftPoint x - rightPoint x))
          (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x)) +
        highAmplitudeStretch (2 * (n + 1)) L
          (kernelDirectionalRate N (leftPoint x - rightPoint x)
            ((fun j ↦ LocalMeanAlignmentBalance.velocity u (leftPoint x) j) -
             (fun j ↦ LocalMeanAlignmentBalance.velocity u (rightPoint x) j)))
          (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x)) +
        nu * highAmplitudeEndpointRate n L
          (PeriodicRieszPolynomial.kernel N (leftPoint x - rightPoint x))
          (fullVorticity u (leftPoint x)) (fullVorticity u (rightPoint x))
          (fullVorticityLaplacian u (leftPoint x)) (fullVorticityLaplacian u (rightPoint x))) := by
  unfold explicitRate materialHighAmplitudeRate materialPairedRate
  rw [highAmplitudeRate_eq_strain_add_kernel_add_endpoint]

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularRateDecomposition
