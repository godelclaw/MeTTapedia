import Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierTriadRigidity

/-!
# Regression and axiom audit for the exact periodic Fourier-triad no-go
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace Regression

open PeriodicFourierTriad

/-- Regression seal for the exact positive cutoff-flux calculation. -/
theorem periodicFourierTriad_cutoffFlux_regression :
    outwardFlux triadSupport (lowModes triadSupport 1) triadVelocity = 4 :=
  triad_cutoffFlux_one

/-- Regression seal for exact global convection-energy cancellation. -/
theorem periodicFourierTriad_globalCancellation_regression :
    nonlinearEnergyRate triadSupport triadSupport triadVelocity = 0 :=
  triad_global_nonlinearEnergyRate

/-- Regression seal for the amplitude-scaling no-go theorem. -/
theorem periodicFourierTriad_noStaticViscousFluxRigidity_regression
    (C nu : ℝ) (hC : 0 ≤ C) (hnu : 0 < nu) :
    ¬ PointwiseViscousFluxRigidity C nu :=
  no_pointwiseViscousFluxRigidity C nu hC hnu

#print axioms PeriodicFourierTriad.triadVelocity_reality
#print axioms PeriodicFourierTriad.triadVelocity_divergenceFree
#print axioms PeriodicFourierTriad.triad_global_nonlinearEnergyRate
#print axioms PeriodicFourierTriad.triad_cutoffFlux_one
#print axioms PeriodicFourierTriad.realScale_triad_cutoffFlux
#print axioms PeriodicFourierTriad.realScale_triad_high_viscousQuadratic
#print axioms PeriodicFourierTriad.realScale_triad_admissible
#print axioms PeriodicFourierTriad.no_pointwiseViscousFluxRigidity
#print axioms periodicFourierTriad_noStaticViscousFluxRigidity_regression

end Regression
end NavierStokes
end FluidDynamics
end Mettapedia
