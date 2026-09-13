import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressureCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteVelocityInvariant

/-! Reality symmetry of the full, unrestricted momentum right-hand side. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullVelocityRHSReality

open scoped ComplexConjugate
open PeriodicFourierTriad PancakeBlockReality PancakePeriodicVorticityEquation
open PancakeCoefficientLimitEquation PancakeInfinitePressureCoefficients
open PancakeFiniteVelocityInvariant PancakeInfiniteVelocityEnvelope

theorem infiniteVelocityRHS_conjugate (ν : ℝ) (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) :
    infiniteVelocityRHS ν u (-q) = coefficientConjugate (infiniteVelocityRHS ν u q) := by
  have hc : (-unitTorusDerivativePhase) • infiniteConvection u (-q) =
      coefficientConjugate ((-unitTorusDerivativePhase) • infiniteConvection u q) := by
    rw [infiniteConvection_neg_conjugate u hr]
    ext i
    simp [coefficientConjugate, unitTorusDerivativePhase, map_mul, map_ofNat]
  rw [infiniteVelocityRHS, hc, lerayMode_neg_conjugate,
    unitTorusViscousVorticityCoeff_neg_conjugate ν u hr]
  ext i
  simp [infiniteVelocityRHS, coefficientConjugate]

end Mettapedia.FluidDynamics.NavierStokes.FullVelocityRHSReality
