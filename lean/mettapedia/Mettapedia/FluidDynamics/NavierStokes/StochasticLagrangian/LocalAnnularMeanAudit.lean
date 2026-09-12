import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularMeanBalance
import Mettapedia.Analysis.UnitTorusMaterialBalanceTests

/-! Audit of the two-endpoint spatial mean balance and its signed time identity. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes Mettapedia.Analysis
open PeriodicFourierTriad LocalAnnularMeanBalance

example (n : ℕ) (L t : ℝ) (u : ℝ → FourierVelocity)
    (x : UnitAddTorus (Fin 3 ⊕ Fin 3)) : frozenMaterialRate n 0 L u t x = 0 := by
  simp [frozenMaterialRate, UnitTorusMaterialBalance.scalarMaterialRate, density,
    SignedCrossKernel.highAmplitudeStretch, SignedCrossKernel.pairedStretch]

#print axioms Mettapedia.Analysis.CompactMeanDerivative.hasDerivAt_mean_of_uniform_lipschitz
#print axioms Mettapedia.Analysis.UnitTorusWeakDerivative.measurePreserving_torusPoint
#print axioms Mettapedia.Analysis.UnitTorusWeakDerivative.integral_coordinateRate_mul
#print axioms Mettapedia.Analysis.UnitTorusWeakDerivative.integral_coordinateTransport_zero
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalance.ae_ae_materialRate_split
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalance.ae_ae_differentiableAt_materialLine
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalance.ae_hasDerivAt_mean_materialRate
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalance.intervalIntegral_materialRate_eq
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalance.integral_mean_eq_initial_add_weighted_materialRate
#print axioms Mettapedia.Analysis.UnitTorusProductTransport.coordinateDivergence_pairVelocity
#print axioms Mettapedia.Analysis.UnitTorusProductTransport.integral_pair
#print axioms Mettapedia.Analysis.SignedCrossKernel.locallyLipschitz_highAmplitudeStretch_even
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance.integral_density_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance.divergence_extendedProductVelocity
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance.ae_hasDerivAt_mean
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance.integral_frozenMaterialRate_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMeanBalance.integral_source_eq_initial_add_weighted_rate
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalanceTests.materialRate_time
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalanceTests.productVelocity_divergence_const
#print axioms Mettapedia.Analysis.UnitTorusMaterialBalanceTests.integral_materialRate_abs_zero
