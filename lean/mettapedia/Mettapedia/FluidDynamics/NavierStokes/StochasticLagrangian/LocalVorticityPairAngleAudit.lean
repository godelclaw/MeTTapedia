import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityPairAngleSymmetric
import Mettapedia.Analysis.CrossProductStrainTests

/-! Audit of actual two-point dynamics, signed perturbations, and the growing-angle canary. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.Analysis.EuclideanCrossProduct
open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad LocalLowDiffusionBudget

example (u : FourierVelocity) (x y : UnitAddTorus (Fin 3)) :
    0 ≤ angleEnergy (fullVorticity u x) (fullVorticity u y) ∧
      angleEnergy (fullVorticity u x) (fullVorticity u y) ≤ 1 :=
  ⟨angleEnergy_nonneg _ _, angleEnergy_le_one _ _⟩

example (u : FourierVelocity) (x y : UnitAddTorus (Fin 3)) (hx : fullVorticity u x = 0) :
    angleEnergy (fullVorticity u x) (fullVorticity u y) = 0 := by
  simp [angleEnergy, hx]

#print axioms Mettapedia.Analysis.EuclideanCrossProduct.cross_mulVec_add_mulVec_cross
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.hasDerivAt_cross
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.angleEnergy_nonneg
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.angleEnergy_le_one
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.hasDerivAt_angleEnergy
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.angleRate_eq_common_add_perturbation
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.hasDerivAt_cross_of_strainEquations
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.hasDerivAt_angleEnergy_of_strainEquations
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.neg_two_topEigenvalue_le_rayleigh
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.commonStrain_angleRate_le_defects
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.angleRate_le_defects_add_perturbation
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.cross_fullStrain_apply_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.trace_fullStrainOperator_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.pairAngleRate_le_topSpectralDefects
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.hasDerivAt_pairCross_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.hasDerivAt_pairAngle_path
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.deriv_pairAngle_path_le_topSpectralDefects
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.symmetricPairForcing_eq
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.cross_rate_eq_symmetric
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.angleRate_eq_symmetric
#print axioms Mettapedia.Analysis.EuclideanCrossProduct.hasDerivAt_angleEnergy_symmetricStrain
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.symmetricAngleRate_le_endpointDefects
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.endpointDefectCoefficient_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.pairAngleRate_le_endpointDefects
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.thirdEigenvalue_mul_norm_sq_le_rayleigh
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.topGap_sub_two_topEigenvalue_le_rayleigh
#print axioms Mettapedia.FluidDynamics.NavierStokes.TraceFreeStrainAngle.symmetricAngleRate_le_gap_damping
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.pairAngleRate_le_gap_damping
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPairAngle.deriv_pairAngle_path_le_gap_damping
