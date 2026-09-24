import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltEvolution

/-!
# Regression tests and axiom audit for the physical alignment-loss evolution
-/

open scoped Topology
open Mettapedia.FluidDynamics.NavierStokes
open PressureTiltDatum PressureTiltResidualRate PressureTiltEvolution PancakeLocalInfiniteVelocity

example (nu : ℝ) : residualRate 0 nu = 0 := by
  rw [residualRate_eq]
  simp

example (nu : ℝ) : residualRate 1 nu ≠ 0 := residualRate_ne_zero 1 nu (by norm_num)

example (nu : ℝ) :
    residualRate 1 nu 0 - residualRate 1 nu 1 = 384 * Real.pi^3 / 5 := by
  simpa only [mul_one] using residualRate_coordinate_difference 1 nu

example (nu : ℝ) (hnu : 0 < nu) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity 1) T B,
        defectAtOrigin (s.coefficients 0) = 0 ∧
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < defectAtOrigin (s.coefficients t)) :=
  exists_local_defect_growth 1 nu hnu (by norm_num)

#check PressureTiltEvolution.exists_local_alignment_loss
#check PressureTiltEvolution.exists_local_defect_growth

#print axioms EndpointDerivative.hasDerivWithinAt_Ici_of_continuousOn
#print axioms FourierFiniteJets.coordinateJet_eq_fullFourierField
#print axioms FourierFiniteJets.hasContinuousCoordinateJet
#print axioms FourierFiniteJets.hasContinuousCoordinateJet_component
#print axioms FourierFiniteJets.laplacian_gradient_eq_matrixReconstruction
#print axioms FourierFiniteJets.scalarJetCoeff_supported
#print axioms FourierFiniteJets.scalarJet_hasDerivAt
#print axioms FourierFiniteJets.spatialVelocityGradient_eq_matrixReconstruction
#print axioms LocalInitialGradient.continuous_gradientField
#print axioms LocalInitialGradient.continuous_gradientRHSField
#print axioms LocalInitialGradient.coordinateDerivative_hasDerivWithinAt_initial
#print axioms LocalInitialGradient.gradientField_hasDerivWithinAt_initial
#print axioms LocalInitialGradient.velocityGradient_hasDerivWithinAt_initial
#print axioms LocalInitialSpectral.fullStrainOperator_hasDerivWithinAt_initial
#print axioms LocalInitialSpectral.fullVorticity_hasDerivWithinAt_initial
#print axioms LocalInitialSpectral.hasDerivWithinAt_matrixCurl
#print axioms LocalInitialSpectral.hasDerivWithinAt_symmetrize
#print axioms PressureTiltEvolution.defectAtOrigin_initial
#print axioms PressureTiltEvolution.eventually_defect_pos
#print axioms PressureTiltEvolution.eventually_residual_ne_zero
#print axioms PressureTiltEvolution.exists_local_alignment_loss
#print axioms PressureTiltEvolution.exists_local_defect_growth
#print axioms PressureTiltEvolution.fullSymmetricStrain_origin
#print axioms PressureTiltEvolution.residualAtOrigin_initial
#print axioms PressureTiltEvolution.residual_hasDerivWithinAt_initial
#print axioms PressureTiltLocalSolution.exists_localMomentEnvelope
#print axioms PressureTiltLocalSolution.torusFourierVelocity_fullVelocity
#print axioms PressureTiltResidualRate.eigenvalueRate_eq
#print axioms PressureTiltResidualRate.hasDerivAt_residual_of_rates
#print axioms PressureTiltResidualRate.norm_residualRate_sq
#print axioms PressureTiltResidualRate.residualRate_coordinate_difference
#print axioms PressureTiltResidualRate.residualRate_eq
#print axioms PressureTiltResidualRate.residualRate_ne_zero
#print axioms PressureTiltResidualRate.strainRate_diagonalDirection
#print axioms PressureTiltResidualRate.vorticityRate_eq
#print axioms PressureTiltTangent.gradientRate_eq
#print axioms PressureTiltTangent.gradient_origin
#print axioms PressureTiltTangent.laplacian_gradient_origin
#print axioms PressureTiltTangent.velocity_origin
#print axioms SpatialNavierStokesTangent.gradient_infiniteVelocityRHS
#print axioms SpatialNavierStokesTangent.gradient_infiniteVelocityRHS_of_stagnation
#print axioms SpatialNavierStokesTangent.matrixTransport_eq_zero
#print axioms SpectralEigenvalueWithin.hasDerivWithinAt_topEigenvalue
