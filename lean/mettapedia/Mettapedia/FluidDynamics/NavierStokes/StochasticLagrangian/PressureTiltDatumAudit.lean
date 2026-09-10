import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltAlignment

/-!
# Regression tests and axiom audit for the physical pressure-tilt obstruction
-/

open Mettapedia.FluidDynamics.NavierStokes
open PressureTiltDatum PressureTiltOrigin PressureTiltAlignment
open PancakeSpectralFiniteDifference PancakeAnisotropyDepletion

example : PancakeSpectralDefectEvolution.topSpectralDefect (originStrain 1)
    (LocalLowDiffusionBudget.fullVorticity (velocity 1) 0) = 0 := topSpectralDefect_origin 1

example :
    lineRemainder (topVector (originStrain 0))
      (originPressure 0 (topVector (originStrain 0))) = 0 := by
  have h := norm_pressureTilt_sq 0
  norm_num only [zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

example :
    lineRemainder (topVector (originStrain 1))
      (originPressure 1 (topVector (originStrain 1))) ≠ 0 :=
  pressureTilt_ne_zero 1 (by norm_num)

example : (originStrain 1).topGap = 6 * Real.pi := topGap_origin 1

#print axioms FourierFiniteSupport.coordinateDerivative_eq_sum
#print axioms FourierFiniteSupport.fourierCurl_eq_zero
#print axioms FourierFiniteSupport.fullFourierField_eq_sum
#print axioms FourierFiniteSupport.fullStrainOperator_eq_spatialStrain
#print axioms FourierFiniteSupport.fullVorticity_eq_spatialVorticity
#print axioms FourierFiniteSupport.summable_fourierMoment
#print axioms FourierPressurePairSum.pressureCoeff_eq_indicatorPairSum
#print axioms FourierPressurePairSum.pressureCoeff_eq_pairSum
#print axioms PressureTiltAlignment.diagonalDirection_norm_sq
#print axioms PressureTiltAlignment.fullStrainOperator_origin
#print axioms PressureTiltAlignment.inner_diagonalDirection_topVector_ne_zero
#print axioms PressureTiltAlignment.inner_diagonalDirection_topVector_sq
#print axioms PressureTiltAlignment.norm_pressureTilt_sq
#print axioms PressureTiltAlignment.norm_pressure_diagonalDirection_sq
#print axioms PressureTiltAlignment.not_pressureTilt_le_of_defect
#print axioms PressureTiltAlignment.originStrain_eq
#print axioms PressureTiltAlignment.positive_gap_zero_defect_nonzero_pressure
#print axioms PressureTiltAlignment.pressureTilt_ne_zero
#print axioms PressureTiltAlignment.pressure_diagonalDirection
#print axioms PressureTiltAlignment.pressure_diagonalDirection_ne_zero
#print axioms PressureTiltAlignment.pressure_diagonalDirection_perpendicular
#print axioms PressureTiltAlignment.pressure_topVector_perpendicular
#print axioms PressureTiltAlignment.secondEigenvalue_origin
#print axioms PressureTiltAlignment.spectralResidual_origin
#print axioms PressureTiltAlignment.strain_apply
#print axioms PressureTiltAlignment.strain_diagonalDirection
#print axioms PressureTiltAlignment.strain_rayleigh_le
#print axioms PressureTiltAlignment.topEigenvalue_origin
#print axioms PressureTiltAlignment.topGap_origin
#print axioms PressureTiltAlignment.topSpectralDefect_origin
#print axioms PressureTiltAlignment.topVector_diagonalDirection
#print axioms PressureTiltAlignment.topVector_eq_smul_diagonalDirection
#print axioms PressureTiltDatum.infinitePressureCoeff_eq
#print axioms PressureTiltDatum.modes_neg_closed
#print axioms PressureTiltDatum.pressureCoeff_eq
#print axioms PressureTiltDatum.pressureFormula_eq_zero
#print axioms PressureTiltDatum.pressureFormula_values
#print axioms PressureTiltDatum.sum_modes
#print axioms PressureTiltDatum.sum_pressureModes
#print axioms PressureTiltDatum.velocity_conjugate
#print axioms PressureTiltDatum.velocity_eq_zero_of_not_mem
#print axioms PressureTiltDatum.velocity_transverse
#print axioms PressureTiltDatum.velocity_values
#print axioms PressureTiltDatum.velocity_zero
#print axioms PressureTiltOrigin.fullVelocity_divergence
#print axioms PressureTiltOrigin.fullVelocity_fourierCoeff
#print axioms PressureTiltOrigin.fullVelocity_real
#print axioms PressureTiltOrigin.fullVelocity_zero_mean
#print axioms PressureTiltOrigin.fullVorticity_origin
#print axioms PressureTiltOrigin.mFourier_origin
#print axioms PressureTiltOrigin.pressureHessian_origin
#print axioms PressureTiltOrigin.spatialVorticity_origin
#print axioms PressureTiltOrigin.strain_matrix_origin
#print axioms PressureTiltOrigin.velocity_moments
