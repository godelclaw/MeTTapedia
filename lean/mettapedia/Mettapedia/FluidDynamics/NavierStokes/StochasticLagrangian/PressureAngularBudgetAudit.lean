import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalPressureAngularBudget

/-! Regression and axiom audit for localized pressure angular budgets. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureAngularBudgetAudit

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakeAnisotropyDepletion PancakeQuadraticFourierSupport
open PressureTiltSymbol FourierPressureTraceSymbol FourierPressureLocalization
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (e : R3) : tiltSymbol e 0 = 0 := tiltSymbol_zero e

example (e k : R3) (h : ⟪k, e⟫ = 0) : tiltSymbol e k = 0 := by
  simp [tiltSymbol, h]

example (e : R3) (he : ‖e‖ = 1) : tiltSymbol e e = 0 := by
  simp [tiltSymbol, lineRemainder, he]

/-- Oblique frequencies really have a nonzero transverse pressure symbol. -/
example :
    let e := (EuclideanSpace.basisFun (Fin 3) ℝ) 0
    let f := (EuclideanSpace.basisFun (Fin 3) ℝ) 1
    tiltSymbol e (e + f) = (1 / 2 : ℝ) • f := by
  dsimp only
  norm_num [tiltSymbol, lineRemainder, norm_add_sq_real,
    inner_add_left, inner_add_right, EuclideanSpace.inner_single_right]

/-- The output of a shifted mode may be zero; the variation bound still applies. -/
example (e k : R3) (he : ‖e‖ = 1) (hk : k ≠ 0) :
    ‖tiltSymbol e k - tiltSymbol e 0‖ ≤ 4 := by
  simpa only [sub_zero, mul_div_cancel_right₀ 4 (norm_ne_zero_iff.mpr hk)] using
    norm_tiltSymbol_sub_le e k 0 he hk

/-- The tail really vanishes at the global symbol bound. -/
example (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) :
    tiltTailTraceEnergy c chi outputs u e 1 = 0 := by
  have hm (q : Wavevector) : ‖complexTiltSymbol e q‖ ≤ 1 := by
    rw [complexTiltSymbol, norm_complexifyVector]
    exact norm_tiltSymbol_le_one e _ he
  simp [tiltTailTraceEnergy, scalarEnergy, not_lt.mpr (hm _)]

end Mettapedia.FluidDynamics.NavierStokes.PressureAngularBudgetAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.tiltSymbol_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.tiltSymbol_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.norm_sq_smul_tiltSymbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.norm_tiltSymbol_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.norm_tiltSymbol_le_one
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.tiltSymbol_eq_remainder_projector
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.norm_real_unitProjector_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTiltSymbol.norm_tiltSymbol_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.norm_complexifyVector
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.complexifyVector_sub
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.realFrequency_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.realFrequency_add
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.complexTiltSymbol_neg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.coefficientVec_tiltCoefficient_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.realSymmetric_tiltCoefficient_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.scalarEnergy_traceAmplitude
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.norm_realTraceAmplitude_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureTraceSymbol.scalarEnergy_realTraceAmplitude_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.cutoffFrequencyMass_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.localized_tiltCoefficient_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.frozenPatchEnergy_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.frozenPatchEnergy_le_main_add_commutator
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.frozenPatchEnergy_le_with_tail
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.norm_complexTiltSymbol_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.tiltCommutatorEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.norm_complexTiltSymbol_output_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization.frozenPatchEnergy_le_of_cone
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.scalarReconstruction_convolution
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.reconstruction_realTraceAmplitude
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.continuous_realPressureTrace
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.realPressureTrace_eq_sum_diagonal
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.tracePatchEnergy_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.integral_realPressureTrace_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.sum_tracePatchEnergy_eq_integral
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy.sum_tracePatchEnergy_le_weighted
#print axioms Mettapedia.FluidDynamics.NavierStokes.WeightedPressureAngularBudget.exists_weighted_pressure_angular_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalPressureAngularBudget.exists_local_pressure_angular_budget
