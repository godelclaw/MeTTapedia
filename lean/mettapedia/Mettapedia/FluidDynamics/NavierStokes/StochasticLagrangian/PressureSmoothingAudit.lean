import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SmoothedPressureBudget

/-! Sharp-mode regressions and dependency audit for pressure-patch smoothing. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingAudit

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeQuadraticFourierSupport
open FourierPressureCommutator FourierEllipticProductEnergy FourierResolventSmoothing
open Mettapedia.Analysis.FiniteResolventEnergy Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem norm_four_eq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 4 = (∑ j : Fin 3, ‖v j‖ ^ 2) ^ 2 := by
  rw [← EuclideanSpace.norm_sq_eq]
  ring

example (epsilon : ℝ) (z : ℂ) :
    smoothCutoff epsilon (Finsupp.single 0 z) = Finsupp.single 0 z := by
  ext q
  by_cases hq : q = 0
  · subst q
    exact smoothCutoff_apply_zero epsilon _
  · simp [smoothCutoff_apply, smooth, Finsupp.single_eq_of_ne hq]

example (c : FourierCoeff (Fin 3)) : smoothCutoff 0 c = c := smoothCutoff_zero c

/-- Nonreal coefficients are damped, not real-part projected. -/
example :
    smoothCutoff 1 (Finsupp.single (![1, 0, 0] : Wavevector) Complex.I) ![1, 0, 0] = Complex.I / 2 := by
  norm_num [smoothCutoff_apply, smooth, multiplier, realFrequency, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_three]
  ring

/-- First and second derivative energies both attain the sharp unit-mode bound. -/
example :
    let c := Finsupp.single (![1, 0, 0] : Wavevector) Complex.I
    coordinateEnergy (smoothCutoff 1 c).support (smoothCutoff 1 c) = 1 / 4 ∧
      secondCoordinateEnergy (smoothCutoff 1 c).support (smoothCutoff 1 c) = 1 / 4 := by
  dsimp only
  rw [support_smoothCutoff 1 (by norm_num)]
  norm_num [coordinateEnergy_eq, secondCoordinateEnergy_eq, smoothCutoff_apply, smooth, multiplier,
    norm_four_eq, realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, norm_mul, norm_inv]

/-- The spatial L2 error, not only its coefficient surrogate, attains epsilon/4. -/
example :
    let c := Finsupp.single (![1, 0, 0] : Wavevector) Complex.I
    (∫ x : T3, ‖fourierPolynomial c x - fourierPolynomial (smoothCutoff 1 c) x‖ ^ 2) = 1 / 4 := by
  dsimp only
  rw [integral_error_sq_eq 1 (by norm_num)]
  unfold scalarEnergy
  simp only [smoothCutoff_apply]
  simp_rw [norm_sub_smooth_sq]
  norm_num [multiplier, realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- Two active coordinates contribute squared frequency two and fourth power four. -/
example :
    let c := Finsupp.single (![1, 1, 0] : Wavevector) Complex.I
    secondCoordinateEnergy (smoothCutoff (1 / 2) c).support (smoothCutoff (1 / 2) c) = 1 := by
  dsimp only
  rw [support_smoothCutoff (1 / 2) (by norm_num)]
  norm_num [secondCoordinateEnergy_eq, smoothCutoff_apply, smooth, multiplier,
    norm_four_eq, realFrequency, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, norm_mul, norm_inv]

end Mettapedia.FluidDynamics.NavierStokes.PressureSmoothingAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.smoothCutoff_apply
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.support_smoothCutoff
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.smoothCutoff_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.smoothCutoff_apply_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.resolvent_coefficient_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.coordinateEnergy_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.secondCoordinateEnergy_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.coordinateEnergy_smooth_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.secondCoordinateEnergy_smooth_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.error_energy_cutoff_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.integral_error_sq_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierResolventSmoothing.integral_error_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing.transverse_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing.frozenPatchEnergy_le_smooth
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing.tracePatchEnergy_smooth_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePatchSmoothing.tiltCommutatorEnergy_smooth_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureBudget.exists_weighted_smoothed_pressure_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureBudget.exists_local_smoothed_pressure_budget
