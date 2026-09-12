import Mettapedia.Analysis.PeriodicRadialRiesz
import Mettapedia.Analysis.ScalarTripleProductEvolutionTests

/-!
# Checks of the constructed radial tensor and its periodic scope

Coplanar depletion is tested on the Fourier-defined Euclidean kernel,
not just on an operator assumed to have radial form. Periodic moments
and the signed image sum are tested separately. The periodic operator
is not assumed radial in a chosen shortest torus displacement.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialRieszTensorTests

open EuclideanCrossProduct WeightedCrossProductTests
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
open MeasureTheory
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem constructed_coplanar_depletion (N n : ℕ) :
    SignedCrossKernel.pairedStretch n (RadialRieszRegularization.tensor N leftVector)
      leftVector rightVector = 0 ∧ ‖cross leftVector rightVector‖ ^ 2 = 1 := by
  refine ⟨?_, cross_norm_sq⟩
  have ha : leftVector ≠ 0 := by
    intro h
    have hh := endpoint_norm_sq.1
    simp [h] at hh
  apply RadialRieszRegularization.pairedStretch_tensor_eq_zero_of_coplanar N n
    (EuclideanSpace.single 0 1) (by simp) ha
  exact (real_inner_comm _ _).trans (inner_self_cross _ _)

theorem periodic_firstMoment (N : ℕ) :
    (∫ q : T3, ‖q‖ * ‖PeriodicRadialRiesz.tensor N q‖) ≤
      2 * ∑ i : Fin 3, ∑ j : Fin 3, RadialRieszRegularization.baseMoment 1 i j := by
  convert PeriodicRadialRiesz.moment_tensor_le (d := 3) N 1 (by decide) using 1 <;> norm_num

theorem periodic_secondMoment (N : ℕ) :
    (∫ q : T3, ‖q‖ ^ 2 * ‖PeriodicRadialRiesz.tensor N q‖) ≤
      (4 / 3 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, RadialRieszRegularization.baseMoment 2 i j := by
  convert PeriodicRadialRiesz.moment_tensor_le (d := 3) N 2 (by decide) using 1
  norm_num

example (N n : ℕ) (q : T3) (hq : q ≠ 0) (a b : R3) :
    Summable (fun z : UnitTorusLattice.LatticeSubmodule (ι := Fin 3) ↦
      RadialRieszRegularization.radialCoefficient N (EuclideanSpace.single 0 1)
        (UnitTorusSchwartzLattice.displacement q z) *
      tripleProduct a b (UnitTorusSchwartzLattice.displacement q z) *
        ⟪UnitTorusSchwartzLattice.displacement q z,
          RadialPower.radialPower n a - RadialPower.radialPower n b⟫) :=
  (PeriodicRadialRiesz.hasSum_pairedStretch_images N n (EuclideanSpace.single 0 1)
    (by simp) hq a b).summable

end Mettapedia.Analysis.RadialRieszTensorTests
