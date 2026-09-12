import Mettapedia.Analysis.PeriodicRadialRieszEvolution

/-! # Lift invariance and lattice-point checks for the differentiated kernel -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRieszEvolutionTests

open UnitTorusLattice UnitTorusPeriodization UnitTorusSchwartzLattice PeriodicRadialRiesz
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Lat" => LatticeSubmodule (ι := Fin 3)

theorem derivative_lattice_shift (N : ℕ) (z : Lat) (x : R3) :
    liftedTensorDerivative N ((z : R3) + x) = liftedTensorDerivative N x := by
  apply liftedTensorDerivative_eq_of_projection_eq
  rw [torusProjection_add, (torusProjection_eq_zero_iff_mem _).mpr z.property, zero_add]

theorem summable_tensor_images_at_origin (N : ℕ) :
    Summable (fun z : Lat ↦ RadialRieszRegularization.tensor N (z : R3)) := by
  simpa only [add_zero] using (hasSum_tensor_images_lift (d := 3) N 0).summable

theorem summable_derivative_images_at_origin (N : ℕ) (v : R3) :
    Summable (fun z : Lat ↦ RadialRieszRegularization.tensorDerivative N (z : R3) v) := by
  simpa only [add_zero] using (hasSum_tensorDerivative_images (d := 3) N 0 v).summable

theorem coincident_endpoint_rate (n : ℕ) (H Hdot : R3 →L[ℝ] R3) (a da db : R3) :
    SignedCrossKernel.pairedMaterialRate n H Hdot a a da db = 0 :=
  SignedCrossKernel.pairedMaterialRate_self n H Hdot a da db

end Mettapedia.Analysis.PeriodicRadialRieszEvolutionTests
