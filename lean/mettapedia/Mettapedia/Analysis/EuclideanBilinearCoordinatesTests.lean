import Mettapedia.Analysis.SchwartzBilinearKernel

/-! Phase, coordinate separation, and reconstruction regressions for bilinear kernels. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.EuclideanBilinearCoordinatesTests

open EuclideanBilinearCoordinates SchwartzBilinearKernel
open scoped FourierTransform SchwartzMap

local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

/-- This is bilinear, not conjugate-linear in either argument. -/
example : elementary (𝕜 := ℂ) (0 : Fin 3) (0 : Fin 3) (0 : Fin 3)
    (EuclideanSpace.single 0 Complex.I) (EuclideanSpace.single 0 Complex.I) =
      -EuclideanSpace.single 0 (1 : ℂ) := by simp [elementary_apply]

/-- The two input coordinates are selected independently. -/
example : elementary (𝕜 := ℂ) (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
    (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) = 0 := by simp

example (B : Op) : reconstruct (entry B) = B := reconstruct_entry B

/-- Fourier transformation preserves arbitrary complex matrix entries. -/
example (s : Fin 3 → Fin 3 → Fin 3 → 𝓢(E6, ℂ)) (ξ : E6) :
    (𝓕 (assemble s)) ξ = reconstruct (fun i j l ↦ (𝓕 (s i j l)) ξ) :=
  fourier_assemble s ξ

end Mettapedia.Analysis.EuclideanBilinearCoordinatesTests

#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.norm_elementaryLinear_le
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.elementary_apply
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.norm_elementary_le
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.sum_coordinates
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.ext_basis
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.reconstruct_apply_basis
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.reconstruct_entry
#print axioms Mettapedia.Analysis.EuclideanBilinearCoordinates.norm_reconstruct_le
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.lift_apply
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.fourier_lift
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.assemble_apply
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.fourier_assemble
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.norm_assemble_le
#print axioms Mettapedia.Analysis.SchwartzBilinearKernel.moment_assemble_le
