import Mettapedia.Analysis.PolarizedCrossKernel
import Mettapedia.Analysis.AngularCurlSourceBound

/-!
# Exact checks for polarized exchange

These are algebraic endpoint tests, not Navier--Stokes trajectories.
An anisotropic rank-one kernel retains either sign at equal endpoint
values and tests. In contrast, its isotropic part cancels exactly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PolarizedCrossKernelTests

open scoped RealInnerProductSpace
open PolarizedCrossKernel
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def endpoint : R3 := WithLp.toLp 2 ![1, 0, 0]
def transverse : R3 := WithLp.toLp 2 ![0, 0, 1]
def kernelVector : R3 := WithLp.toLp 2 ![1, 1, 0]
def anisotropicKernel : R3 →L[ℝ] R3 := InnerProductSpace.rankOne ℝ kernelVector kernelVector

theorem transverse_orthogonal : ⟪endpoint, transverse⟫ = 0 := by
  norm_num [endpoint, transverse, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem diagonal_positive : pairedTest anisotropicKernel endpoint endpoint transverse transverse = 2 := by
  rw [pairedTest_diagonal]
  norm_num [anisotropicKernel, InnerProductSpace.rankOne_apply, endpoint, transverse, kernelVector,
    EuclideanCrossProduct.cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem diagonal_negative : pairedTest anisotropicKernel endpoint endpoint (-transverse) (-transverse) = -2 := by
  rw [pairedTest_diagonal]
  norm_num [anisotropicKernel, InnerProductSpace.rankOne_apply, endpoint, transverse, kernelVector,
    EuclideanCrossProduct.cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem not_controlled_by_endpoint_increments (C : ℝ) :
    ¬ |pairedTest anisotropicKernel endpoint endpoint transverse transverse| ≤
      C * (‖endpoint - endpoint‖ + ‖transverse - transverse‖) := by
  norm_num [diagonal_positive]

theorem scalar_kernel_zero (a b f g : R3) (c : ℝ) :
    pairedTest (c • ContinuousLinearMap.id ℝ R3) a b f g = 0 :=
  pairedTest_scalar_identity a b f g c

end Mettapedia.Analysis.PolarizedCrossKernelTests
