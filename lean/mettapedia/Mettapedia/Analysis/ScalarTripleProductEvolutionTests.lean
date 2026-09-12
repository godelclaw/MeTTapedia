import Mettapedia.Analysis.ScalarTripleProductEvolution
import Mettapedia.Analysis.WeightedCrossProductTests
import Mettapedia.Analysis.RadialRieszMoments

/-!
# Separation cancellation and its scope

The tests distinguish conservation of the scalar triple product from
growth of the old weighted cross-product norm. The radial kernel test
also retains coplanarity even when the endpoint vectors are not parallel.
These finite-dimensional tests are not spatial NS solutions.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.ScalarTripleProductEvolutionTests

open EuclideanCrossProduct WeightedCrossProductTests
open scoped RealInnerProductSpace FourierTransform
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def normal : R3 := WithLp.toLp 2 ![0, 0, 1]

theorem tripleProduct_value : tripleProduct leftVector rightVector normal = 1 := by
  have hc : cross leftVector rightVector = normal := by
    ext i
    fin_cases i <;> norm_num [cross, cross_apply, leftVector, rightVector, normal, Matrix.cons_val_two]
  rw [tripleProduct, hc, real_inner_self_eq_norm_sq]
  norm_num [normal, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]

theorem tripleRate_value :
    tripleRate leftVector rightVector normal
      (strain leftVector) (strain rightVector) (strain normal) = 0 := by
  simpa only [strain, LinearMap.coe_toContinuousLinearMap', strainMatrix_trace, zero_mul] using
    tripleRate_common strainMatrix leftVector rightVector normal

theorem conserved_tripleProduct_firstVariation :
    HasDerivAt (fun t : ℝ ↦ tripleProduct
      (leftVector + t • strain leftVector) (rightVector + t • strain rightVector)
      (normal + t • strain normal)) 0 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).smul_const (strain leftVector)).const_add leftVector
  have hb := ((hasDerivAt_id (0 : ℝ)).smul_const (strain rightVector)).const_add rightVector
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const (strain normal)).const_add normal
  simpa only [id_eq, zero_smul, one_smul, add_zero, tripleRate_value] using
    hasDerivAt_tripleProduct ha hb hh

theorem triple_cancellation_is_not_weighted_damping :
    tripleRate leftVector rightVector normal (strain leftVector) (strain rightVector) (strain normal) = 0 ∧
      WeightedCrossProduct.rate 2 leftVector rightVector (strain leftVector) (strain rightVector) = 48 :=
  ⟨tripleRate_value, energy_rate⟩

theorem coplanar_radial_depletion (n : ℕ) (c d : ℝ) :
    SignedCrossKernel.pairedStretch n (radialOperator c d leftVector) leftVector rightVector = 0 ∧
      ‖cross leftVector rightVector‖ ^ 2 = 1 := by
  refine ⟨?_, cross_norm_sq⟩
  rw [pairedStretch_radialOperator]
  have hz : tripleProduct leftVector rightVector leftVector = 0 :=
    (real_inner_comm _ _).trans (inner_self_cross _ _)
  simp only [hz, mul_zero, zero_mul]

example (N : ℕ) (A : R3 ≃ₗᵢ[ℝ] R3) (x : R3) :
    RadialRieszRegularization.potential N (A x) = RadialRieszRegularization.potential N x :=
  RadialRieszRegularization.potential_isometry N A x

example (i j : Fin 3) (x : R3) (hx : 1 ≤ ‖x‖) :
    Filter.Tendsto (fun N : ℕ ↦ (𝓕 (RadialRieszRegularization.kernel N i j)) x)
      Filter.atTop (nhds (AnnularRieszKernel.rieszEntry i j x : ℂ)) := by
  simp only [RadialRieszRegularization.fourier_kernel_apply]
  simpa only [one_mul, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((RadialRieszRegularization.tendsto_weight x hx).mul_const (AnnularRieszKernel.rieszEntry i j x))

end Mettapedia.Analysis.ScalarTripleProductEvolutionTests
