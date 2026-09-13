import Mettapedia.Analysis.RegularizedProjectionParabolic
import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Sharpness and curl-compatible negative curvature

The finite jet below has zero divergence and its curl is the second input
to the projection. It is an algebraic jet, not a constructed Navier–Stokes
solution. These constraints alone do not make the projection Hessian positive.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RegularizedProjectionParabolicTests

open scoped RealInnerProductSpace
open RegularizedProjectionParabolic WeightedCurlCancellation

theorem negative_curvature : energyCurvature 1 (0 : ℝ) 1 1 0 = -2 := by
  norm_num [energyCurvature, coefficientRate, RegularizedProjection.coefficient,
    RCLike.inner_apply]

theorem lower_bound_attained :
    energyCurvature 1 (0 : ℝ) 1 1 0 =
      -(2 / (1 : ℝ)) * ⟪RegularizedProjection.residual 1 (0 : ℝ) 1, (1 : ℝ)⟫ ^ 2 := by
  norm_num [negative_curvature, RegularizedProjection.residual,
    RegularizedProjection.coefficient, RCLike.inner_apply]

theorem positive_curvature : energyCurvature 1 (0 : ℝ) 0 0 1 = 2 := by
  norm_num [energyCurvature, coefficientRate, RegularizedProjection.coefficient,
    RCLike.inner_apply]

theorem negative_curvature_parameter (δ : ℝ) (hδ : 0 < δ) :
    energyCurvature δ (0 : ℝ) 1 1 0 = -2 / δ := by
  have hd := hδ.ne'
  norm_num [energyCurvature, coefficientRate, RegularizedProjection.coefficient,
    RCLike.inner_apply]
  field_simp

/-- A bound uniform in positive regularization cannot hold for the bare
projection Hessian, even with these four fixed scalar inputs. -/
theorem no_uniform_curvature_lower_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ energyCurvature δ (0 : ℝ) 1 1 0 < -C := by
  have hpos : 0 < C + 1 := by positivity
  refine ⟨1 / (C + 1), by positivity, ?_, ?_⟩
  · exact (div_le_one hpos).mpr (by linarith)
  · rw [negative_curvature_parameter _ (by positivity)]
    field_simp
    linarith

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def incompressibleJet : Fin 3 → R3 :=
  ![WithLp.toLp 2 ![1, 1, 0], WithLp.toLp 2 ![0, -1, 1], 0]

theorem incompressibleJet_trace : (∑ j : Fin 3, incompressibleJet j j) = 0 := by
  norm_num [incompressibleJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem incompressibleJet_curl :
    curlJet incompressibleJet = WithLp.toLp 2 ![(1 : ℝ), 0, 1] := by
  ext i
  fin_cases i <;> norm_num [curlJet, incompressibleJet, Matrix.cons_val_two]

theorem curl_compatible_negative_curvature :
    (∑ j : Fin 3, energyCurvature 1 (0 : R3) (curlJet incompressibleJet)
      (incompressibleJet j) 0) = -4 := by
  rw [incompressibleJet_curl]
  norm_num [energyCurvature, coefficientRate, RegularizedProjection.coefficient,
    incompressibleJet, Fin.sum_univ_three, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Matrix.cons_val_two]

end Mettapedia.Analysis.RegularizedProjectionParabolicTests
