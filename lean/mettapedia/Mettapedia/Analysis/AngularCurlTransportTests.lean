import Mettapedia.Analysis.AngularCurlRadialVariation
import Mettapedia.Analysis.AngularCurlTransportBound
import Mettapedia.Analysis.AngularCurlVariationTests

/-! Exact local-jet tests for transport signs and radial cancellation.
These tests do not assert that the jets form a global NS trajectory. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlTransportTests

open scoped RealInnerProductSpace
open AngularCurlDecomposition AngularCurlEvolutionTests WeightedCurlCancellation EuclideanCrossProduct

def diagonalDeformation (c : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![c, 0, 0], ![0, -c, 0], ![0, 0, 0]]

theorem diagonalDeformation_trace (c : ℝ) :
    (∑ j : Fin 3, diagonalDeformation c j j) = 0 := by
  simp [diagonalDeformation, Fin.sum_univ_three]

theorem deformation_response (c : ℝ) :
    deformationWork baseVector baseJet (diagonalDeformation c) = 2 * c := by
  norm_num [deformationWork, deformationStress_eq_angularJet, curlJetAdjoint,
    angularCurl, angularJet, curlJet, baseVector, baseJet, diagonalDeformation,
    cross, cross_apply, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem positive_deformation :
    deformationWork baseVector baseJet (diagonalDeformation 1) = 2 := by
  rw [deformation_response, mul_one]

theorem negative_deformation :
    deformationWork baseVector baseJet (diagonalDeformation (-1)) = -2 := by
  rw [deformation_response]
  norm_num

theorem pointwise_radial_response (E : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    ⟪variationalGradient baseVector baseJet E, baseVector⟫ = 8 := by
  rw [inner_variationalGradient_value, base_density, mul_one]

theorem radial_perturbation_response (c : Fin 3 → ℝ) (b : ℝ) :
    deformationWork baseVector (fun j ↦ baseJet j + c j • baseVector) (diagonalDeformation b) = 2 * b := by
  rw [deformationWork_add_radial, deformation_response]

end Mettapedia.Analysis.AngularCurlTransportTests
