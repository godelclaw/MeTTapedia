import Mettapedia.Analysis.AngularCurlVariation
import Mettapedia.Analysis.AngularCurlEvolutionTests

/-! Exact value/jet response tests; these local jets are not NS trajectories. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlVariationTests

open scoped RealInnerProductSpace
open AngularCurlDecomposition AngularCurlEvolutionTests WeightedCurlCancellation EuclideanCrossProduct

theorem value_response : ⟪valueGradient baseVector baseJet, baseVector⟫ = 6 := by
  norm_num [valueGradient, angularCurl, angularJet, curlJet, amplitudeGradient,
    baseVector, baseJet, cross, cross_apply, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  simp +decide
  norm_num

theorem jet_response : (∑ j : Fin 3, ⟪jetGradient baseVector baseJet j, baseJet j⟫) = 2 := by
  have h := gradient_pairing_self baseVector baseJet
  rw [value_response, base_density] at h
  linarith only [h]

theorem full_response : ⟪valueGradient baseVector baseJet, baseVector⟫ +
    (∑ j : Fin 3, ⟪jetGradient baseVector baseJet j, baseJet j⟫) = 8 := by
  rw [value_response, jet_response]
  norm_num

end Mettapedia.Analysis.AngularCurlVariationTests
