import Mettapedia.Analysis.AngularCurlEvolution

/-! Algebraic first-jet tests for the changing amplitude weight, not NS solutions. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlEvolutionTests

open scoped RealInnerProductSpace
open AngularCurlDecomposition WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def baseVector : R3 := WithLp.toLp 2 ![1, 0, 0]
def baseJet : Fin 3 → R3 := fun j ↦ if j = 0 then WithLp.toLp 2 ![0, 1, 0] else 0

theorem base_density : angularCurlDensity baseVector baseJet = 1 := by
  norm_num [angularCurlDensity, angularCurl, angularJet, curlJet, baseVector, baseJet,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  simp +decide

theorem growing_amplitude_rate :
    angularCurlDensityRate baseVector baseJet baseVector baseJet = 8 := by
  have h := angularCurlDensityRate_proportional baseVector baseJet 1
  simpa only [one_smul, mul_one, base_density] using h

theorem shrinking_amplitude_rate :
    angularCurlDensityRate baseVector baseJet (-baseVector) (-baseJet) = -8 := by
  have h := angularCurlDensityRate_proportional baseVector baseJet (-1)
  simpa only [neg_one_smul, Pi.neg_def, mul_neg, mul_one, base_density] using h

end Mettapedia.Analysis.AngularCurlEvolutionTests
