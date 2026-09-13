import Mettapedia.Analysis.AngularCurlSkewDeformation
import Mettapedia.Analysis.AngularCurlEvolutionTests

/-! Exact rotational-work signs on divergence-free local first jets.
These are algebraic tests, not constructed global NS trajectories. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlSkewDeformationTests

open scoped RealInnerProductSpace
open AngularCurlDecomposition AngularCurlEvolutionTests WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def helicityJet (b : ℝ) : Fin 3 → R3 :=
  ![WithLp.toLp 2 ![1, 0, 0], WithLp.toLp 2 ![0, -1, b], 0]

theorem helicityJet_divergence (b : ℝ) : (∑ j : Fin 3, helicityJet b j j) = 0 := by
  norm_num [helicityJet, Fin.sum_univ_three, Matrix.cons_val_two]

theorem helicity_response (b : ℝ) : longitudinalHelicityDensity baseVector (helicityJet b) = b := by
  norm_num [longitudinalHelicityDensity, baseVector, helicityJet, angularCurl, angularJet,
    curlJet, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem rotational_response (b : ℝ) :
    deformationWork baseVector (helicityJet b) (skewDeformation baseVector) = -b := by
  rw [deformationWork_skew_eq_neg_helicity _ _ (helicityJet_divergence b), helicity_response]

theorem positive_rotational_work :
    deformationWork baseVector (helicityJet (-1)) (skewDeformation baseVector) = 1 := by
  rw [rotational_response]
  norm_num

theorem negative_rotational_work :
    deformationWork baseVector (helicityJet 1) (skewDeformation baseVector) = -1 := by
  rw [rotational_response]

end Mettapedia.Analysis.AngularCurlSkewDeformationTests
