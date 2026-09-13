import Mettapedia.Analysis.AngularCurlCurvatureBound

/-!
# Compatible divergence-free jets with both angular curvature signs

These are local second-jet algebra tests, not asserted periodic NS
trajectories. Symmetry and the differentiated divergence constraint are
checked explicitly. The curvature cannot simply be discarded by sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.AngularCurlCurvatureTests

open scoped RealInnerProductSpace
open AngularCurlDecomposition WeightedCurlCancellation
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def value : R3 := WithLp.toLp 2 ![1, 0, 0]
def first : Fin 3 → R3 := ![WithLp.toLp 2 ![0, 1, 0], WithLp.toLp 2 ![1, 0, 0], 0]
def second (c : ℝ) : Fin 3 → Fin 3 → R3 :=
  ![![WithLp.toLp 2 ![c, 0, 0], WithLp.toLp 2 ![0, -c, 0], 0],
    ![WithLp.toLp 2 ![0, -c, 0], 0, 0], ![0, 0, 0]]

theorem first_divergence : (∑ j : Fin 3, first j j) = 0 := by
  norm_num [first, Fin.sum_univ_three, Matrix.cons_val_two]

theorem second_symmetric (c : ℝ) (j k : Fin 3) : second c j k = second c k j := by
  fin_cases j <;> fin_cases k <;> rfl

theorem second_divergence (c : ℝ) (k : Fin 3) : (∑ j : Fin 3, second c k j j) = 0 := by
  fin_cases k <;> simp [second, Fin.sum_univ_three]

theorem curvature_trace (c : ℝ) :
    (∑ k : Fin 3, angularCurlDensitySecondVariation value first (first k) (second c k)) =
      2 * c ^ 2 - 32 * c + 28 := by
  simp [angularCurlDensitySecondVariation, angularCurlSecondVariation, angularJetSecondVariation,
    angularCurlRate, angularJetRate, angularCurl, angularJet, curlJet, value, first, second,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  ring

theorem positive_curvature :
    (∑ k : Fin 3, angularCurlDensitySecondVariation value first (first k) (second 0 k)) = 28 := by
  norm_num [curvature_trace]

theorem negative_curvature :
    (∑ k : Fin 3, angularCurlDensitySecondVariation value first (first k) (second 6 k)) = -92 := by
  norm_num [curvature_trace]

end Mettapedia.Analysis.AngularCurlCurvatureTests
