import Mettapedia.Analysis.EuclideanCrossProduct
import Mettapedia.Analysis.WeightedCurlCancellation

/-!
# Strain and rotation in the curl-vorticity source

The velocity gradient is represented by its component-gradient rows.
Its skew part contributes an amplitude gradient, minus the vorticity
times its divergence. The latter vanishes for a solenoidal vorticity jet.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.VorticityJetSource

open scoped RealInnerProductSpace
open EuclideanCrossProduct
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def strainRows (G : Fin 3 → R3) (m : Fin 3) : R3 :=
  WithLp.toLp 2 (fun j ↦ (G m j + G j m) / 2)

def axialVector (G : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 ![G 2 1 - G 1 2, G 0 2 - G 2 0, G 1 0 - G 0 1]

def source (G D : Fin 3 → R3) : R3 :=
  -(2 • (∑ m : Fin 3, cross (G m) (D m)))

def amplitudeGradient (a : R3) (D : Fin 3 → R3) : R3 :=
  WithLp.toLp 2 (fun j ↦ ⟪a, D j⟫)

theorem source_eq_strain_add_rotation (G D : Fin 3 → R3) :
    source G D = source (strainRows G) D + amplitudeGradient (axialVector G) D -
      (∑ j : Fin 3, D j j) • axialVector G := by
  ext i
  fin_cases i <;>
    simp [source, strainRows, axialVector, amplitudeGradient, cross, cross_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two] <;> ring

theorem source_eq_strain_add_amplitudeGradient (G D : Fin 3 → R3)
    (hD : ∑ j : Fin 3, D j j = 0) :
    source G D = source (strainRows G) D + amplitudeGradient (axialVector G) D := by
  rw [source_eq_strain_add_rotation G D, hD, zero_smul, sub_zero]

theorem inner_amplitudeGradient (a b : R3) (D : Fin 3 → R3) :
    ⟪b, amplitudeGradient a D⟫ = ∑ j : Fin 3, b j * ⟪a, D j⟫ := by
  simp [amplitudeGradient, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

end Mettapedia.Analysis.VorticityJetSource
