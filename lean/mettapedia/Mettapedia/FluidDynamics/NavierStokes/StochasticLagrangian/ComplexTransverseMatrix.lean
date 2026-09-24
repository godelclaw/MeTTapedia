import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.Analysis.FiniteSumEnergy

/-! # Complex matrix action transverse to a real unit line -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix

open scoped BigOperators
open PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def pairing (e : R3) (v : C3) : ℂ := ∑ j : Fin 3, (e j : ℂ) * v j

def transverse (e : R3) (v : C3) : C3 := v - pairing e v • complexifyVector e

def matrixAction (A : Fin 3 → Fin 3 → ℂ) (e : R3) : C3 :=
  coefficientVec (fun i ↦ ∑ j : Fin 3, (e j : ℂ) * A i j)

theorem pairing_eq_inner (e : R3) (v : C3) : pairing e v = inner ℂ (complexifyVector e) v := by
  simp [pairing, complexifyVector, coefficientVec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_comm]

theorem norm_pairing_le (e : R3) (v : C3) (he : ‖e‖ = 1) : ‖pairing e v‖ ≤ ‖v‖ := by
  rw [pairing_eq_inner]
  simpa only [norm_complexifyVector, he, one_mul] using norm_inner_le_norm (𝕜 := ℂ) (complexifyVector e) v

theorem norm_transverse_le (e : R3) (v : C3) (he : ‖e‖ = 1) : ‖transverse e v‖ ≤ 2 * ‖v‖ := by
  have hn := norm_sub_le v (pairing e v • complexifyVector e)
  simp only [norm_smul, norm_complexifyVector, he, mul_one] at hn
  have hp := norm_pairing_le e v he
  change ‖v - pairing e v • complexifyVector e‖ ≤ _
  linarith

theorem norm_matrixAction_sq_le (A : Fin 3 → Fin 3 → ℂ) (e : R3) (he : ‖e‖ = 1) :
    ‖matrixAction A e‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖A i j‖ ^ 2 := by
  have he' : (∑ j : Fin 3, ‖(e j : ℂ)‖ ^ 2) = 1 := by
    simpa only [Complex.norm_real, EuclideanSpace.norm_sq_eq, he, one_pow] using
      (EuclideanSpace.norm_sq_eq e).symm
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  have h := Finset.norm_sum_smul_sq_le Finset.univ (fun j : Fin 3 ↦ (e j : ℂ)) (A i)
  simpa only [matrixAction, coefficientVec, PiLp.toLp_apply, smul_eq_mul, he', one_mul] using h

theorem transverse_sum {ι : Type*} (s : Finset ι) (e : R3) (v : ι → C3) :
    transverse e (∑ i ∈ s, v i) = ∑ i ∈ s, transverse e (v i) := by
  simp only [transverse, pairing, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum, Finset.sum_smul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem transverse_smul (e : R3) (a : ℂ) (v : C3) :
    transverse e (a • v) = a • transverse e v := by
  simp only [transverse, pairing, PiLp.smul_apply, smul_eq_mul, smul_sub, smul_smul]
  have h : (∑ j : Fin 3, (e j : ℂ) * (a * v j)) = a * pairing e v := by
    simp only [pairing, Finset.mul_sum]
    congr 1
    funext j
    ring
  rw [h]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.ComplexTransverseMatrix
