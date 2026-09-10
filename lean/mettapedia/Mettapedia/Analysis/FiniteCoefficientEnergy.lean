import Mettapedia.Analysis.FiniteMultiplierLocalization
import Mettapedia.Analysis.FiniteSumEnergy
import Mathlib.Algebra.BigOperators.Fin

/-! # Algebra of finite coefficient energies -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteMultiplierLocalization

open scoped BigOperators

variable {G 𝕜 : Type*} [NormedField 𝕜]

theorem scalarEnergy_nonneg (P : Finset G) (a : G → 𝕜) : 0 ≤ scalarEnergy P a :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem scalarEnergy_add_le (P : Finset G) (a b : G → 𝕜) :
    scalarEnergy P (fun q ↦ a q + b q) ≤ 2 * scalarEnergy P a + 2 * scalarEnergy P b := by
  unfold scalarEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a q) (b q)) 2
  nlinarith only [h, sq_nonneg (‖a q‖ - ‖b q‖)]

theorem scalarEnergy_sum_le {ι : Type*} (P : Finset G) (I : Finset ι) (a : ι → G → 𝕜) :
    scalarEnergy P (fun q ↦ ∑ i ∈ I, a i q) ≤
      (I.card : ℝ) * ∑ i ∈ I, scalarEnergy P (a i) := by
  unfold scalarEnergy
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ ↦ Finset.norm_sum_sq_le_card_mul_sum_norm_sq I (fun i ↦ a i q))

theorem scalarEnergy_const_mul (P : Finset G) (a : G → 𝕜) (z : 𝕜) :
    scalarEnergy P (fun q ↦ z * a q) = ‖z‖ ^ 2 * scalarEnergy P a := by
  simp only [scalarEnergy, norm_mul, mul_pow, Finset.mul_sum]

theorem scalarEnergy_add_add_le (P : Finset G) (a b c : G → 𝕜) :
    scalarEnergy P (fun q ↦ a q + b q + c q) ≤
      3 * (scalarEnergy P a + scalarEnergy P b + scalarEnergy P c) := by
  have h := scalarEnergy_sum_le P Finset.univ (fun i : Fin 3 ↦ ![a, b, c] i)
  simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using h

end Mettapedia.Analysis.FiniteMultiplierLocalization
