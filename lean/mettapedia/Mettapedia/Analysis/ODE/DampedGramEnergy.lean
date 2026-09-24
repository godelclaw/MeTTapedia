import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Gram energy for a family with different damping rates

The Cauchy kernel of two positive damping rates is the integral of the
product of their exponential decays. The resulting Gram energy is
nonnegative and retains all cross terms of the family. No orthogonality
or bound on the number of indices is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DampedGramEnergy

open scoped RealInnerProductSpace
open MeasureTheory

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairing (P : Finset ι) (γ : ι → ℝ) (x y : ι → E) : ℝ :=
  ∑ i ∈ P, ∑ j ∈ P, ⟪x i, y j⟫ / (γ i + γ j)

def energy (P : Finset ι) (γ : ι → ℝ) (x : ι → E) : ℝ :=
  pairing P γ x x

def decaySum (P : Finset ι) (γ : ι → ℝ) (x : ι → E) (t : ℝ) : E :=
  ∑ i ∈ P, Real.exp (-γ i * t) • x i

theorem norm_decaySum_sq (P : Finset ι) (γ : ι → ℝ) (x : ι → E) (t : ℝ) :
    ‖decaySum P γ x t‖ ^ 2 =
      ∑ i ∈ P, ∑ j ∈ P, Real.exp (-(γ i + γ j) * t) * ⟪x i, x j⟫ := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [decaySum]
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrableOn_decay_entry (γ : ι → ℝ) (x y : ι → E) (i j : ι)
    (hi : 0 < γ i) (hj : 0 < γ j) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(γ i + γ j) * t) * ⟪x i, y j⟫) (Set.Ioi 0) :=
  (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (add_pos hi hj)) 0).mul_const _

theorem integral_decay_entry (γ : ι → ℝ) (x y : ι → E) (i j : ι)
    (hi : 0 < γ i) (hj : 0 < γ j) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-(γ i + γ j) * t) * ⟪x i, y j⟫) =
      ⟪x i, y j⟫ / (γ i + γ j) := by
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr (add_pos hi hj))]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

theorem integrableOn_norm_decaySum_sq (P : Finset ι) (γ : ι → ℝ) (x : ι → E)
    (hγ : ∀ i ∈ P, 0 < γ i) :
    IntegrableOn (fun t : ℝ ↦ ‖decaySum P γ x t‖ ^ 2) (Set.Ioi 0) := by
  simp_rw [norm_decaySum_sq]
  exact integrable_finsetSum P (fun i hi ↦
    integrable_finsetSum P (fun j hj ↦ integrableOn_decay_entry γ x x i j (hγ i hi) (hγ j hj)))

theorem energy_eq_integral_norm_decaySum_sq (P : Finset ι) (γ : ι → ℝ) (x : ι → E)
    (hγ : ∀ i ∈ P, 0 < γ i) :
    energy P γ x = ∫ t : ℝ in Set.Ioi 0, ‖decaySum P γ x t‖ ^ 2 := by
  simp_rw [norm_decaySum_sq]
  rw [integral_finsetSum P (fun i hi ↦
    integrable_finsetSum P (fun j hj ↦ integrableOn_decay_entry γ x x i j (hγ i hi) (hγ j hj)))]
  unfold energy pairing
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum P (fun j hj ↦ integrableOn_decay_entry γ x x i j (hγ i hi) (hγ j hj))]
  exact Finset.sum_congr rfl (fun j hj ↦ (integral_decay_entry γ x x i j (hγ i hi) (hγ j hj)).symm)

theorem energy_nonneg (P : Finset ι) (γ : ι → ℝ) (x : ι → E)
    (hγ : ∀ i ∈ P, 0 < γ i) : 0 ≤ energy P γ x := by
  rw [energy_eq_integral_norm_decaySum_sq P γ x hγ]
  exact integral_nonneg (fun _ ↦ sq_nonneg _)

theorem pairing_symmetric (P : Finset ι) (γ : ι → ℝ) (x y : ι → E) :
    pairing P γ x y = pairing P γ y x := by
  unfold pairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm, add_comm (γ j) (γ i)]

theorem pairing_sub_left (P : Finset ι) (γ : ι → ℝ) (x y z : ι → E) :
    pairing P γ (x - y) z = pairing P γ x z - pairing P γ y z := by
  simp only [pairing, Pi.sub_apply, inner_sub_left, sub_div, Finset.sum_sub_distrib]

theorem pairing_sub_right (P : Finset ι) (γ : ι → ℝ) (x y z : ι → E) :
    pairing P γ x (y - z) = pairing P γ x y - pairing P γ x z := by
  simp only [pairing, Pi.sub_apply, inner_sub_right, sub_div, Finset.sum_sub_distrib]

/-- All pairwise damping factors cancel to the full summed inner product. -/
theorem pairing_damping_add (P : Finset ι) (γ : ι → ℝ) (x y : ι → E)
    (hγ : ∀ i ∈ P, 0 < γ i) :
    pairing P γ (fun i ↦ γ i • x i) y + pairing P γ x (fun i ↦ γ i • y i) =
      ⟪∑ i ∈ P, x i, ∑ j ∈ P, y j⟫ := by
  unfold pairing
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hn : γ i + γ j ≠ 0 := ne_of_gt (add_pos (hγ i hi) (hγ j hj))
  field_simp

end Mettapedia.Analysis.DampedGramEnergy
