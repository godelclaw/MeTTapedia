import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Entropy and orientation costs of retained viscous memory

For the actual matrix memory `C ≥ 0`, the analytic companion argument
uses `tr C - η log det(I+C/η)`. Adding its spatial integral to kinetic
energy gives a nonnegative reserve that pays weighted source gradients
and the matrix gradient cost along complete smooth unforced histories.

This file certifies the scalar eigenvalue entropy, its derivatives, and
the separated-eigenvalue orientation coefficients. Matrix functional
calculus, the actual PDE identity, and its spatial/time integration are
analytic in `labs/viscous_memory_entropy.py` and the lab README. The
resulting spatially integrated costs do not bound arbitrary receivers
or supply an arbitrary-data continuation estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryEntropy

def entropy (η c : ℝ) : ℝ := c - η * Real.log (1 + c / η)

@[simp] theorem entropy_zero (η : ℝ) : entropy η 0 = 0 := by
  simp [entropy]

theorem entropy_bounds (η c : ℝ) (hη : 0 < η) (hc : 0 ≤ c) :
    0 ≤ entropy η c ∧ entropy η c ≤ c := by
  have harg : 0 < 1 + c / η := by positivity
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos harg) hη.le
  have he : η * (1 + c / η - 1) = c := by field_simp; ring
  rw [he] at hl
  have hp := mul_nonneg hη.le (Real.log_nonneg
    (show 1 ≤ 1 + c / η by linarith [div_nonneg hc hη.le]))
  dsimp [entropy]
  constructor <;> linarith

theorem entropy_hasDerivAt (η c : ℝ) (hη : 0 < η) (hc : 0 ≤ c) :
    HasDerivAt (entropy η) (c / (η + c)) c := by
  have harg : 0 < 1 + c / η := by positivity
  have hd : η + c ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_id c).sub
    (((((hasDerivAt_id c).div_const η).const_add 1).log harg.ne').const_mul η)
  convert! h using 1
  dsimp only [id_eq]
  field_simp
  ring

theorem slope_hasDerivAt (η c : ℝ) (hη : 0 < η) (hc : 0 ≤ c) :
    HasDerivAt (fun x : ℝ ↦ x / (η + x)) (η / (η + c) ^ 2) c := by
  have hd : η + c ≠ 0 := ne_of_gt (by positivity)
  convert! (hasDerivAt_id c).div ((hasDerivAt_id c).const_add η) hd using 1
  dsimp only [id_eq]
  ring

theorem eigen_entropy_bounds (η : ℝ) (c : Fin 3 → ℝ)
    (hη : 0 < η) (hc : ∀ i, 0 ≤ c i) :
    0 ≤ ∑ i, entropy η (c i) ∧ ∑ i, entropy η (c i) ≤ ∑ i, c i := by
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ (entropy_bounds η (c i) hη (hc i)).1)
  · exact Finset.sum_le_sum (fun i _ ↦ (entropy_bounds η (c i) hη (hc i)).2)

/-- The actual positive memory source has diagonal entries `2ν g_i`
in the memory eigenbasis. This is its exact contribution after kinetic
loss and entropy gain are combined; `η` is fixed, not sent to zero. -/
theorem source_balance (η ν c g : ℝ) (hη : 0 < η) (hc : 0 ≤ c) :
    -2 * ν * g + (c / (η + c)) * (2 * ν * g) =
      -(2 * ν * η * g / (η + c)) := by
  have hd : η + c ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- A factor-two separation of the regularized eigenvalues pays the
square of a spatial frame-connection coefficient. The factor two on
the right counts both symmetric off-diagonal matrix entries. -/
theorem spatial_turning_paid (a b r : ℝ) (hb : 0 < b) (hab : 2 * b ≤ a) :
    r ^ 2 ≤ 2 * (a - b) ^ 2 / (a * b) * r ^ 2 := by
  have ha : 0 < a := by linarith
  have hc : (1/2 : ℝ) ≤ (a - b) ^ 2 / (a * b) := by
    apply (le_div_iff₀ (mul_pos ha hb)).2
    nlinarith [mul_nonneg (show 0 ≤ 2 * a - b by linarith)
      (show 0 ≤ a - 2 * b by linarith)]
  have h := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
  calc
    r ^ 2 = 2 * ((1/2) * r ^ 2) := by ring
    _ ≤ 2 * ((a - b) ^ 2 / (a * b) * r ^ 2) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

private theorem off_diagonal_le (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : z ^ 2 ≤ x * y) : 2 * |z| ≤ x + y := by
  nlinarith [sq_abs z, sq_nonneg (x - y), abs_nonneg z]

/-- In a memory eigenbasis put `x=G_aa/a`, `y=G_bb/b` and
`z=G_ab/√(ab)`. Positivity of `G` gives `z²≤xy`. This bounds the
source-induced angular rate, not the complete material frame derivative;
the latter also has advection and diffusion contributions. -/
theorem source_turning_paid (η ν a b x y z : ℝ)
    (hη : 0 < η) (hν : 0 ≤ ν) (hb : 0 < b) (hab : 2 * b ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ^ 2 ≤ x * y) :
    2 * ν * Real.sqrt (a * b) * |z| / (a - b) ≤
      (2 * ν * η * (x + y)) / η := by
  have hg : 0 < a - b := by linarith
  have hs : Real.sqrt (a * b) ≤ 2 * (a - b) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith [mul_nonneg (show 0 ≤ 2 * a - b by linarith)
        (show 0 ≤ a - 2 * b by linarith), sq_nonneg (a - b)]
  have ho := off_diagonal_le x y z hx hy hz
  have hp : Real.sqrt (a * b) * |z| ≤ (a - b) * (x + y) := by
    calc
      _ ≤ (2 * (a - b)) * |z| := mul_le_mul_of_nonneg_right hs (abs_nonneg z)
      _ ≤ (a - b) * (x + y) := by nlinarith [mul_le_mul_of_nonneg_left ho hg.le]
  rw [show (2 * ν * η * (x + y)) / η = 2 * ν * (x + y) by field_simp]
  apply (div_le_iff₀ hg).2
  nlinarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * ν by positivity)]

end Mettapedia.FluidDynamics.NavierStokes.ViscousMemoryEntropy
