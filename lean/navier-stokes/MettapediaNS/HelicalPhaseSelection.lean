import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Angular and axial phase counts for two helical parents

A positive parent has phase label `(m, 1)` and its conjugate has label
`(-m, -1)`. These finite arithmetic results count the labels of products.
For angular indices 2 and 4, a nonzero axial mean is possible at order
three. For indices 6 and 8, it is impossible before order seven.

The application to amplitude derivatives of the Navier--Stokes evolution
is analytic: the base preserves phase labels and quadratic interactions
add them. This module certifies the counting statement, not that PDE
application, any estimate on an evolution, or a regularity theorem.
-/

namespace Mettapedia.FluidDynamics.NavierStokes.HelicalPhaseSelection

/-- Multiplicities of the two parents and their complex conjugates. -/
structure ParentCounts where
  firstPos : ℕ
  firstNeg : ℕ
  secondPos : ℕ
  secondNeg : ℕ

namespace ParentCounts

/-- Total number of factors. -/
def order (c : ParentCounts) : ℕ :=
  c.firstPos + c.firstNeg + c.secondPos + c.secondNeg

/-- Angular index of the product. -/
def angular (m n : ℤ) (c : ParentCounts) : ℤ :=
  m * ((c.firstPos : ℤ) - c.firstNeg) +
    n * ((c.secondPos : ℤ) - c.secondNeg)

/-- Axial index, with each positive parent having index one. -/
def axial (c : ParentCounts) : ℤ :=
  (c.firstPos : ℤ) - c.firstNeg + c.secondPos - c.secondNeg

/-- Adjacent positive even angular indices can delay the first fast mean
to arbitrarily high order. The bound counts factors; it does not assert
that the corresponding interaction coefficient is nonzero. -/
theorem minimum_order_adjacent (k : ℕ) (c : ParentCounts)
    (hang : c.angular (2 * (k : ℤ)) (2 * ((k : ℤ) + 1)) = 0)
    (hax : c.axial ≠ 0) : 2 * k + 1 ≤ c.order := by
  let x : ℤ := (c.firstPos : ℤ) - c.firstNeg
  let y : ℤ := (c.secondPos : ℤ) - c.secondNeg
  have hk : (0 : ℤ) ≤ k := by positivity
  have hkp : (0 : ℤ) ≤ (k : ℤ) + 1 := by omega
  have hh : 2 * (k : ℤ) * x + 2 * ((k : ℤ) + 1) * y = 0 := hang
  have hx : x = ((k : ℤ) + 1) * (x + y) := by nlinarith [hh]
  have hy : y = -(k : ℤ) * (x + y) := by nlinarith [hh]
  have hn : x + y ≠ 0 := by
    intro h
    apply hax
    dsimp [x, y] at h
    simp only [axial]
    omega
  have hpos : (0 : ℤ) < |x + y| := abs_pos.mpr hn
  have hone : (1 : ℤ) ≤ |x + y| := by omega
  have hsum : |x| + |y| = (2 * (k : ℤ) + 1) * |x + y| := by
    calc
      |x| + |y| = |((k : ℤ) + 1) * (x + y)| + |-(k : ℤ) * (x + y)| :=
        congrArg₂ (fun p q : ℤ ↦ |p| + |q|) hx hy
      _ = (2 * (k : ℤ) + 1) * |x + y| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hk, abs_of_nonneg hkp]
        ring
  have hxb : |x| ≤ (c.firstPos : ℤ) + c.firstNeg := by
    rw [abs_le]
    dsimp [x]
    constructor <;> omega
  have hyb : |y| ≤ (c.secondPos : ℤ) + c.secondNeg := by
    rw [abs_le]
    dsimp [y]
    constructor <;> omega
  have horder : |x| + |y| ≤ (c.order : ℤ) := by
    simp only [order, Nat.cast_add]
    omega
  have hmul := mul_le_mul_of_nonneg_left hone (show (0 : ℤ) ≤ 2 * k + 1 by omega)
  have hmain : 2 * (k : ℤ) + 1 ≤ (c.order : ℤ) := by
    rw [hsum] at horder
    nlinarith [hmul]
  exact_mod_cast hmain

theorem minimum_order_two_four (c : ParentCounts)
    (hang : c.angular 2 4 = 0) (hax : c.axial ≠ 0) : 3 ≤ c.order := by
  simp only [angular, axial, order] at *
  omega

theorem minimum_order_six_eight (c : ParentCounts)
    (hang : c.angular 6 8 = 0) (hax : c.axial ≠ 0) : 7 ≤ c.order := by
  simp only [angular, axial, order] at *
  omega

theorem axial_zero_before_seven (c : ParentCounts)
    (hang : c.angular 6 8 = 0) (horder : c.order ≤ 6) : c.axial = 0 := by
  by_contra h
  have := minimum_order_six_eight c hang h
  omega

/-- The first possible fast mean for the `(2,1),(4,1)` pair. -/
def cubicWitness : ParentCounts := ⟨2, 0, 0, 1⟩

theorem cubicWitness_indices :
    cubicWitness.order = 3 ∧ cubicWitness.angular 2 4 = 0 ∧
      cubicWitness.axial = 1 := by
  norm_num [cubicWitness, order, angular, axial]

/-- The first possible fast mean for the `(6,1),(8,1)` pair. -/
def seventhOrderWitness : ParentCounts := ⟨4, 0, 0, 3⟩

theorem seventhOrderWitness_indices :
    seventhOrderWitness.order = 7 ∧ seventhOrderWitness.angular 6 8 = 0 ∧
      seventhOrderWitness.axial = 1 := by
  norm_num [seventhOrderWitness, order, angular, axial]

end ParentCounts

end Mettapedia.FluidDynamics.NavierStokes.HelicalPhaseSelection
