import Mathlib

/-!
The algebraic connector behind the C6 non-collapse split.

At a vertex and a fixed colour, the two one-defect equations form a two by
two linear system in the two adjacent deflated amplitudes.  Multiplying by
the adjugate shows that each determinant times each amplitude is zero.
Over a domain, every slot therefore has a genuine dichotomy: either its
determinant collapses or the corresponding deflated amplitude is killed.

This is deliberately generic.  The frozen C6 generator identities instantiate
these lemmas eighteen times; the all-collapse branch uses the left disjunct,
while the non-collapse branches must account for the right disjunct.
-/

namespace Krenn.AdjugateDichotomy

section CommRing

variable {R : Type*} [CommRing R]

/-- The first coordinate of a two-by-two system after multiplication by the
adjugate. -/
theorem left_adjugate_identity
    (a₁ b₁ a₂ b₂ p q l₁ l₂ : R)
    (h₁ : l₁ = a₁ * p + b₁ * q)
    (h₂ : l₂ = a₂ * p + b₂ * q) :
    (a₁ * b₂ - a₂ * b₁) * p = b₂ * l₁ - b₁ * l₂ := by
  rw [h₁, h₂]
  ring

/-- The second coordinate of a two-by-two system after multiplication by the
adjugate. -/
theorem right_adjugate_identity
    (a₁ b₁ a₂ b₂ p q l₁ l₂ : R)
    (h₁ : l₁ = a₁ * p + b₁ * q)
    (h₂ : l₂ = a₂ * p + b₂ * q) :
    (a₁ * b₂ - a₂ * b₁) * q = a₁ * l₂ - a₂ * l₁ := by
  rw [h₁, h₂]
  ring

end CommRing

section Domain

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- If both one-defect equations vanish, the first deflated amplitude is
killed unless the associated determinant collapses. -/
theorem left_kill_or_collapse
    (a₁ b₁ a₂ b₂ p q : R)
    (h₁ : a₁ * p + b₁ * q = 0)
    (h₂ : a₂ * p + b₂ * q = 0) :
    a₁ * b₂ - a₂ * b₁ = 0 ∨ p = 0 := by
  have product_zero : (a₁ * b₂ - a₂ * b₁) * p = 0 := by
    rw [left_adjugate_identity a₁ b₁ a₂ b₂ p q
      (a₁ * p + b₁ * q) (a₂ * p + b₂ * q) rfl rfl]
    simp [h₁, h₂]
  exact mul_eq_zero.mp product_zero

/-- If both one-defect equations vanish, the second deflated amplitude is
killed unless the associated determinant collapses. -/
theorem right_kill_or_collapse
    (a₁ b₁ a₂ b₂ p q : R)
    (h₁ : a₁ * p + b₁ * q = 0)
    (h₂ : a₂ * p + b₂ * q = 0) :
    a₁ * b₂ - a₂ * b₁ = 0 ∨ q = 0 := by
  have product_zero : (a₁ * b₂ - a₂ * b₁) * q = 0 := by
    rw [right_adjugate_identity a₁ b₁ a₂ b₂ p q
      (a₁ * p + b₁ * q) (a₂ * p + b₂ * q) rfl rfl]
    simp [h₁, h₂]
  exact mul_eq_zero.mp product_zero

end Domain

/-- A finite collection of slot dichotomies is globally either all-collapse
or has a concrete kill branch.  This is the exact branching point needed by
the C6 proof; it does not claim that the kill branch is already refuted. -/
theorem all_collapse_or_exists_kill {α ι : Type*} [Zero α]
    (determinant kill : ι → α)
    (slot : ∀ i, determinant i = 0 ∨ kill i = 0) :
    (∀ i, determinant i = 0) ∨ ∃ i, kill i = 0 := by
  classical
  by_cases existsKill : ∃ i, kill i = 0
  · exact Or.inr existsKill
  · left
    intro i
    rcases slot i with hdet | hkill
    · exact hdet
    · exact (existsKill ⟨i, hkill⟩).elim

end Krenn.AdjugateDichotomy

#print axioms Krenn.AdjugateDichotomy.left_kill_or_collapse
#print axioms Krenn.AdjugateDichotomy.right_kill_or_collapse
#print axioms Krenn.AdjugateDichotomy.all_collapse_or_exists_kill
