import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# Krenn–Gu amplitude predicates

The reusable weighted perfect-matching amplitude lives in
`Mettapedia.Combinatorics.Matching.Amplitude`.  This file retains only the
three-colour GHZ predicate and the Krenn–Gu-specific descent formulation.
-/

namespace GHZ.Configuration

open Amplitude

/-- A GHZ configuration in three colours: every monochromatic colouring has
nonvanishing amplitude, and every mixed colouring has vanishing amplitude. -/
def isGHZ {V : Type*} [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ) : Prop :=
  (∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) ∧
  (∀ c : V → Fin 3, ¬ Monochromatic c → amplitude W c = 0)

/-- Solvability on `2 * n` vertices.  `n = 2` is the exceptional four-vertex case,
which genuinely admits a solution; the conjecture concerns `n ≥ 3`. -/
def solvable (n : ℕ) : Prop := ∃ W : Sym2 (Fin (2 * n) × Fin 3) → ℂ, isGHZ W

/-- A solution on `2n` vertices, for
`n ≥ 4`, yields a solution on `2n - 2` vertices.  The bound `n ≥ 4` is essential and
not cosmetic: descent must never be allowed to terminate at the four-vertex case,
which is solvable. The step is applied to inputs of at least eight vertices
and can produce a six-vertex solution.

Together with the six-vertex obstruction this is equivalent to the conjecture:
if the conjecture holds, every premise asserting a solution is false. The
definition alone establishes neither descent nor the six-vertex obstruction. -/
def descent : Prop := ∀ n : ℕ, 4 ≤ n → solvable n → solvable (n - 1)

/-- The six-vertex obstruction. This definition does not establish it. -/
def baseSix : Prop := ¬ solvable 3

/-- **The conjecture follows from descent together with the six-vertex base case.**
Both hypotheses remain explicit. -/
theorem conjecture_of_descent (hd : descent) (hb : baseSix) :
    ∀ n : ℕ, 3 ≤ n → ¬ solvable n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h3 hs
    rcases eq_or_lt_of_le h3 with rfl | h
    · exact hb hs
    · have h4 : 4 ≤ n := h
      exact ih (n - 1) (by omega) (by omega) (hd n h4 hs)

/-- Contrapositive form: a counterexample at any vertex count above six, together
with descent, produces one at six vertices. -/
theorem six_of_descent (hd : descent) {n : ℕ} (h3 : 3 ≤ n) (hs : solvable n) :
    solvable 3 := by
  by_contra hb
  exact conjecture_of_descent hd hb n h3 hs

/-- If no solution exists at any relevant size, the descent implication is vacuous. -/
theorem descent_of_conjecture
    (h : ∀ n : ℕ, 3 ≤ n → ¬ solvable n) : descent := by
  intro n hn solution
  exact False.elim (h n (by omega) solution)

/-- The descent-and-base formulation has exactly the strength of the conjecture. -/
theorem conjecture_iff_descent_and_baseSix :
    (∀ n : ℕ, 3 ≤ n → ¬ solvable n) ↔ descent ∧ baseSix := by
  constructor
  · intro h
    exact ⟨descent_of_conjecture h, h 3 (by omega)⟩
  · rintro ⟨hd, hb⟩
    exact conjecture_of_descent hd hb

end GHZ.Configuration
