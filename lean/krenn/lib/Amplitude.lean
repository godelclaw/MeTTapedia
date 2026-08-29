import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# Krenn–Gu amplitude predicates

The reusable weighted perfect-matching amplitude lives in
`Mettapedia.Combinatorics.Matching.Amplitude`.  This file retains only the
three-colour GHZ predicate and the Krenn–Gu-specific descent formulation.
-/

namespace KrennGu

open Amplitude

/-- A GHZ configuration in three colours: every monochromatic colouring has
nonvanishing amplitude, and every mixed colouring has vanishing amplitude. -/
def IsGHZ {V : Type*} [Fintype V] [DecidableEq V] (W : Sym2 (V × Fin 3) → ℂ) : Prop :=
  (∀ k : Fin 3, amplitude W (Amplitude.const (V := V) k) ≠ 0) ∧
  (∀ c : V → Fin 3, ¬ Monochromatic c → amplitude W c = 0)

/-- Solvability on `2 * n` vertices.  `n = 2` is the exceptional four-vertex case,
which genuinely admits a solution; the conjecture concerns `n ≥ 3`. -/
def Solvable (n : ℕ) : Prop := ∃ W : Sym2 (Fin (2 * n) × Fin 3) → ℂ, IsGHZ W

/-- **One sufficient route, not the conjecture.**  A solution on `2n` vertices, for
`n ≥ 4`, yields a solution on `2n - 2` vertices.  The bound `n ≥ 4` is essential and
not cosmetic: descent must never be allowed to terminate at the four-vertex case,
which is solvable, so the step is only ever taken from six vertices upward.

This is *stronger* than the conjecture needs and may well be false even if the
conjecture is true.  The conjecture asks only that no counterexample exist at all;
this asks that *every* solution descend, including ones a proof would never have to
meet.  It is recorded because it is a clean sufficient condition, not because it is
the target. -/
def Descent : Prop := ∀ n : ℕ, 4 ≤ n → Solvable n → Solvable (n - 1)

/-- The six-vertex base case: the statement proved for `N = 6, D = 3`. -/
def BaseSix : Prop := ¬ Solvable 3

/-- **The conjecture follows from descent together with the six-vertex base case.**
A sufficient route, not a reduction of the problem to its difficulty: see the
warning on `Descent`. -/
theorem conjecture_of_descent (hd : Descent) (hb : BaseSix) :
    ∀ n : ℕ, 3 ≤ n → ¬ Solvable n := by
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
theorem six_of_descent (hd : Descent) {n : ℕ} (h3 : 3 ≤ n) (hs : Solvable n) :
    Solvable 3 := by
  by_contra hb
  exact conjecture_of_descent hd hb n h3 hs

end KrennGu
