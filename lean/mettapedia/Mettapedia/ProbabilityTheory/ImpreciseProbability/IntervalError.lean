import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute error under interval uncertainty

These results depend only on a real interval. They apply to probability
queries, frequencies, and other scalar observations without identifying their
interpretations. The midpoint is optimal for worst-case absolute error;
no distribution on the unknown value is presumed.
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError

/-- The largest error a point estimate can have on an interval. -/
noncomputable def intervalErrorRadius (lower upper estimate : ℝ) : ℝ :=
  max |lower - estimate| |upper - estimate|

/-- The interval midpoint has worst-case absolute error equal to half its width. -/
theorem intervalErrorRadius_midpoint {lower upper : ℝ} (ordered : lower ≤ upper) :
    intervalErrorRadius lower upper ((lower + upper) / 2) = (upper - lower) / 2 := by
  unfold intervalErrorRadius
  rw [abs_of_nonpos (show lower - (lower + upper) / 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ upper - (lower + upper) / 2 by linarith)]
  have equal : -(lower - (lower + upper) / 2) = upper - (lower + upper) / 2 := by ring
  rw [equal, max_self]
  ring

/-- No point estimate has a smaller worst-case absolute error over the same
interval. This is a minimax statement, not a Bayesian-risk claim. -/
theorem half_width_le_intervalErrorRadius (lower upper estimate : ℝ) :
    (upper - lower) / 2 ≤ intervalErrorRadius lower upper estimate := by
  have triangle := abs_sub_le upper estimate lower
  have signed := le_abs_self (upper - lower)
  have first := le_max_left |lower - estimate| |upper - estimate|
  have second := le_max_right |lower - estimate| |upper - estimate|
  rw [abs_sub_comm estimate lower] at triangle
  unfold intervalErrorRadius
  linarith

theorem midpoint_minimax {lower upper : ℝ} (ordered : lower ≤ upper) (estimate : ℝ) :
    intervalErrorRadius lower upper ((lower + upper) / 2) ≤
      intervalErrorRadius lower upper estimate := by
  rw [intervalErrorRadius_midpoint ordered]
  exact half_width_le_intervalErrorRadius lower upper estimate

theorem error_le_intervalErrorRadius {lower upper actual estimate : ℝ}
    (contains : actual ∈ Set.Icc lower upper) :
    |actual - estimate| ≤ intervalErrorRadius lower upper estimate := by
  rw [abs_le]
  have lowerAbs := neg_abs_le (lower - estimate)
  have upperAbs := le_abs_self (upper - estimate)
  have lowerMax := le_max_left |lower - estimate| |upper - estimate|
  have upperMax := le_max_right |lower - estimate| |upper - estimate|
  unfold intervalErrorRadius
  constructor <;> linarith [contains.1, contains.2]

end Mettapedia.ProbabilityTheory.ImpreciseProbability.IntervalError
