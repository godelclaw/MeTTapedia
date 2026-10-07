import GoalSystem

/-!
# Goal review as an ordinary recurring goal

Review has no separate clock, selector or acknowledgement transition. Its
purpose is supplied by the host's goal content and outcome checker, using the
same queue and protected request ledger as other work.
-/

namespace GoalReview

def goal (id interval : Nat) (baseUrgency : Nat := 0) : GoalSystem.Goal :=
  { id := id, baseUrgency := baseUrgency, recurrence := .every interval }

theorem review_is_an_ordinary_recurring_goal (id interval base : Nat) :
    goal id interval base =
      ({ id := id, baseUrgency := base, recurrence := .every interval } : GoalSystem.Goal) := by
  rfl

end GoalReview
