; One agent-owned MeTTa space containing typed goals and evidence.
; The space itself carries no prescribed architectural role: this program
; creates it, writes atoms, and performs a variable-sharing relational query.

!(bind! &agent (new-space))

!(add-atom &agent (Goal focus))
!(add-atom &agent (NeedsEvidence focus))
!(add-atom &agent (Evidence test-receipt))
!(add-atom &agent (Supports test-receipt focus))

!(match &agent (Goal $goal) (SeenGoal $goal))

; Comma is the native shared-variable conjunction. The formal
; simultaneous-meet normalization is proved separately.
!(match &agent
  (, (Goal $goal)
     (NeedsEvidence $goal)
     (Evidence $evidence)
     (Supports $evidence $goal))
  (Actionable $goal $evidence))

!(test
  (collapse
    (match &agent
      (, (Goal $goal)
         (NeedsEvidence $goal)
         (Evidence $evidence)
         (Supports $evidence $goal))
      (Actionable $goal $evidence)))
  ((Actionable focus test-receipt)))
