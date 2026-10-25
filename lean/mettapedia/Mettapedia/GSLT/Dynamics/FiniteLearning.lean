import Mettapedia.GSLT.Dynamics.OrderedListFold
import Mettapedia.LearningTheory.FiniteClass

/-!
# Finite-learning observation traces

Candidate filtering realizes the denotational version space. A complete path
retains one event per observation and finalization, even when repeated events
leave the candidate set unchanged. Online mistake counts remain order-sensitive.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.Dynamics.FiniteLearning
open Mettapedia.LearningTheory

/-- Every complete execution computes the specified candidate set and entry count. -/
theorem complete_path {Point : Type} (hypotheses result : Finset (Point → Bool))
    (observations : List (Point × Bool))
    (path : (OrderedListFold.theory updateCandidates).RewritePath
      (.active observations hypotheses) (.done result)) :
    result = versionSpace hypotheses observations ∧ path.length = observations.length + 1 := by
  obtain ⟨value, length⟩ := OrderedListFold.complete_path updateCandidates observations hypotheses result path
  exact ⟨value.trans (foldl_updateCandidates hypotheses observations), length⟩

namespace Controls

def threeHypotheses : Finset (Bool → Bool) := {fun _ => false, id, fun _ => true}

/-- The final candidate set can agree while the online mistakes differ. -/
theorem order_changes_halving_mistakes :
    halvingMistakes id threeHypotheses [false, true] = 1 ∧
      halvingMistakes id threeHypotheses [true, false] = 0 := by decide

end Controls
end Mettapedia.GSLT.Dynamics.FiniteLearning
