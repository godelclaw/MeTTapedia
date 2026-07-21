import Mettapedia.Ethics.UtilitarianToValue
import Mettapedia.Ethics.UtilitarianToVirtue
import Mettapedia.Ethics.VirtueToValue

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u

variable {World : Type u}

/-- Coherence of the FOET triangle: the virtue-mediated path Utility -> Virtue -> Value
    equals the direct path Utility -> Value.
    This follows because UtilityAssignmentSentence.toVirtueTarget is defined as
    s.toValue.toVirtueTarget, and ValueJudgmentSentence.toVirtueTarget_toValue
    proves s.toVirtueTarget.toValue = s for any value judgment. -/
theorem utilitarian_virtue_value_coherence
    (s : UtilityAssignmentSentence World) :
    s.toVirtueTarget.toValue = s.toValue := by
  show s.toValue.toVirtueTarget.toValue = s.toValue
  exact ValueJudgmentSentence.toVirtueTarget_toValue s.toValue

end Mettapedia.Ethics