import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mathlib.Tactic.DeriveCountable

/-!
# Countability of finite Hennessy-Milner syntax

Every finite formula retains its independently supplied atom and label.
Countability follows for countable atom and label carriers, without a
branching, equation or semantic identification assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

deriving instance Countable for Formula

end Mettapedia.GSLT.HennessyMilner
