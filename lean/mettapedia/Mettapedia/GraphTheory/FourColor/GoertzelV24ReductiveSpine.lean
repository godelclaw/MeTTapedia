import Mathlib.Order.WellFounded

/-!
# The reductive/compositional proof spine

This module states the logical architecture singled out in the source's
definition of a reductive proof.  An object has a natural-number size and an
explicit threshold.  Above the threshold, a reduction strictly decreases
size and preserves being a counterexample.  The universal target is then
equivalent to establishing the target directly at or below the threshold.

This is only the spine: it does not assert a threshold, reduction, or base
checker for planar graphs.  It also does not infer that the bounded-size class
is finite: a route-native enumeration and coverage proof must establish that
separately.  These are precisely the obligations that the corridor, pumping,
Trail Completability, and bounded-size layers must supply.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ReductiveSpine

/-- The source's reductive structure, separated from its finite base check.
`target object` is the desired property; a counterexample is `¬ target
object`. -/
structure ReductiveSystem (Object : Type*) (target : Object → Prop) where
  size : Object → Nat
  threshold : Nat
  reduce : Object → Object
  reduce_smaller :
    ∀ object, ¬ target object → threshold < size object →
      size (reduce object) < size object
  reduce_counterexample :
    ∀ object, ¬ target object → threshold < size object →
      ¬ target (reduce object)

namespace ReductiveSystem

variable {Object : Type*} {target : Object → Prop}

/-- The route's own bounded-size base claim: establish the same target
predicate for every object at or below the derived threshold.  Turning this
claim into a finite computation requires a separate coverage theorem. -/
def BaseVerified (system : ReductiveSystem Object target) : Prop :=
  ∀ object, system.size object ≤ system.threshold → target object

/-- Strict descent plus preservation of counterexamples reduces the universal
theorem to the route-native bounded-size floor. -/
theorem target_all_of_baseVerified
    (system : ReductiveSystem Object target)
    (base : system.BaseVerified) :
  ∀ object, target object := by
  intro object
  refine (measure system.size).wf.induction object ?_
  intro current ih
  by_contra hcounterexample
  by_cases hlarge : system.threshold < system.size current
  · have hsmaller :=
      system.reduce_smaller current hcounterexample hlarge
    have hcounterexample' :=
      system.reduce_counterexample current hcounterexample hlarge
    exact hcounterexample' (ih (system.reduce current) hsmaller)
  · exact hcounterexample (base current (Nat.le_of_not_gt hlarge))

/-- The universal theorem trivially verifies every member of its own base. -/
theorem baseVerified_of_target_all
    (system : ReductiveSystem Object target)
    (hall : ∀ object, target object) :
    system.BaseVerified := by
  intro object _hsmall
  exact hall object

/-- Source-facing reduction theorem: once the descent system is built, the
full universal statement is equivalent to its bounded-size base claim. -/
theorem target_all_iff_baseVerified
    (system : ReductiveSystem Object target) :
    (∀ object, target object) ↔ system.BaseVerified :=
  ⟨system.baseVerified_of_target_all,
    system.target_all_of_baseVerified⟩

end ReductiveSystem

end GoertzelV24ReductiveSpine

end Mettapedia.GraphTheory.FourColor
