import Mettapedia.Languages.MeTTa.Experimental.NoValueCBPV
import Mettapedia.TypeTheory.ContextualCBPVZero

/-!
# Zero answers realized: `(empty)` over MeTTa atoms

`NoValueCBPV` places zero answers as an observation field: a run with no
outcome. With the nullary choice (`ContextualCBPVZero`) that run is now the
observation of an actual computation, `(empty)`, over the MeTTa signature
extended by the reserved kind (`zero_answers_realized`). Every runtime
encoding of the zoo's answer kinds is therefore an observed run: zero
answers, the raised error and the raised inert call
(`runtime_encodings_realized` and this file).

The other answer kinds stay values, and an empty observation is never a
value's: `(empty)` differs from returning the unit datum `()`
(`empty_not_unit`), the confusion the zoo's `reify_nil` warns about.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.NoValueCBPV

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Experimental.NoValueZoo
open Mettapedia.TypeTheory.ContextualCBPV
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-- The answers of a closed returner of the extended MeTTa signature, through
the nullary-choice observer, from the same fixed state as `outcomes`. -/
def outcomesZ (code : Comp (withZero mettaSig) [] (.ret atomT)) : List Outcome :=
  (ProgramZ.runWorldsAt code.observedZ (sym "state") []).map WorldResult.answer

/-- `(empty)` over atoms; its payload is never observed. -/
def emptyAtomComputation : Comp (withZero mettaSig) [] (.ret atomT) :=
  emptyC (sig := mettaSig) (sym "none")

theorem empty_outcomes : outcomesZ emptyAtomComputation = [] := rfl

/-- **The zoo's zero answers is the observation of `(empty)`.** -/
theorem zero_answers_realized :
    encode .zeroAnswers = .run (lookupCall (sym "k2")) (outcomesZ emptyAtomComputation) := rfl

/-- `(empty)` is not the unit datum: zero answers versus one answer `()`. -/
theorem empty_not_unit :
    outcomesZ emptyAtomComputation ≠
      outcomesZ (.ret (.const (sig := withZero mettaSig) Ground.atom unitAtom)) := by
  change ([] : List Outcome) ≠ [.inl unitAtom]
  simp

#print axioms zero_answers_realized
#print axioms empty_not_unit

end Mettapedia.Languages.MeTTa.Experimental.NoValueCBPV
