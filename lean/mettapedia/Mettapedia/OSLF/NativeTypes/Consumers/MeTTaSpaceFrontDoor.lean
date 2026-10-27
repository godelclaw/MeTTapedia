import Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero.FrontDoor

/-!
# The Zero / PeTTa space boundary through the front door

The space consumer's question, whether a result is an answer of a query against a PeTTa space, is a native type of
MeTTa Zero at the front door: some step from the query request reaches the answer (`queryMember_iff_frontDoor`). The
consumer's own decider is a corollary: its check of the first copy of an answer holds exactly where the front door's
native type does (`checkOccurrence_iff_frontDoor`). Copies beyond the first are counted by the consumer's
occurrence-labelled query, which the authored language does not label.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PeTTa (PeTTaSpace)
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero (Zero sat_query_iff)

/-- **An answer of a query is the front door's native type** at the query request. -/
theorem queryMember_iff_frontDoor (space : PeTTaSpace) {spaceTerm pattern template result : Pattern}
    (requestState : IsState (MeTTaZero.queryRequestPattern spaceTerm pattern template))
    (answerState : IsState (MeTTaZero.queryAnswerPattern result)) :
    (∃ occurrence, QueryMember space pattern template result occurrence) ↔
      (Zero PeTTa.MeTTaZeroExtension.model space spaceTerm).sat Env.closed
        (.possibly .any (.is (MeTTaZero.queryAnswerPattern result)))
        (MeTTaZero.queryRequestPattern spaceTerm pattern template) := by
  exact (queryMember_iff_authored space spaceTerm pattern template result).trans
    ((Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy.totalTheory_query_step_iff _ _ _ _ _ _).trans
      (sat_query_iff PeTTa.MeTTaZeroExtension.model space requestState answerState).symm)

/-- **The consumer's decider is a corollary**: its check of the first copy of an answer holds exactly where the front
door's native type does. -/
theorem checkOccurrence_iff_frontDoor (space : PeTTaSpace) {spaceTerm pattern template result : Pattern}
    (requestState : IsState (MeTTaZero.queryRequestPattern spaceTerm pattern template))
    (answerState : IsState (MeTTaZero.queryAnswerPattern result)) :
    checkOccurrence space pattern template result 0 = true ↔
      (Zero PeTTa.MeTTaZeroExtension.model space spaceTerm).sat Env.closed
        (.possibly .any (.is (MeTTaZero.queryAnswerPattern result)))
        (MeTTaZero.queryRequestPattern spaceTerm pattern template) := by
  rw [← queryMember_iff_frontDoor space requestState answerState, checkOccurrence_exact]
  constructor
  · exact fun member => ⟨0, member⟩
  · rintro ⟨occurrence, member⟩
    rw [queryMember_iff] at member ⊢
    omega

end Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpace
