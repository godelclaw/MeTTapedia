import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCrossing
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPracticalStage
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplits

/-!
# The set driver: the membership language read on its hereditary terms

The membership language (`SetMembership.membership`, one rule `{x, ...rest} ⇒ x`) read modulo the set laws has the
hereditarily finite sets as its states and membership as its steps. Its declared hereditary reading takes the
hereditary terms as its carrier (`HFNative`): past modalities, counting of containers and quantifiers over a type then
range over hereditary terms, not over every pattern of the reference structure.

- **The set driver** (`askHereditary`): at a hereditary term, a context-free formula is answered by the decision of
  its fragment: count-guarded formulas by stage evaluation (counting and singletons under steps back, guarded fixed
  points, quantifiers over a type), crossing fixed points by elimination to two-way types (`evalCrossing`). It answers
  nothing elsewhere.
- **Stage evaluation searches representatives** (`evalPractical`): a step back or a quantifier over sets whose body
  has a closed set of representatives searches those, not the whole stage; otherwise it searches the stage
  (`evalCounted`). The two agree on every count-guarded formula (`evalPractical_eq`).
- **Every answer is exact in the hereditary reading** (`askHereditary_sound`), through the exact morphism onto the
  hereditarily finite sets (`sat_iff_hfSets`).
- **Forward formulas read alike in both structures** (`hereditary_iff_membership`), so on them the set driver and the
  front door of the reference structure agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The set driver**: at a hereditary term, a context-free formula decided by its fragment's decision. -/
def askHereditary (formula : Formula 0) (term : Pattern) : Option Bool :=
  if hereditary membership hfRule.category term && formula.contextFree then
    if formula.countGuarded then some (evalPractical formula term) else evalCrossing formula term
  else none

/-- **Every answer of the set driver is exact** in the membership language read on its hereditary terms. -/
theorem askHereditary_sound {formula : Formula 0} {term : Pattern} {answer : Bool}
    (answered : askHereditary formula term = some answer) :
    ∃ holds : IsHF term, (answer = true ↔ HFNative.sat Env.closed formula ⟨term, holds⟩) := by
  unfold askHereditary at answered
  split at answered
  · rename_i fit
    obtain ⟨hereditaryTerm, free⟩ := Bool.and_eq_true_iff.mp fit
    have holds : IsHF term := (hereditary_iff _).mp hereditaryTerm
    refine ⟨holds, ?_⟩
    split at answered
    · rename_i guarded
      cases answered
      rw [evalPractical_eq formula guarded holds]
      exact countGuarded_decide guarded free holds
    · exact (evalCrossing_iff answered holds).trans (sat_iff_hfSets formula free ⟨term, holds⟩).symm
  · cases answered

/-- **Forward formulas read alike** among the hereditary terms and in the reference structure. -/
theorem hereditary_iff_membership {formula : Formula 0} (forward : formula.forward = true) {term : Pattern}
    (holds : IsHF term) :
    HFNative.sat Env.closed formula ⟨term, holds⟩ ↔ Membership.sat Env.closed formula term :=
  (NativeStructure.Generated.inclusion hereditary_generated).sat_iff formula forward
    (BoundedMorphism.envPreimage_closed _) ⟨term, holds⟩

/-- **On forward formulas the set driver is the front door of the reference structure.** -/
theorem askHereditary_membership {formula : Formula 0} (forward : formula.forward = true) {term : Pattern}
    {answer : Bool} (answered : askHereditary formula term = some answer) :
    answer = true ↔ Membership.sat Env.closed formula term := by
  obtain ⟨holds, exact⟩ := askHereditary_sound answered
  exact exact.trans (hereditary_iff_membership forward holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
