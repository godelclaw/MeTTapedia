import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitControls

/-!
# Controls: splits of hereditarily finite sets through the generic contract

The membership language is a flat set language, so its canonical forms (every set sorted without repetition, bottom
up) list the parts of each set by coverings (`hereditaryParts`), and the generic parts decider decides its splits
(`flatPartsDecider`). The set decider of `SetMembershipSplits` decides them on the term's parts region by its own
semantics; certified deciders never disagree (`Decider.agree`), and on the split controls they give the same
verdicts.

- `2` splits into `1` and `{1}` (`generic_two_splits_apart`); neither `1` nor `2` splits into two empty sets
  (`generic_one_no_empty_split`, `generic_two_no_empty_split`).
- Every split of `2` has a part with `1` as a member (`generic_two_every_split_keeps_one`).
- `3` is well founded (`generic_three_wellFounded`): the generic decider decides the step formulas too.
- The two deciders agree on these verdicts (`deciders_agree`), and the front door with the generic decider proves the
  split of `2` and refutes the empty split (`ask_generic_two_splits_apart`, `ask_generic_two_no_empty_split`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- The generic parts decider for the membership language. -/
def membershipPartsDecider : Decider RelationEnv.empty membership := flatPartsDecider membership_flat 2 2

theorem generic_true {formula : Formula 0} {term : Pattern}
    (decided : membershipPartsDecider.decide formula term = some true) :
    (referenceStructure RelationEnv.empty membership).sat Env.closed formula term :=
  (membershipPartsDecider.exact decided).mpr rfl

theorem generic_false {formula : Formula 0} {term : Pattern}
    (decided : membershipPartsDecider.decide formula term = some false) :
    ¬ (referenceStructure RelationEnv.empty membership).sat Env.closed formula term := fun holds =>
  Bool.false_ne_true ((membershipPartsDecider.exact decided).mp holds)

/-- **`2` splits into `1` and `{1}`.** -/
theorem generic_two_splits_apart : (referenceStructure RelationEnv.empty membership).sat Env.closed splitsApart two :=
  generic_true (by decide +kernel)

/-- **`1` does not split into two empty sets.** -/
theorem generic_one_no_empty_split : ¬ (referenceStructure RelationEnv.empty membership).sat Env.closed splitsEmpty one :=
  generic_false (by decide +kernel)

/-- **Nor does `2`.** -/
theorem generic_two_no_empty_split : ¬ (referenceStructure RelationEnv.empty membership).sat Env.closed splitsEmpty two :=
  generic_false (by decide +kernel)

/-- **Every split of `2` has a part with `1` as a member.** -/
theorem generic_two_every_split_keeps_one :
    (referenceStructure RelationEnv.empty membership).sat Env.closed everySplitKeepsOne two :=
  generic_true (by decide +kernel)

/-- **`3` is well founded.** -/
theorem generic_three_wellFounded :
    (referenceStructure RelationEnv.empty membership).sat Env.closed (.mu (.necessarily .any (.var 0))) three :=
  generic_true (by decide +kernel)

/-- **The generic decider and the set decider give the same verdicts on the split controls.** -/
theorem deciders_agree :
    membershipPartsDecider.decide splitsApart two = setDecider.decide splitsApart two ∧
      membershipPartsDecider.decide splitsEmpty one = setDecider.decide splitsEmpty one ∧
      membershipPartsDecider.decide splitsEmpty two = setDecider.decide splitsEmpty two ∧
      membershipPartsDecider.decide everySplitKeepsOne two = setDecider.decide everySplitKeepsOne two := by
  decide +kernel

theorem ask_generic_two_splits_apart_answer :
    askWith RelationEnv.empty [] membership 2 splitsApart two membershipPartsDecider none 4 (some membershipForms) =
      .proved .decided := by
  decide +kernel

/-- **The front door with the generic decider proves that `2` splits into `1` and `{1}`.** -/
theorem ask_generic_two_splits_apart : (referenceStructure RelationEnv.empty membership).sat Env.closed splitsApart two :=
  askWith_proved ask_generic_two_splits_apart_answer

theorem ask_two_no_empty_split_answer :
    askWith RelationEnv.empty [] membership 2 splitsEmpty two membershipPartsDecider none 4 (some membershipForms) =
      .refuted .decided := by
  decide +kernel

/-- **And refutes that it splits into two empty sets.** -/
theorem ask_generic_two_no_empty_split :
    ¬ (referenceStructure RelationEnv.empty membership).sat Env.closed splitsEmpty two :=
  askWith_refuted ask_two_no_empty_split_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
