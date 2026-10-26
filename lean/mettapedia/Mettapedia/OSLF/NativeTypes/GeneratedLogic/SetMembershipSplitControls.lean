import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitProofs

/-!
# Controls: splits of hereditarily finite sets

Each verdict is decided on the parts region and carried to the membership language by `decideRegional_iff`. A set
splits into two sets whose union it is; the parts may overlap. Two verdicts are also read as sentences of set theory,
true or false in the model of the sets (`denote_nativeTypeSentence_regional`), the four cases of the
certificate compiler run on splits, with the sizes of the derivations: splits proved and refuted and every-splits
refuted from the laws of the empty set, the power set and separation, and an every-split with upward parts proved
from them alone and, in the classical profile, from them and excluded middle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (model)

theorem two_hereditary : IsHF two := (hereditary_iff _).mp (by decide +kernel)
theorem one_hereditary : IsHF one := (hereditary_iff _).mp (by decide +kernel)
theorem three_hereditary : IsHF three := (hereditary_iff _).mp (by decide +kernel)

/-- **`2 = {0, 1}` splits into `{0}` and `{1}`.** -/
theorem two_splits_apart : Membership.sat Env.closed (.split .hashSet (.is one) (.is (set [one]))) two :=
  (decideRegional_iff rfl two_hereditary).mp (by decide +kernel)

/-- **`1 = {0}` splits into two copies of itself**: the parts may overlap. -/
theorem one_splits_into_itself : Membership.sat Env.closed (.split .hashSet (.is one) (.is one)) one :=
  (decideRegional_iff rfl one_hereditary).mp (by decide +kernel)

/-- **`1` does not split into two empty sets.** -/
theorem one_not_two_empties : ¬ Membership.sat Env.closed (.split .hashSet (.empty .hashSet) (.empty .hashSet)) one :=
  fun holdsAt => absurd ((decideRegional_iff rfl one_hereditary).mpr holdsAt) (by decide +kernel)

/-- **Every split of `2` has a part containing `1`.** -/
theorem two_every_split_keeps_one :
    Membership.sat Env.closed (.everySplit .hashSet (.possibly .any (.is one)) (.possibly .any (.is one))) two :=
  (decideRegional_iff rfl two_hereditary).mp (by decide +kernel)

/-- **Not every split of `2` has a part containing `0` and `1`**: `{0} ∪ {1}` is a split. -/
theorem two_some_split_separates :
    ¬ Membership.sat Env.closed (.everySplit .hashSet (.atLeast 2 .forward .any .top) (.atLeast 2 .forward .any .top))
      two :=
  fun holdsAt => absurd ((decideRegional_iff rfl two_hereditary).mpr holdsAt) (by decide +kernel)

/-- **Some member of `3` splits into `1` and itself**: `2 = {0} ∪ {0, 1}`. -/
theorem three_member_splits :
    Membership.sat Env.closed (.possibly .any (.split .hashSet (.is one) (.is two))) three :=
  (decideRegional_iff rfl three_hereditary).mp (by decide +kernel)

/-- **Every descent from `3` ends at a set that splits into empty parts**: splits under a least fixed point. -/
theorem three_descends_to_split_empty :
    Membership.sat Env.closed (.mu (.or (.split .hashSet (.empty .hashSet) (.empty .hashSet))
      (.and (.nonEmpty .hashSet) (.necessarily .any (.var 0))))) three :=
  (decideRegional_iff rfl three_hereditary).mp (by decide +kernel)

/-- **The split of `2` into `{0}` and `{1}` is a true sentence of set theory.** -/
theorem two_splits_apart_sentence :
    model.{0}.models (nativeTypeSentence (.split .hashSet (.is one) (.is (set [one]))) two) :=
  (denote_nativeTypeSentence_regional rfl two_hereditary _).mpr two_splits_apart

/-- **That `1` splits into two empty sets is a false sentence of set theory.** -/
theorem one_not_two_empties_sentence :
    ¬ model.{0}.models (nativeTypeSentence (.split .hashSet (.empty .hashSet) (.empty .hashSet)) one) :=
  fun holds => one_not_two_empties ((denote_nativeTypeSentence_regional rfl one_hereditary _).mp holds)

/-! ## Split sentences through the certificate compiler -/

/-- The size of a derivation, and its side. -/
def splitReport {φ : Mettapedia.Logic.HOL.ClosedFormula Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.Symbol}
    {ψ : Mettapedia.Logic.HOL.ClosedFormula Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.Symbol} :
    Proof lawList φ ⊕ Proof lawList ψ → String
  | .inl proof => s!"proved in {proofSize proof} rules"
  | .inr proof => s!"refuted in {proofSize proof} rules"

/-- **`2 = {0} ∪ {1}`, proved from the three laws.** -/
def splitsApart : Formula 0 := .split .hashSet (.is one) (.is (set [one]))

/-- info: "proved in 8250 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := splitsApart) rfl two_hereditary)

/-- **`1` is not the union of two empty sets**, refuted from the three laws by the case analysis on which members
land in which part. -/
def splitsEmpty : Formula 0 := .split .hashSet (.empty .hashSet) (.empty .hashSet)

/-- info: "refuted in 1504 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := splitsEmpty) rfl one_hereditary)

-- With two members, the case analysis branches over nine coverings.
/-- info: "refuted in 9063 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := splitsEmpty) rfl two_hereditary)

/-- **Not every split of `2` has a part with two members**: refuted from the three laws, with no excluded middle. -/
def everySplitTwoMembers : Formula 0 :=
  .everySplit .hashSet (.atLeast 2 .forward .any .top) (.atLeast 2 .forward .any .top)

/-- info: "refuted in 3840 rules" -/
#guard_msgs in
#eval splitReport (compileSentenceClassical (formula := everySplitTwoMembers) rfl two_hereditary)

/-- **Every split of `2` has a part containing `1`**: its parts are upward, so the core profile proves it from the three
laws; the classical profile proves it from them and excluded middle, as the implication from it. -/
def everySplitKeepsOne : Formula 0 := .everySplit .hashSet (.possibly .any (.is one)) (.possibly .any (.is one))

/-- info: "proved in 9485 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := everySplitKeepsOne) rfl two_hereditary)

/-- info: "proved in 22144 rules" -/
#guard_msgs in
#eval splitReport (compileSentenceClassical (formula := everySplitKeepsOne) rfl two_hereditary)

/-- **A split under a step**: some member of `3` is `1 ∪ 2`. -/
def memberSplits : Formula 0 := .possibly .any (.split .hashSet (.is one) (.is two))

/-- info: "proved in 11382 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := memberSplits) rfl three_hereditary)

/-- **A split under a least fixed point**: every descent from `3` ends at a set that splits into empty parts. -/
def descendsToEmptySplit : Formula 0 := .mu (.or (.split .hashSet (.empty .hashSet) (.empty .hashSet))
  (.and (.nonEmpty .hashSet) (.necessarily .any (.var 0))))

/-- info: "proved in 7057 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := descendsToEmptySplit) rfl three_hereditary)

/-- The core profile takes every-splits with upward parts, and leaves out the others. -/
example : everySplitKeepsOne.regionalWith false = true ∧ everySplitTwoMembers.regionalWith false = false :=
  ⟨rfl, rfl⟩

/-! ## Splits at the front door -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- **Without a decider the front door leaves splits open**: its canonical regions hold reachable states, not parts. -/
theorem ask_split_open :
    ask RelationEnv.empty [] membership 2 splitsApart two none 4 (some membershipForms) = .unknown 4 := by
  decide +kernel

/-- **With the parts-region decider it proves the split**, `2 = {0} ∪ {1}`. -/
theorem askWith_split_proved :
    askWith RelationEnv.empty [] membership 2 splitsApart two setDecider none 4 (some membershipForms) =
      .proved .decided := by
  decide +kernel

/-- **And refutes one that fails**: `1` is not the union of two empty sets. -/
theorem askWith_split_refuted :
    askWith RelationEnv.empty [] membership 2 splitsEmpty one setDecider none 4 (some membershipForms) =
      .refuted .decided := by
  decide +kernel

/-- **And decides an every-split**: every split of `2` has a part containing `1`. -/
theorem askWith_everySplit_proved :
    askWith RelationEnv.empty [] membership 2 everySplitKeepsOne two setDecider none 4 (some membershipForms) =
      .proved .decided := by
  decide +kernel

/-- The kind of a certified set verdict. -/
def setVerdictKind {formula : Formula 0} {term : Pattern} : SetVerdict (L := ℕ) formula term → String
  | .proved _ => "proved from the three laws"
  | .provedClassically _ => "proved from the three laws and excluded middle"
  | .refuted _ => "refuted from the three laws"

/-- info: "proved from the three laws" -/
#guard_msgs in
#eval setVerdictKind (askSets (formula := splitsApart) rfl two_hereditary)

/-- info: "refuted from the three laws" -/
#guard_msgs in
#eval setVerdictKind (askSets (formula := splitsEmpty) rfl one_hereditary)

/-- info: "proved from the three laws" -/
#guard_msgs in
#eval setVerdictKind (askSets (formula := everySplitKeepsOne) rfl two_hereditary)

/-- info: "refuted from the three laws" -/
#guard_msgs in
#eval setVerdictKind (askSets (formula := everySplitTwoMembers) rfl two_hereditary)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
