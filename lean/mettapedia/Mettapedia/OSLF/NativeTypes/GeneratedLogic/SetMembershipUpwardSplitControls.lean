import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipUpwardSplits
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitControls

/-!
# Controls: every-splits with upward parts, from the three laws

- Every split of `1` has a nonempty part: proved from the laws of the empty set, the power set and separation in 1,883
  rules; the classical compiler's proof, from excluded middle as well, takes 2,423.
- Every split of `2` has a part with `1` as a member (`everySplitKeepsOne`): proved from the three laws in 9,485
  rules, with a closed term in the package (`everySplitKeepsOne_core_proofTerm`); the classical proof takes 22,144.
- Nested: some member of `2` has every split with a nonempty part (2,896 rules), and some member of `2` has every split
  with a part containing `0` (3,102 rules).
- "Every split has a first part that is empty or has a member" is not upward (`emptyOrInhabited_part_not_upward`):
  "empty" is not, and that every-split is excluded middle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Every split has a nonempty part. -/
def nonEmptyPart : Formula 0 := .everySplit .hashSet (.nonEmpty .hashSet) (.nonEmpty .hashSet)

theorem one_nonEmptyPart : Membership.sat Env.closed nonEmptyPart one :=
  (decideRegional_iff rfl one_hereditary).mp (by decide +kernel)

theorem two_everySplitKeepsOne : Membership.sat Env.closed everySplitKeepsOne two :=
  (decideRegional_iff rfl two_hereditary).mp (by decide +kernel)

/-- The core proof that every split of `1` has a nonempty part. -/
def nonEmptyPartProof : Proof lawList (nativeTypeSentence nonEmptyPart one) :=
  upwardEverySplitProof lawsOfList (left := .nonEmpty .hashSet) (right := .nonEmpty .hashSet) rfl rfl rfl rfl
    one_hereditary one_nonEmptyPart

/-- The core proof that every split of `2` has a part with `1` as a member. -/
def everySplitKeepsOneProof : Proof lawList (nativeTypeSentence everySplitKeepsOne two) :=
  upwardEverySplitProof lawsOfList (left := .possibly .any (.is one)) (right := .possibly .any (.is one)) rfl rfl
    rfl rfl two_hereditary two_everySplitKeepsOne

/-- info: 1883 -/
#guard_msgs in
#eval proofSize nonEmptyPartProof

/-- info: 2423 -/
#guard_msgs in
#eval proofSize (sentenceProofClassical (formula := nonEmptyPart) rfl one_hereditary one_nonEmptyPart)

/-- info: 9485 -/
#guard_msgs in
#eval proofSize everySplitKeepsOneProof

/-- Some member has every split with a nonempty part. -/
def memberNonEmptyPart : Formula 0 := .possibly .any nonEmptyPart

/-- Some member has every split with a part containing `0`. -/
def memberKeepsZero : Formula 0 :=
  .possibly .any (.everySplit .hashSet (.possibly .any (.is zero)) (.possibly .any (.is zero)))

/-- info: "proved in 2896 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := memberNonEmptyPart) rfl two_hereditary)

/-- info: "proved in 3102 rules" -/
#guard_msgs in
#eval splitReport (compileSentence (formula := memberKeepsZero) rfl two_hereditary)

/-- **"Empty" is not upward**, so the first part of `emptyOrInhabited` is not. -/
theorem emptyOrInhabited_part_not_upward :
    (Formula.or (.empty .hashSet) (.possibly .any .top) : Formula 0).upwardShape = false := rfl

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L]

/-- **Every split of `2` has a part with `1` as a member, by a closed term of the package with no excluded middle.** -/
theorem everySplitKeepsOne_core_proofTerm :
    ∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (nativeTypeSentence everySplitKeepsOne two)))) :=
  ⟨packageTerm everySplitKeepsOneProof, packageTerm_typed _⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
