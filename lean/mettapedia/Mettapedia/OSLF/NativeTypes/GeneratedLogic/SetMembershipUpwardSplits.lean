import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExcludedMiddle

/-!
# Every-splits with upward parts need no excluded middle

Some every-splits are excluded middle (`SetMembershipExcludedMiddle`): their part formulas say that a part has no
member. When both part formulas have upward shapes, true of a part as soon as it has certain members, the split itself
is enough, and the certificate compiler's core profile takes them (`Formula.regionalWith false`), nested anywhere:

- **Upward shapes** (`Formula.upwardShape`): truth, "not empty", "has a member with φ", and their conjunctions and
  disjunctions.
- **Each member lies in a part** (`sideOf`): a member of `x = a ∪ b` described by `v` is a member of `a` or of `b`
  described by `v`, constructively, since the union is a disjunction.
- **Branching** (`branchSplits`): taking the members one by one, each branch knows lists of terms describing members of
  `a` and of `b`, covering the term's members. The split of the term by those lists has the first formula at the first
  part or the second at the second.
- **The part a branch knows** (`partDescribedOfEach`): the members of `a` described by the known terms form a part of
  `a`, described by them forward and existentially, where the compiler proves the formula; an upward formula then
  carries to `a` (`upwardMono`).

These are in `SetMembershipProofs`. Here:

- **Every every-split with upward parts that holds is proved from the three laws** (`upwardEverySplitProof`), and so is
  every regional native type whose every-splits all have upward parts (`sentenceProof`).
- **The boundary**: "every split has a first part that is empty or has a member" is not upward, and it is excluded
  middle (`emptyOrInhabited_not_core`, `middleOfEmptyOrInhabited`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Term)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol)

/-- An every-split with upward parts of the core fragment is in the core fragment. -/
theorem everySplit_core {left right : Formula 0} (leftShape : left.upwardShape = true)
    (rightShape : right.upwardShape = true) (leftCore : left.regionalWith false = true)
    (rightCore : right.regionalWith false = true) :
    (Formula.everySplit .hashSet left right).regionalWith false = true := by
  simp only [Formula.regionalWith, leftShape, rightShape, leftCore, rightCore, Bool.and_self, Bool.or_true]

/-- **Every every-split with upward parts that holds is proved from the three laws**, with no excluded middle. -/
def upwardEverySplitProof {Δ : List (Term Symbol [] .prop)} (laws : HasLaws Δ) {left right : Formula 0}
    (leftShape : left.upwardShape = true) (rightShape : right.upwardShape = true)
    (leftCore : left.regionalWith false = true) (rightCore : right.regionalWith false = true) {term : Pattern}
    (holds : IsHF term) (holdsAt : Membership.sat Env.closed (.everySplit .hashSet left right) term) :
    Proof Δ (nativeTypeSentence (.everySplit .hashSet left right) term) :=
  sentenceProofIn laws.core (everySplit_core leftShape rightShape leftCore rightCore) holds holdsAt

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
