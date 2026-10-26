import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExcludedMiddle

/-!
# Controls: every-splits and excluded middle

The derivations between the sentences of `emptyOrInhabited` and `emptyOrNonEmpty` at `1 = {0}` and the two
principles, from the laws of the empty set, the power set and separation, with their sizes. At `0` the sentence of
`emptyOrInhabited` needs no principle. The certificate compiler's classical proof at `1`, which is uniform in the
native type, is larger than the derivation from excluded middle by hand.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

/-- `0` is a member of `1`. -/
theorem zero_mem_one : zero ∈ membersOf one := List.mem_singleton.mpr rfl

-- The every-split at `1` gives excluded middle.
/-- info: 798 -/
#guard_msgs in
#eval proofSize (middleOfEmptyOrInhabited lawsOfList one_isHF zero_mem_one)

-- Excluded middle gives the every-split at `1`.
/-- info: 206 -/
#guard_msgs in
#eval proofSize (emptyOrInhabitedOfMiddle lawsOfList one_isHF)

-- The every-split with "not empty" at `1` gives weak excluded middle.
/-- info: 794 -/
#guard_msgs in
#eval proofSize (weakMiddleOfEmptyOrNonEmpty lawsOfList one_isHF zero_mem_one)

-- Weak excluded middle gives it.
/-- info: 187 -/
#guard_msgs in
#eval proofSize (emptyOrNonEmptyOfWeakMiddle lawsOfList one_isHF)

-- Excluded middle gives weak excluded middle.
/-- info: 9 -/
#guard_msgs in
#eval proofSize (weakMiddleOfMiddle (Δ := lawList))

-- At `0` the every-split needs no principle.
/-- info: 224 -/
#guard_msgs in
#eval proofSize (emptyOrInhabitedAtZero lawsOfList)

-- The certificate compiler's classical proof at `1`.
/-- info: 2488 -/
#guard_msgs in
#eval proofSize (sentenceProofClassical emptyOrInhabited_regional one_isHF emptyOrInhabited_one)

/-- The core profile's fragment leaves this every-split out: its first part is not upward. -/
example : emptyOrInhabited.regionalWith false = false := emptyOrInhabited_not_core

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
