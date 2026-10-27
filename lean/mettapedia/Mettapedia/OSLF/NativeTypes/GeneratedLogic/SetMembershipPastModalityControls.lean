import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastModalities

/-!
# Controls: past modalities and quantifiers over the type, by finite search

Each verdict is a finite search over subsets of a finite stage `V_n`, each candidate decided on its parts region, and
read among the hereditary terms.

- Some set containing `0` has a member with a member (`zero_in_deep_set`); no set containing `0` is empty
  (`no_empty_container`), and every set containing `0` has a member (`every_container_inhabited`).
- Not every set containing `0` has a member with a member (`not_every_container_deep`): `{0}` contains `0`.
- Some set has a member and only empty members (`some_set_of_empty_members`); no set is both empty and inhabited
  (`no_empty_inhabited_set`); not every set has a member (`not_every_set_inhabited`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Has a member. -/
def inhabited : Formula 0 := .possibly .any .top

/-- Has a member with a member. -/
def deep : Formula 0 := .possibly .any inhabited

/-- Has no member. -/
def emptySet : Formula 0 := .necessarily .any .bot

/-- **Some set containing `0` has a member with a member.** -/
theorem zero_in_deep_set : HFNative.sat Env.closed (.sometimeBefore .any deep) ⟨zero, zero_hf⟩ :=
  (decideSometimeBefore_iff rfl rfl zero_hf).mp (by decide +kernel)

/-- **No set containing `0` is empty.** -/
theorem no_empty_container : ¬ HFNative.sat Env.closed (.sometimeBefore .any emptySet) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((decideSometimeBefore_iff rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Every set containing `0` has a member.** -/
theorem every_container_inhabited : HFNative.sat Env.closed (.alwaysBefore .any inhabited) ⟨zero, zero_hf⟩ :=
  (decideAlwaysBefore_iff rfl rfl zero_hf).mp (by decide +kernel)

/-- **Not every set containing `0` has a member with a member.** -/
theorem not_every_container_deep : ¬ HFNative.sat Env.closed (.alwaysBefore .any deep) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((decideAlwaysBefore_iff rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Some set has a member and only empty members**: `{0}`. -/
theorem some_set_of_empty_members :
    HFNative.sat Env.closed (.someOf (.base "Set") (.and inhabited (.necessarily .any emptySet))) ⟨zero, zero_hf⟩ :=
  (decideSomeOf_iff rfl zero_hf).mp (by decide +kernel)

/-- **No set is both empty and inhabited.** -/
theorem no_empty_inhabited_set :
    ¬ HFNative.sat Env.closed (.someOf (.base "Set") (.and emptySet inhabited)) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((decideSomeOf_iff rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Not every set has a member**: the empty set. -/
theorem not_every_set_inhabited : ¬ HFNative.sat Env.closed (.everyOf (.base "Set") inhabited) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((decideEveryOf_iff rfl zero_hf).mpr holds) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
