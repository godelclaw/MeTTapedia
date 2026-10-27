import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWay

/-!
# Controls: two-way native types of the hereditarily finite sets

Steps back nested with steps forward and quantifiers over the sort, decided by the evaluation and read among the
hereditary terms.

- A member of `1` lies in a set with a member that has a member (`member_of_one_in_deep_set`).
- No set containing `0` lies in an empty set (`no_container_in_empty_set`); no set containing `0` is empty after a
  further step back either (`no_empty_container_of_container`).
- Some set containing `0` has only members that lie in some set (`container_members_contained`).
- No set lies in an empty set (`no_set_in_empty_set`), every set lies in some set (`every_set_contained`), and every
  set lies in a set with a member that has a member (`every_set_in_deep_set`).
- Named sets and splits: `0` lies in `1` (`zero_in_one`) and not in itself (`zero_not_in_zero`); some set containing `0`
  splits into `1` and a nonempty part other than `1` (`container_splits_off_one`); every set containing `0` has a split
  with a part containing `0` (`container_split_keeps_zero`); `1` splits into two parts both `1`
  (`one_splits_into_ones`), parts that share their member.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem one_hf : IsHF one := (hereditary_iff _).mp (by decide)

/-- Has a member with a member, as a two-way formula. -/
def deepSet : Formula 0 := .possibly .any (.possibly .any .top)

/-- Has no member. -/
def noMember : Formula 0 := .necessarily .any .bot

/-- **A member of `1` lies in a set with a member that has a member.** -/
theorem member_of_one_in_deep_set :
    HFNative.sat Env.closed (.possibly .any (.sometimeBefore .any deepSet)) ⟨one, one_hf⟩ :=
  (twoWay_decide rfl rfl one_hf).mp (by decide +kernel)

/-- **No set containing `0` lies in an empty set.** -/
theorem no_container_in_empty_set :
    ¬ HFNative.sat Env.closed (.sometimeBefore .any (.sometimeBefore .any noMember)) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((twoWay_decide rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Some set containing `0` has only members that lie in some set.** -/
theorem container_members_contained :
    HFNative.sat Env.closed (.sometimeBefore .any (.necessarily .any (.sometimeBefore .any .top))) ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

/-- **Every set containing `0` has a member lying in an empty set: false.** -/
theorem no_empty_container_of_container :
    ¬ HFNative.sat Env.closed (.alwaysBefore .any (.possibly .any (.sometimeBefore .any (.empty .hashSet))))
      ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((twoWay_decide rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **No set lies in an empty set.** -/
theorem no_set_in_empty_set :
    ¬ HFNative.sat Env.closed (.someOf (.base "Set") (.sometimeBefore .any noMember)) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((twoWay_decide rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Every set lies in some set.** -/
theorem every_set_contained :
    HFNative.sat Env.closed (.everyOf (.base "Set") (.sometimeBefore .any .top)) ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

/-- **Every set lies in a set with a member that has a member.** -/
theorem every_set_in_deep_set :
    HFNative.sat Env.closed (.everyOf (.base "Set") (.sometimeBefore .any deepSet)) ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)


/-- **`0` lies in `1`.** -/
theorem zero_in_one : HFNative.sat Env.closed (.sometimeBefore .any (.is one)) ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

/-- **`0` does not lie in itself.** -/
theorem zero_not_in_zero : ¬ HFNative.sat Env.closed (.sometimeBefore .any (.is zero)) ⟨zero, zero_hf⟩ :=
  fun holds => absurd ((twoWay_decide rfl rfl zero_hf).mpr holds) (by decide +kernel)

/-- **Some set containing `0` splits into `1` and a nonempty part other than `1`.** -/
theorem container_splits_off_one :
    HFNative.sat Env.closed (.sometimeBefore .any (.split .hashSet (.is one) (.and (.nonEmpty .hashSet) (.isNot one))))
      ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

/-- **Every set containing `0` has a split with a part containing `0`.** -/
theorem container_split_keeps_zero :
    HFNative.sat Env.closed (.alwaysBefore .any (.split .hashSet (.possibly .any (.is zero)) .top)) ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

/-- **`1` splits into two parts both `1`**, sharing their member. -/
theorem one_splits_into_ones :
    HFNative.sat Env.closed (.someOf (.base "Set") (.and (.is one) (.split .hashSet (.is one) (.is one))))
      ⟨zero, zero_hf⟩ :=
  (twoWay_decide rfl rfl zero_hf).mp (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
