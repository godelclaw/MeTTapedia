import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedDecision
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointControls

/-!
# Controls: counting and singletons with fixed points

- **Count-guarded**: "at least two members", "every hereditary member, and the set itself, has at most one member"
  (`νX. fewer than 2 members ∧ □X`), "some descent reaches a singleton" (`μX. single ⊤ ∨ ◇X`), and "at least two
  members lie in some set" (`≥2 ◆⊤`), whose counted body takes a step back. **Not count-guarded**: counting containers
  (backward).
- **Evaluated by the kernel**: `2 = {0, 1}` has two members, and the term `{0, 0}`, which denotes `1`, has one; `{1}`
  is hereditarily at most one-membered and `2` is not; `2` descends to a singleton and `0` does not; `2` has two members
  that lie in some set, `{0, 0}` has not.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.CountedControls

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The term `{0, 0}`: two members that denote one set. -/
def doubled : Pattern := set [zero, zero]

theorem doubled_hf : IsHF doubled := (hereditary_iff _).mp (by decide +kernel)

/-- **At least two members.** -/
def twoMembers : Formula 0 := .atLeast 2 .forward .any .top

/-- **Hereditarily at most one member**: `νX. (fewer than two members) ∧ □X`. -/
def hereditarilyAtMostOne : Formula 0 := .nu (.and (.allButFewer 2 .forward .any .bot) (.necessarily .any (.var 0)))

/-- **Some descent reaches a singleton**: `μX. single ⊤ ∨ ◇X`. -/
def reachesSingleton : Formula 0 := .mu (.or (.single .hashSet .top) (.possibly .any (.var 0)))

/-- **At least two members lie in some set.** -/
def twoContained : Formula 0 := .atLeast 2 .forward .any (.sometimeBefore .any .top)

theorem twoMembers_countGuarded : twoMembers.countGuarded = true := rfl
theorem hereditarilyAtMostOne_countGuarded : hereditarilyAtMostOne.countGuarded = true := rfl
theorem reachesSingleton_countGuarded : reachesSingleton.countGuarded = true := rfl
theorem twoContained_countGuarded : twoContained.countGuarded = true := rfl

/-- **Not count-guarded**: counting containers. -/
theorem backward_not_countGuarded : (Formula.atLeast 2 .backward .any .top : Formula 0).countGuarded = false := rfl

/-- Guarded formulas are count-guarded: the hereditarily even sets. -/
theorem hereditarilyEven_countGuarded : hereditarilyEven.countGuarded = true := rfl

/-! ## Evaluated by the kernel -/

theorem two_twoMembers : HFSets.sat Env.closed twoMembers (hfOf two_hf) :=
  (evalCounted_iff rfl two_hf).mp (by decide +kernel)

/-- **`{0, 0}` has one member**: its two members denote one set. -/
theorem doubled_not_twoMembers : ¬ HFSets.sat Env.closed twoMembers (hfOf doubled_hf) := fun holds =>
  absurd ((evalCounted_iff rfl doubled_hf).mpr holds) (by decide +kernel)

theorem justOne_hereditarilyAtMostOne : HFSets.sat Env.closed hereditarilyAtMostOne (hfOf justOne_holds) :=
  (evalCounted_iff rfl justOne_holds).mp (by decide +kernel)

theorem two_not_hereditarilyAtMostOne : ¬ HFSets.sat Env.closed hereditarilyAtMostOne (hfOf two_hf) := fun holds =>
  absurd ((evalCounted_iff rfl two_hf).mpr holds) (by decide +kernel)

/-- **`2` descends to a singleton**: its member `1 = {0}`. -/
theorem two_reachesSingleton : HFSets.sat Env.closed reachesSingleton (hfOf two_hf) :=
  (evalCounted_iff rfl two_hf).mp (by decide +kernel)

theorem zero_not_reachesSingleton : ¬ HFSets.sat Env.closed reachesSingleton (hfOf zero_hf) := fun holds =>
  absurd ((evalCounted_iff rfl zero_hf).mpr holds) (by decide +kernel)

theorem two_twoContained : HFSets.sat Env.closed twoContained (hfOf two_hf) :=
  (evalCounted_iff rfl two_hf).mp (by decide +kernel)

theorem doubled_not_twoContained : ¬ HFSets.sat Env.closed twoContained (hfOf doubled_hf) := fun holds =>
  absurd ((evalCounted_iff rfl doubled_hf).mpr holds) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.CountedControls
