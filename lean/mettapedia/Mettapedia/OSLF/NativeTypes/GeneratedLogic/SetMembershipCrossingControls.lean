import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCrossing

/-!
# Controls: fixed points that cross steps back

Evaluated by the kernel, among the hereditarily finite sets:

- `νX. ⧫X` (a chain of sets, each a member of the next, going up forever) holds at `∅` (`chain_up`); its least fixed
  point holds nowhere (`no_chain_up`): an ascending chain never ends.
- `μX. (is ∅ ∨ ⧫X)` holds at `∅` and fails at `{∅}` (`empty_reaches_empty`, `single_not_down`): a set containing
  `{∅}` has height at least two, so going up never meets `∅`.
- `νX. ◇⧫X` (some member is a member of a set where it holds again) fails at `∅` and holds at `{∅}`
  (`empty_no_member_up`, `single_member_up`); its variable sits at depth zero after a step forward and a step back.
- A fixed point under a step forward, `μX. (is ∅ ∨ ◇X)`, is not crossing; the guarded decision decides it, and the
  crossing decision does not answer (`guarded_not_crossing`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.CrossingControls

open Mettapedia.OSLF.MeTTaIL.Syntax

def empty : Pattern := set []
def single (member : Pattern) : Pattern := set [member]

theorem empty_hf : IsHF empty := .members fun _ member => absurd member List.not_mem_nil
theorem single_hf : IsHF (single empty) := .members fun _ member => by
  rw [List.mem_singleton.mp member]
  exact empty_hf

/-- A chain of sets going up forever. -/
def chainUp : Formula 0 := .nu (.sometimeBefore .any (.var 0))

/-- Its least fixed point. -/
def chainUpLeast : Formula 0 := .mu (.sometimeBefore .any (.var 0))

/-- Going up meets `∅`. -/
def upToEmpty : Formula 0 := .mu (.or (.is empty) (.sometimeBefore .any (.var 0)))

/-- Some member is a member of a set where this holds again. -/
def memberUp : Formula 0 := .nu (.possibly .any (.sometimeBefore .any (.var 0)))

/-- Going down meets `∅`: guarded, not crossing. -/
def downToEmpty : Formula 0 := .mu (.or (.is empty) (.possibly .any (.var 0)))

theorem chain_up_answer : evalCrossing chainUp empty = some true := by decide +kernel

/-- **An ascending chain from `∅` goes on forever.** -/
theorem chain_up : HFSets.sat Env.closed chainUp (hfOf empty_hf) := (evalCrossing_iff chain_up_answer empty_hf).mp rfl

theorem no_chain_up_answer : evalCrossing chainUpLeast empty = some false := by decide +kernel

/-- **The least fixed point of going up holds nowhere**: at `∅` it fails. -/
theorem no_chain_up : ¬ HFSets.sat Env.closed chainUpLeast (hfOf empty_hf) :=
  fun holds => Bool.false_ne_true ((evalCrossing_iff no_chain_up_answer empty_hf).mpr holds)

theorem empty_reaches_answer : evalCrossing upToEmpty empty = some true := by decide +kernel

/-- **`∅` meets `∅` going up**, at once. -/
theorem empty_reaches_empty : HFSets.sat Env.closed upToEmpty (hfOf empty_hf) :=
  (evalCrossing_iff empty_reaches_answer empty_hf).mp rfl

theorem single_down_answer : evalCrossing upToEmpty (single empty) = some false := by decide +kernel

/-- **`{∅}` never meets `∅` going up.** -/
theorem single_not_down : ¬ HFSets.sat Env.closed upToEmpty (hfOf single_hf) :=
  fun holds => Bool.false_ne_true ((evalCrossing_iff single_down_answer single_hf).mpr holds)

theorem empty_member_answer : evalCrossing memberUp empty = some false := by decide +kernel

/-- **`∅` has no member**, so the property fails there. -/
theorem empty_no_member_up : ¬ HFSets.sat Env.closed memberUp (hfOf empty_hf) :=
  fun holds => Bool.false_ne_true ((evalCrossing_iff empty_member_answer empty_hf).mpr holds)

theorem single_member_answer : evalCrossing memberUp (single empty) = some true := by decide +kernel

/-- **At `{∅}` it holds**: `∅` is a member of `{∅}` itself. -/
theorem single_member_up : HFSets.sat Env.closed memberUp (hfOf single_hf) :=
  (evalCrossing_iff single_member_answer single_hf).mp rfl

theorem guarded_not_crossing_answer : evalCrossing downToEmpty empty = none := by decide +kernel

/-- **A fixed point under a step forward is not crossing**: the crossing decision does not answer it. -/
theorem guarded_not_crossing : crossing downToEmpty = false := by decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.CrossingControls
