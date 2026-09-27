import MettapediaFourColor.HubcapOrbit
import FourColor.Present10Defs

/-!
# Sharing a discharging certificate across a half turn

The reference hubcap `f10_242` has ten positions and period five. Equality of
the entire rotated parts transports five representative checks to the other
five positions. This is a second application of the same orbit lemma used
by `PeriodicHubcap`, with a different period and different charge bounds.

The part and rules come from Gonthier and Werner's proof, formalized in Lean
by Chris Emery. The original ten check theorems are not imported here.
-/

namespace FourColor.HalfTurnHubcap

open HubcapOrbit

def bound (j : ℕ) : ℤ :=
  match j % 5 with
  | 0 => 4
  | 1 => 5
  | 2 => 5
  | 3 => 4
  | _ => 2

def cap : Hubcap := oneEntries bound (List.range 10)

/-- Rotation by five positions leaves the full checker input unchanged. -/
theorem rotations : ∀ j : Fin 10,
    hubcapRot 10 j.val p10_241r = hubcapRot 10 (j.val % 5) p10_241r := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_zero : checkDbound2 theRedpart rf10 (hubcapRot 10 0 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_one : checkDbound2 theRedpart rf10 (hubcapRot 10 1 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_two : checkDbound2 theRedpart rf10 (hubcapRot 10 2 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_three : checkDbound2 theRedpart rf10 (hubcapRot 10 3 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_four : checkDbound2 theRedpart rf10 (hubcapRot 10 4 p10_241r) 2 = true := by
  decide +kernel

/-- The five representative checks imply all ten hubcap constraints. -/
theorem fit : hubcapFit theRedpart rf10 p10_241r cap = true := by
  apply oneEntries_fit_periodic theRedpart rf10 p10_241r bound (List.range 10) 5
    (by decide)
  · intro j hj
    exact rotations ⟨j, List.mem_range.mp hj⟩
  · intro j _
    simp [bound]
  · intro j hj
    interval_cases j
    · exact check_zero
    · exact check_one
    · exact check_two
    · exact check_three
    · exact check_four

/-- The shared certificate closes the original part in the discharging proof. -/
theorem succeeds (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_241r := by
  exact succeed_by_hubcap10 hred cap rfl (by decide +kernel)
    (by decide +kernel) fit

#print axioms fit
#print axioms succeeds

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in List.range 10 do
    let name := Name.str `FourColor s!"c10_242_{i + 1}"
    if env.contains name then
      throwError m!"The replacement must not import the original check {name}"
  if env.contains `FourColor.f10_242 then
    throwError "The replacement must not import the original hubcap theorem"

end FourColor.HalfTurnHubcap
