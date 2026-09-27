import MettapediaFourColor.HubcapOrbit
import FourColor.Present10Defs

/-!
# A periodic discharging case with two representative checks

This proves the hubcap obligation `f10_128` from the classical presentation
using two checker computations instead of ten. The reference proof is by
Gonthier and Werner, formalized in Lean by Chris Emery. Only its part and rule
definitions are imported here; its ten check theorems are not used.

The generic orbit lemma assembles all ten constraints. A separate finite
calculation checks the equalities between their rotated boundary data. The
result is consumed by the discharging soundness theorem for the actual part.
-/

namespace FourColor.PeriodicHubcap

open HubcapOrbit

def bound (j : ℕ) : ℤ := if j % 2 = 0 then 2 else 4

def cap : Hubcap := oneEntries bound (List.range 10)

/-- The part presented by any position agrees with its parity representative. -/
theorem rotations : ∀ j : Fin 10,
    hubcapRot 10 j.val p10_127r = hubcapRot 10 (j.val % 2) p10_127r := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The even-position representative. -/
theorem even_check : checkDbound2 theRedpart rf10 (hubcapRot 10 0 p10_127r) 2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd-position representative. -/
theorem odd_check : checkDbound2 theRedpart rf10 (hubcapRot 10 1 p10_127r) 4 = true := by
  decide +kernel

/-- All ten constraints follow from the two representative computations. -/
theorem fit : hubcapFit theRedpart rf10 p10_127r cap = true := by
  apply oneEntries_fit_periodic theRedpart rf10 p10_127r bound (List.range 10) 2
    (by decide)
  · intro j hj
    exact rotations ⟨j, List.mem_range.mp hj⟩
  · intro j _
    simp [bound]
  · intro j hj
    interval_cases j
    · exact even_check
    · exact odd_check

/-- The compressed certificate closes the same part in the classical argument. -/
theorem succeeds (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_127r := by
  exact succeed_by_hubcap10 hred cap rfl (by decide +kernel)
    (by decide +kernel) fit

#print axioms fit
#print axioms succeeds

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in List.range 10 do
    let name := Name.str `FourColor s!"c10_128_{i + 1}"
    if env.contains name then
      throwError m!"The replacement must not import the original check {name}"
  if env.contains `FourColor.f10_128 then
    throwError "The replacement must not import the original hubcap theorem"

end FourColor.PeriodicHubcap
