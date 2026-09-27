import MettapediaFourColor.ChargeBound
import FourColor.Present10Defs

/-!
# A discharging case with three semantic representatives

The period-five case `p10_241r` also has reflection symmetry. Three checked
charge bounds suffice: reflection supplies two more and the half turn
supplies the remaining five. The consumer bounds the actual charge around
the hub, so it requires no Boolean checker-equivariance assertion.
-/

namespace FourColor.ReflectedHubcap

def bound (j : ℕ) : ℤ :=
  match j % 5 with
  | 0 => 4
  | 1 => 5
  | 2 => 5
  | 3 => 4
  | _ => 2

def representative (j : ℕ) : ℕ :=
  match j % 5 with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | _ => 4

/-- The complete parts and bounds fall into three reflection orbits. -/
theorem representatives : ∀ j : Fin 10,
    (representative j.val = 0 ∨ representative j.val = 1 ∨ representative j.val = 4) ∧
    bound j.val = bound (representative j.val) ∧
    (hubcapRot 10 j.val p10_241r = hubcapRot 10 (representative j.val) p10_241r ∨
      hubcapRot 10 j.val p10_241r = reflectDrule
        (hubcapRot 10 (representative j.val) p10_241r)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_zero : checkDbound2 theRedpart rf10 (hubcapRot 10 0 p10_241r) 4 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_one : checkDbound2 theRedpart rf10 (hubcapRot 10 1 p10_241r) 5 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_four : checkDbound2 theRedpart rf10 (hubcapRot 10 4 p10_241r) 2 = true := by
  decide +kernel

/-- Bounds for every edge, transported from the three checked representatives. -/
theorem bounds (hred : RedpartSound theRedpart) (j : Fin 10) :
    ChargeBound (hubcapRot 10 j.val p10_241r) (bound j.val) := by
  obtain ⟨hr, hb, hp⟩ := representatives j
  rw [hb]
  have checked : ChargeBound (hubcapRot 10 (representative j.val) p10_241r)
      (bound (representative j.val)) := by
    rcases hr with hr | hr | hr
    · rw [hr]
      exact ChargeBound.of_check hred rf10 rfl check_zero
    · rw [hr]
      exact ChargeBound.of_check hred rf10 rfl check_one
    · rw [hr]
      exact ChargeBound.of_check hred rf10 rfl check_four
  rcases hp with hp | hp
  · rwa [hp]
  · rw [hp]
    apply ChargeBound.reflect (p := hubcapRot 10 (representative j.val) p10_241r)
      (b := bound (representative j.val))
    · simpa only [hubcapRot, Part.size_rot] using
        (show 0 < p10_241r.size by decide)
    · exact checked

/-- The three checked bounds close the same part as the reference hubcap. -/
theorem succeeds (hred : RedpartSound theRedpart) (p₀ : Part) :
    SucceedsIn p₀ p10_241r := by
  intro _
  apply ChargeBound.successful_of_bounds (n := 10) rfl (by decide) bound
  · intro j hj
    exact bounds hred ⟨j, hj⟩
  · decide +kernel

#print axioms succeeds

end FourColor.ReflectedHubcap
