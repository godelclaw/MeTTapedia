import FourColor.Present7Defs

/-!
# One hubcap for a degree-seven region

The original presentation splits this part into sixteen hubcap checks and
one reducibility leaf. The same signed bound holds before those splits.
Seven kernel-checked spoke bounds close the whole part at once.

The charge rules and presentation are due to Robertson, Sanders, Seymour
and Thomas, formalized by Gonthier and Werner and ported by Chris Emery.
The existing reducibility predicate and all of its catalogue obligations
are retained. This is a replacement of repeated local checks.
-/

namespace FourColor.Sector7Region

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem m0 : checkDbound2 theRedpart rf7 (hubcapRot 7 0 p7_5836r) 4 = true := by decide +kernel
theorem m1 : checkDbound2 theRedpart rf7 (hubcapRot 7 1 p7_5836r) 5 = true := by decide +kernel
theorem m2 : checkDbound2 theRedpart rf7 (hubcapRot 7 2 p7_5836r) 3 = true := by decide +kernel
theorem m3 : checkDbound2 theRedpart rf7 (hubcapRot 7 3 p7_5836r) (-2) = true := by decide +kernel
theorem m4 : checkDbound2 theRedpart rf7 (hubcapRot 7 4 p7_5836r) (-1) = true := by decide +kernel
theorem m5 : checkDbound2 theRedpart rf7 (hubcapRot 7 5 p7_5836r) 0 = true := by decide +kernel
theorem m6 : checkDbound2 theRedpart rf7 (hubcapRot 7 6 p7_5836r) 1 = true := by decide +kernel

theorem fit :
    hubcapFit theRedpart rf7 p7_5836r
    (Hubcap.one 0 4 <| Hubcap.one 1 5 <| Hubcap.one 2 3 <| Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <| Hubcap.one 5 0 <| Hubcap.one 6 1 <| Hubcap.nil) = true := by
  simp [hubcapFit, m0, m1, m2, m3, m4, m5, m6]

/-- The entire part is closed by one hubcap with seven spoke bounds. -/
theorem step (hred : RedpartSound theRedpart) : SucceedsIn q7_5795 p7_5836r :=
  succeed_by_hubcap7 hred
    (Hubcap.one 0 4 <| Hubcap.one 1 5 <| Hubcap.one 2 3 <| Hubcap.one 3 (-2) <|
     Hubcap.one 4 (-1) <| Hubcap.one 5 0 <| Hubcap.one 6 1 <| Hubcap.nil)
    rfl (by decide +kernel) (by decide +kernel) fit

end FourColor.Sector7Region
