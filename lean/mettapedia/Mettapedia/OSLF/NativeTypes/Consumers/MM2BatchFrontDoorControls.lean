import Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchControls

/-!
# Controls: the two-path MM2 join through the front door

The join's checkpoint completes within a grant of 78 (and not 77). Its system, asked through the front door with the
kernel evaluating the matcher:

- the captured store publishes the target, found by an exploration of one round among the checkpoint's 79 steps;
- a stale snapshot has no step, so it publishes nothing, by a closed region of the configuration alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoorControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
open Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchControls (target)
open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ResumableControls (checkpoint100)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

theorem completes : completesBy checkpoint100 78 = true := by decide +kernel

theorem not_earlier : completesBy checkpoint100 77 = false := by decide +kernel

/-- The front door's answer at a configuration of the join. -/
def answer (store : List Atom) (rounds : ℕ) : Answer :=
  ask ((system .sinkMajor .leaveInert target 78).unfolded (store, .matching checkpoint100)).observed.env [] systemLanguage
    2 (.possibly .any (.inRelation "published")) (pathPattern []) none rounds

theorem publishes_answer : answer checkpoint100.before 1 = .proved (.exploration 1) := by decide +kernel

/-- **The captured store publishes the target**, decided by the front door on the matcher's own steps. -/
theorem publishes : Inhabits .sinkMajor .leaveInert target (checkpoint100.before, .matching checkpoint100) :=
  (inhabits_iff_frontDoor .sinkMajor .leaveInert target ((completesBy_iff _ _).mp completes)).mpr
    (ask_proved publishes_answer)

def stale : List Atom := .symbol "changed" :: checkpoint100.before

theorem stale_answer : answer stale 2 = .refuted (.closedRegion 2) := by decide +kernel

/-- **A stale snapshot publishes nothing.** -/
theorem stale_publishes_nothing : ¬ Inhabits .sinkMajor .leaveInert target (stale, .matching checkpoint100) :=
  fun inhabits => ask_refuted stale_answer
    ((inhabits_iff_frontDoor .sinkMajor .leaveInert target ((completesBy_iff _ _).mp completes)).mp inhabits)

end Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoorControls
