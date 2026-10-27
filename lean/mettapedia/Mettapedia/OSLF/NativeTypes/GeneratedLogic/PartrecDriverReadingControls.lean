import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.Runtime.Controls

/-!
# Controls: the partial-recursive machine through both front doors

The runtime installs the authored machine two ways: through the local profile (`localMachine_eq`) and through the
machine's own driver (`machine_eq`). Both are read faithfully in the machine's reference structure
(`PartrecReading.localReading`, `PartrecReading.driverReading`), so each decided runtime verdict about a query is the
truth of the query's closed generated formula, and the generated front door, evaluated by the kernel, decides that
formula. The two front doors agree at every budget (`FrontDoorAgreement.Agrees`):

| query | request | answer |
|---|---|---|
| built by `Normal` | `Normal` | yes |
| built by `Ret` | `Normal` | no |
| some step reaches a `Ret` | `Normal` | yes |
| some step reaches a `Halt` | `Normal` | no |
| some two steps reach a `Halt` | `Normal` | yes |
| every step reaches a `Ret` | `Normal` | yes |
| every step reaches a `Halt` | `Normal` | no |
| some step | `Halt` | no |
| every step reaches `⊥` | `Halt` | yes |
| built by `Normal` | `Halt` | no |

At budget zero the runtime suspends "some step reaches a `Ret`"; the generated front door answers yes, which more
budget gives the runtime too.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecReading.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Driver)
open Mettapedia.Languages.PartrecMachine (partrecMachine)
open Mettapedia.OSLF.NativeTypes.Runtime.Controls (normal halt)
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls (source_admitted stopped_admitted)

/-! ## The installed machines -/

/-- The machine the runtime installs through the local profile. -/
def localInstalled : Installed :=
  Mettapedia.OSLF.NativeTypes.Runtime.Local.installedLocal generated [] (.base "Cfg") foundation equationFree generic mask

theorem localMachine_eq : Mettapedia.OSLF.NativeTypes.Runtime.Controls.localMachine = .ok localInstalled := by
  unfold Mettapedia.OSLF.NativeTypes.Runtime.Controls.localMachine Mettapedia.OSLF.NativeTypes.Executable.generate
  dsimp only
  split_ifs with complete equations checked
  · rfl
  · exact absurd generic checked
  · exact absurd equationFree equations
  · exact absurd foundation complete

/-- The machine the runtime installs through its own driver. -/
def machineInstalled : Installed := Mettapedia.OSLF.NativeTypes.Runtime.Local.partrec {} []

theorem machine_eq :
    Mettapedia.OSLF.NativeTypes.Executable.generate Mettapedia.OSLF.NativeTypes.Runtime.Controls.machine =
      .ok machineInstalled :=
  Mettapedia.OSLF.NativeTypes.Executable.generate_originalMachine {} []

/-! ## Both front doors -/

open FrontDoorAgreement (frontDoor Agrees agrees_of_frontDoor)

/-- The local profile's reading. -/
abbrev localRead := localReading.reading (kindOf := fun _ => .hashBag)

/-- The machine's own driver's reading. -/
abbrev machineRead := (driverReading {} fun _ => rfl).reading (kindOf := fun _ => .hashBag)

/-- Through the local profile. -/
theorem local_agrees {query : Query} {raw : Pattern}
    (admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] raw) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor localRead [] 2 query raw rounds = some answer) : Agrees localInstalled query raw answer :=
  have inside : Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan [] (.base "Cfg") raw := by
    rw [samePlan]
    exact admitted
  agrees_of_frontDoor localInstalled localRead localReading_covered ⟨raw, inside, rfl⟩ inside formsFor_none answered

/-- Through the machine's own driver. -/
theorem machine_agrees {query : Query} {raw : Pattern}
    (admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] raw) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor machineRead [] 2 query raw rounds = some answer) :
    Agrees machineInstalled query raw answer :=
  agrees_of_frontDoor machineInstalled machineRead (fun _ _ _ => trivial) ⟨raw, admitted, rfl⟩ admitted
    formsFor_none answered

/-! ## The runtime's controls, through the local profile -/

theorem local_normal : Agrees localInstalled (.constructor "Normal") normal true :=
  local_agrees source_admitted (rounds := 4) (by decide +kernel)

theorem local_ret : Agrees localInstalled (.possibility (.constructor "Ret")) normal true :=
  local_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem local_halt : Agrees localInstalled (.possibility (.constructor "Halt")) normal false :=
  local_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem local_every_ret : Agrees localInstalled (.outgoingUniversal (.constructor "Ret")) normal true :=
  local_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem local_stopped : Agrees localInstalled (.possibility .top) halt false :=
  local_agrees stopped_admitted (rounds := 4) (by decide +kernel)

theorem local_stopped_every : Agrees localInstalled (.outgoingUniversal .bottom) halt true :=
  local_agrees stopped_admitted (rounds := 4) (by decide +kernel)

/-! ## The runtime's controls, through the machine's own driver -/

theorem machine_normal : Agrees machineInstalled (.constructor "Normal") normal true :=
  machine_agrees source_admitted (rounds := 4) (by decide +kernel)

theorem machine_not_ret : Agrees machineInstalled (.constructor "Ret") normal false :=
  machine_agrees source_admitted (rounds := 4) (by decide +kernel)

theorem machine_ret : Agrees machineInstalled (.possibility (.constructor "Ret")) normal true :=
  machine_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem machine_halt : Agrees machineInstalled (.possibility (.constructor "Halt")) normal false :=
  machine_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem machine_two_halt : Agrees machineInstalled (.possibility (.possibility (.constructor "Halt"))) normal true :=
  machine_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem machine_every_ret : Agrees machineInstalled (.outgoingUniversal (.constructor "Ret")) normal true :=
  machine_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem machine_every_halt : Agrees machineInstalled (.outgoingUniversal (.constructor "Halt")) normal false :=
  machine_agrees source_admitted (rounds := 8) (by decide +kernel)

theorem machine_stopped : Agrees machineInstalled (.possibility .top) halt false :=
  machine_agrees stopped_admitted (rounds := 4) (by decide +kernel)

theorem machine_stopped_every : Agrees machineInstalled (.outgoingUniversal .bottom) halt true :=
  machine_agrees stopped_admitted (rounds := 4) (by decide +kernel)

theorem machine_stopped_not_normal : Agrees machineInstalled (.constructor "Normal") halt false :=
  machine_agrees stopped_admitted (rounds := 4) (by decide +kernel)

/-- **The suspended verdict**: at budget zero the runtime suspends; the generated front door answers yes. -/
theorem machine_ret_front_door :
    frontDoor machineRead [] 2 (.possibility (.constructor "Ret")) normal 8 = some true := by
  decide +kernel

#guard Mettapedia.OSLF.NativeTypes.Runtime.Controls.observe Mettapedia.OSLF.NativeTypes.Runtime.Controls.machine
  (.possibility (.constructor "Ret")) normal 0 == .ok Mettapedia.OSLF.NativeTypes.Runtime.Controls.pending

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecReading.Controls
