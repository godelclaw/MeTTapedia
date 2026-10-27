import Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay
import Mettapedia.Languages.MeTTa.HE.StateFreeExecution

/-!
# HE state-free replay on LeaTTa's interpreter

The HE instance of the generic trajectory-replay boundary. One replay event is
one actual `interpretStack1` transition of LeaTTa's interpreter, and an existing
`StateFreeExecution.Certificate` makes that step world-preserving. It belongs
to the optional LeaTTa integration because the interpreter it replays is
LeaTTa's; the DAG-replay calibration instance stays in `ReplayInstances`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

/-! ## HE derivation-local state-free replay -/

namespace HE

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE.StateFreeExecution

/-- One HE replay event supplies the fuel and work item for an actual
`interpretStack1` transition. -/
abbrev Event := Nat × Item

/-- The HE event system exposes the real interpreter state transition.  It
does not use the V1 calibration's DAG nodes or certificate checking. -/
def eventSystem (env : MinEnv) : EventSystem St Event where
  Step := fun initial event final =>
    PLift (final = (interpretStack1 env event.1 initial event.2).2)
  step? := fun initial event =>
    some (interpretStack1 env event.1 initial event.2).2

theorem eventSystem_transitionAdequate (env : MinEnv) :
    TransitionAdequate (eventSystem env) := by
  intro initial event final
  simp [eventSystem, eq_comm]

/-- An existing HE state-free certificate makes a replayed interpreter step
world-preserving.  The transition remains an HE step, not a generic proof-DAG
step. -/
theorem replay_singleton_preservesWorld_of_certificate
    {env : MinEnv} {Inv : World -> Item -> Prop}
    (certificate : Certificate env Inv)
    (fuel : Nat) (initial : St) (item : Item)
    (reached : Inv initial.world item) :
    let final := (interpretStack1 env fuel initial item).2
    TrajectoryReplay.replay (eventSystem env) initial [(fuel, item)] =
        some final /\
      final.world = initial.world := by
  dsimp
  constructor
  · simp [TrajectoryReplay.replay, eventSystem]
  · exact certificate.preserves fuel initial item reached

/-- The genuine full-prelude finished-frame certificate instantiates the HE
side of the replay boundary. -/
theorem fullPrelude_finished_replay_preservesWorld (fuel : Nat) :
    let item : Item :=
      { stack := [{ atom := Atom.sym "a", fin := true }], bnd := [] }
    let final := (interpretStack1 fullPreludeEnv fuel St.init item).2
    TrajectoryReplay.replay (eventSystem fullPreludeEnv) St.init
        [(fuel, item)] = some final /\
      final.world = St.init.world := by
  dsimp
  apply replay_singleton_preservesWorld_of_certificate
    (finished_stateFreeExecution fullPreludeEnv)
  exact pureFinished_inv _

/-- The existing concrete mutation witness prevents the HE instance from
accepting every event as state-free. -/
theorem mutation_has_no_covering_certificate
    (Inv : World -> Item -> Prop)
    (certificate : Certificate fullPreludeEnv Inv) :
    Not (Inv St.init.world mutatingItem) :=
  no_certificate_covers_mutation Inv certificate

end HE

end Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.HE.fullPrelude_finished_replay_preservesWorld
