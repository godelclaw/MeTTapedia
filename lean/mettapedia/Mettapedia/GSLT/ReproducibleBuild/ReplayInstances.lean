import Mettapedia.GSLT.ReproducibleBuild.HattaProfile
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.Calibration.PeTTaChainerDAGReplayV1
import Mettapedia.GSLT.Dynamics.AnswerDistinctionConservation

/-!
# CeTTa DAG-replay calibration instance

This file connects the pinned PeTTaChainer DAG replay to the generic trajectory
boundary. The calibration instance reuses the actual DAG-node replay machine.
HE's derivation-local state-free execution is a different evidence discipline;
its instance replays LeaTTa's interpreter, so it lives in
`ReproducibleBuild.LeaTTaReplayInstance`, in the optional LeaTTa integration.
The generic occurrence-erasure obstruction is reused as the collapsed
receipt control rather than re-proved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

/-! ## CeTTa PeTTaChainer DAG-replay V1 calibration -/

namespace CeTTaDAGCalibrationV1

open Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.Calibration.PeTTaChainerDAGReplayV1

/-- The generic event system whose states and events are exactly those of the
existing V1 calibration DAG replay engine. -/
def dagEventSystem : EventSystem (List CheckedNode) DAGNode where
  Step := fun initial node final => PLift (replayNode initial node = some final)
  step? := replayNode

theorem dagEventSystem_transitionAdequate :
    TransitionAdequate dagEventSystem := by
  intro initial node final
  constructor
  · exact fun replayed => ⟨⟨replayed⟩⟩
  · rintro ⟨⟨replayed⟩⟩
    exact replayed

/-- Generic trajectory replay is definitionally the existing V1 DAG-node
replay loop.  This is an interface theorem, not a replacement implementation. -/
theorem replay_eq_replayNodes (environment : List CheckedNode)
    (nodes : List DAGNode) :
    TrajectoryReplay.replay dagEventSystem environment nodes =
      replayNodes environment nodes := by
  induction nodes generalizing environment with
  | nil => rfl
  | cons node nodes ih =>
      simp only [TrajectoryReplay.replay, replayNodes, dagEventSystem]
      cases replayed : replayNode environment node with
      | none => rfl
      | some next =>
          simpa [dagEventSystem] using ih next

/-- Successful V1 node replay yields a proof-relevant
trajectory through the generic transition boundary. -/
theorem replayNodes_eq_some_iff_trajectory
    (environment : List CheckedNode) (nodes : List DAGNode)
    (final : List CheckedNode) :
    replayNodes environment nodes = some final <->
      Nonempty (Trajectory dagEventSystem.Step environment nodes final) := by
  rw [<- replay_eq_replayNodes]
  exact replay_eq_some_iff_trajectory dagEventSystem
    dagEventSystem_transitionAdequate environment nodes final

end CeTTaDAGCalibrationV1

/-! ## Receipt-collapse control -/

/-- Reuse the generic multiplicity collision: replacing an
occurrence multiset by its support cannot preserve exact receipt distinctions. -/
theorem occurrenceSupportErasure_not_exactReceiptReplay :
    Not (Mettapedia.Cybernetics.Distinction.Conserves
      (Mettapedia.Cybernetics.Distinction.inequality (Multiset Unit))
      (Mettapedia.Cybernetics.Distinction.inequality (Finset Unit))
      (@Mettapedia.GSLT.Dynamics.AnswerEffects.bagToSupport.{0}.map Unit)) := by
  intro conserves
  obtain ⟨different, collision⟩ :=
    Mettapedia.GSLT.Dynamics.AnswerEffects.bagToSupport_multiplicity_collision
  exact conserves {()} {(), ()} different collision

end Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.CeTTaDAGCalibrationV1.replayNodes_eq_some_iff_trajectory
#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.occurrenceSupportErasure_not_exactReceiptReplay
