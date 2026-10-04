import MettapediaFourColor.StripTwoPhaseReconstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripPuncturedExtension.relaxed_iff, [``StripPartialColouring.ValidExcept]),
    (``StripPuncturedExtension.terminal_iff, [``StripPuncturedExtension.relaxed_iff,
      ``StripResponseSummary.edges]),
    (``StripPuncturedExtension.direct_sound, [``StripPuncturedExtension.terminal_iff]),
    (``StripPuncturedExtension.reconstruct, [``StripPartialColouring.partial_valid]),
    (``StripTwoPhaseProgress.select, [``KempeIntervalMatching.possible]),
    (``StripTwoPhaseProgress.middle_one, [``StripPuncturedExtension.Direct]),
    (``StripTwoPhaseProgress.middle_two, [``StripPuncturedExtension.Direct]),
    (``StripTwoPhaseProgress.middle, [``KempeRetainedMatching.two_anchor_coclosure,
      ``StripPuncturedExtension.terminal_iff]),
    (``StripTwoPhaseProgress.first_one, [``StripTwoPhaseProgress.Ready]),
    (``StripTwoPhaseProgress.first_two, [``StripTwoPhaseProgress.Ready]),
    (``StripTwoPhaseProgress.progress, [``StripTwoPhaseProgress.middle,
      ``KempeRetainedMatching.two_anchor_coclosure,
      ``KempeChromogramMatching.recover_stable]),
    (``StripTwoPhaseProgress.compatible, [``StripTwoPhaseProgress.progress,
      ``GraphTraceAlignment.align, ``StripPuncturedExtension.reconstruct]),
    (``StripTwoPhaseProgress.disk_progress, [``StripTwoPhaseProgress.compatible,
      ``StripPhaseDisk.closed, ``PlanarGraphBoundaryClosure.rotation_closed])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.StripSpherePhase.whole_repair, `FourColor.StripPhaseObstruction.repairHistory]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-stage strip progress: {contracts.length} roots; {all.toList.length} declarations."
