import MettapediaFourColor.StripDiamondPhaseGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripDiamondPhase.good_iff, [``StripResponseSummary.r1, ``StripDiamondPhase.Diamond]),
    (``StripDiamondPhase.classify, [``StripEndPhase.End, ``StripDiamondPhase.Pattern]),
    (``StripDiamondPhase.active, [``StripDiamondPhase.local_active]),
    (``StripDiamondPhase.release, [``StripDiamondPhase.pattern, ``StripDiamondPhase.local_release]),
    (``StripDiamondPhase.word_update, [``StripDiamondPhase.interval_boundary]),
    (``StripDiamondPhase.reconstruct, [``StripPartialColouring.partial_valid,
      ``StripDiamondPhase.DiamondGraph]),
    (``StripDiamondPhase.second, [``StripDiamondPhase.release, ``StripDiamondPhase.reconstruct,
      ``KempeChromogramMatching.recover, ``StripDiamondPhase.normalized_update]),
    (``StripDiamondPhase.left_of_source, [``StripPartialColouring.validExcept_of_source]),
    (``StripDiamondPhase.repair, [``StripEndPhase.repair, ``StripDiamondPhase.second,
      ``StripDiamondPhase.left_of_source]),
    (``StripDiamondPhase.compatible, [``StripDiamondPhase.repair, ``GraphTraceAlignment.align]),
    (``StripDiamondPhase.from_reading, [``StripDiamondPhase.compatible,
      ``PatchDisk.Reading.exterior_closed]),
    (``StripDiamondPhase.disk_consumer, [``StripDiamondPhase.compatible, ``StripPhaseDisk.closed])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData]
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
  logInfo m!"Two-stage diamond repair and geometric consumers: {contracts.length} roots; \
    {all.toList.length} declarations."
