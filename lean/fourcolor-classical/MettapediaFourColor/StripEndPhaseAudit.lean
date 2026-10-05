import MettapediaFourColor.StripEndPhaseGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripEndPhase.good_iff, [``StripResponseSummary.r0, ``StripPartialColouring.avoid_spec]),
    (``StripEndPhase.release, [``StripEndPhase.repeated, ``StripEndPhase.middle_release]),
    (``StripEndPhase.trace_word, [``trace_eq_zipWith]),
    (``StripEndPhase.normalized_update, [``StripEndPhase.word_update]),
    (``StripEndPhase.proper_iff, [``StripEndPhase.boundary_edges]),
    (``StripEndPhase.reconstruct, [``StripPartialColouring.partial_valid,
      ``StripEndPhase.EndGraph]),
    (``StripEndPhase.repair, [``StripEndPhase.release, ``StripEndPhase.reconstruct,
      ``KempeChromogramMatching.recover, ``StripEndPhase.normalized_update]),
    (``StripEndPhase.compatible, [``StripEndPhase.repair, ``GraphTraceAlignment.align]),
    (``StripEndPhase.from_reading, [``StripEndPhase.compatible,
      ``PatchDisk.Reading.exterior_closed]),
    (``StripEndPhase.disk_consumer, [``StripEndPhase.compatible, ``StripPhaseDisk.closed])]
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
  logInfo m!"Uniform end phase and actual exterior consumers: {contracts.length} roots; \
    {all.toList.length} declarations."
