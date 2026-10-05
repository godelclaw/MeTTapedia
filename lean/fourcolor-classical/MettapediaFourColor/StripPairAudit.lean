import MettapediaFourColor.StripPairCompletion
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``AlternatingPairRepair.initially_blocked, [``AlternatingPairRepair.Fits]),
    (``AlternatingPairRepair.initial_trace, [``AlternatingPairRepair.readBoundary]),
    (``AlternatingPairRepair.release, [``AlternatingPairRepair.Fits]),
    (``AlternatingPairRepair.repair, [``KempeChromogramMatching.majority_coclosure,
      ``AlternatingPairRepair.release]),
    (``AlternatingPairRepair.compatible, [``AlternatingPairRepair.repair,
      ``GraphTraceAlignment.align]),
    (``AlternatingPairRepair.compatible_mapped, [``AlternatingPairRepair.compatible]),
    (``AlternatingPairRepair.long_matching, [``KempeMatchingChromogram.Noncrossing]),
    (``AlternatingPairRepair.long_switch_traces, [``AlternatingPairRepair.readBoundary]),
    (``AlternatingPairRepair.long_colours_fail, [``AlternatingPairRepair.Fits]),
    (``StripPairCompletion.ordered, [``StripFanProgram.ring6]),
    (``StripPairCompletion.valid, [``StripResponseSummary.ValidCore,
      ``AlternatingPairRepair.Fits]),
    (``StripPairCompletion.reconstruct, [``StripSourceExtension.colouring,
      ``StripPairCompletion.valid]),
    (``StripPairCompletion.from_program, [``StripPairCompletion.reconstruct,
      ``AlternatingPairRepair.compatible_mapped, ``StripFanProgram.closed6])]
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
  logInfo m!"Adjacent completion and one-component limit: {contracts.length} roots; \
    {all.toList.length} declarations."
