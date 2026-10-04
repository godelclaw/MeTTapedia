import MettapediaFourColor.StripChoiceEscape
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripChoiceBarrier.actual_iff, [``StripPartialColouring.partial_valid]),
    (``StripChoiceBarrier.score_map, [``StripChoiceBarrier.possible_map]),
    (``StripChoiceBarrier.base_profile, [``StripPuncturedExtension.r5]),
    (``StripChoiceBarrier.matchings_valid, [``KempeMatchingChromogram.Noncrossing]),
    (``StripChoiceBarrier.roots_cover, [``StripChoiceBarrier.mate]),
    (``StripChoiceBarrier.batches_match, [``KempeMatchingChromogram.gram]),
    (``StripChoiceBarrier.answer_barrier, [``StripChoiceBarrier.score]),
    (``StripChoiceBarrier.history_no_source_trace, [``StripChoiceBarrier.history_stays,
      ``StripChoiceBarrier.base_nonextension, ``StripResponseSummary.no_trace]),
    (``KempeAnchorSelection.pins_mate, [``KempeAnchorSelection.pins]),
    (``KempeAnchorSelection.feasible_mate, [``KempeMatchingChromogram.Noncrossing]),
    (``KempeAnchorSelection.feasible_reindex, [``KempeAnchorSelection.feasible]),
    (``KempeAnchorSelection.coclosure, [``KempeChromogramMatching.recover_stable,
      ``KempeRetainedMatching.possible_of_mate, ``KempeAnchorSelection.feasible_mate]),
    (``StripChoiceEscape.checked, [``KempeIntervalMatching.possible]),
    (``StripChoiceEscape.select, [``KempeAnchorSelection.feasible_reindex,
      ``StripChoiceEscape.selected_sound]),
    (``StripChoiceEscape.stages, [``KempeAnchorSelection.coclosure,
      ``StripSymbolicRepair.direct_coclosure]),
    (``StripChoiceEscape.repair, [``StripChoiceEscape.stages]),
    (``StripChoiceEscape.compatible, [``StripChoiceEscape.repair,
      ``GraphTraceAlignment.align, ``StripSourceExtension.complete_valid])]
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
  logInfo m!"Choice obstruction and repair: {contracts.length} roots; {all.toList.length} declarations."
