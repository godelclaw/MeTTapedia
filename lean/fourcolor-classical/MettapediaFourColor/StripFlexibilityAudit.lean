import MettapediaFourColor.StripFlexibilityBarrier
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripFlexibilityBarrier.fixed_complete, [``StripFlexibilityBarrier.fixed]),
    (``StripFlexibilityBarrier.matching_valid, [``KempeMatchingChromogram.Noncrossing,
      ``StripCriticalChain.boundary]),
    (``StripFlexibilityBarrier.chord_cover, [``StripFlexibilityBarrier.mate,
      ``StripFlexibilityBarrier.chord]),
    (``StripFlexibilityBarrier.initial_matches, [``KempeMatchingChromogram.reconstruct]),
    (``StripFlexibilityBarrier.batches_match, [``matchg, ``StripFlexibilityBarrier.batch]),
    (``StripFlexibilityBarrier.sizes_nonincrease, [``StripResponseSummary.relation,
      ``StripFlexibilityBarrier.interval]),
    (``StripFlexibilityBarrier.batch_nonextension, [``StripResponseSummary.no_trace,
      ``StripFlexibilityBarrier.sizes_nonincrease]),
    (``StripFlexibilityBarrier.no_greedy_score, [``StripFlexibilityBarrier.sizes_nonincrease]),
    (``StripFlexibilityBarrier.repair_despite_barrier, [``StripChainRepair.repair,
      ``StripFlexibilityBarrier.no_greedy_score, ``StripFlexibilityBarrier.batch_nonextension]),
    (``StripChainRepair.compatible_changed, [``StripChainRepair.repair,
      ``GraphTraceAlignment.align])]
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
  logInfo m!"Flexibility barrier and compatible repair: {contracts.length} roots; \
    {all.toList.length} declarations."
