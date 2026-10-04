import MettapediaFourColor.StripSymbolicRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

run_cmd do
  let env ← getEnv
  let roots := [``KempeChordExchange.coclosure_of_answers,
    ``StripSourceExtension.complete_valid, ``StripSourceExtension.graphTrace,
    ``StripSourceExtension.terminal_iff_graphTrace, ``StripSymbolicRepair.guard_ear,
    ``StripSymbolicRepair.classify, ``StripSymbolicRepair.coordinates,
    ``StripSymbolicRepair.order, ``StripSymbolicRepair.direct_pairs,
    ``StripSymbolicRepair.majority_answer, ``StripSymbolicRepair.majority_coclosure,
    ``StripSymbolicRepair.source_repair, ``StripSymbolicRepair.residual_continuation,
    ``StripSymbolicRepair.residual_repair, ``StripSymbolicRepair.guarded_repair,
    ``StripSymbolicRepair.previous_counterexample_excluded]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeIntervalMatching, `FourColor.StripIntervalRepair.data,
    `FourColor.StripIntervalRepair.proper, `FourColor.StripIntervalRepair.source_repair,
    `FourColor.StripTwoRoundRepair.data, `FourColor.StripTwoRoundRepair.proper,
    `FourColor.StripTwoRoundRepair.source_repair]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : NameSet := {}
  for root in roots do
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
    if root == ``StripSymbolicRepair.guarded_repair then
      for legacy in [`FourColor.KempeFiniteDecoder.parses,
          `FourColor.StripSymbolicRepair.decode_check,
          `FourColor.StripSymbolicRepair.mate, `FourColor.StripSymbolicRepair.mates_valid] do
        if seen.contains legacy then
          throwError m!"Legacy inverse-layout dependency in {root}: {legacy}"
      for needed in [``exists_adjacent_majority,
          ``KempeChordExchange.coclosure_of_answers, ``KempeChordExchange.answer_exists,
          ``StripSourceExtension.colouring, ``StripSourceExtension.complete_valid,
          ``StripResponseSummary.terminal_iff, ``TriangleStripAnchors.input0099,
          ``StripSymbolicRepair.direct_pairs, ``KempeChromogramMatching.recover,
          ``StripSymbolicRepair.initial_answers, ``StripSymbolicRepair.residual_answers,
          ``StripSymbolicRepair.residual_first, ``StripSymbolicRepair.classify,
          ``KempeCoclosure] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Symbolic strip: {roots.length} roots; {all.toList.length} declarations."
