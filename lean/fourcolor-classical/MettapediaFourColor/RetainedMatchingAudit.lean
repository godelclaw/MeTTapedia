import MettapediaFourColor.StripCoupledRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeChromogramMatching.recover_stable,
    ``KempeRetainedMatching.pin_mate, ``KempeRetainedMatching.possible_of_mate,
    ``KempeRetainedMatching.two_anchor_coclosure, ``StripCoupledRepair.active_anchors,
    ``StripCoupledRepair.select, ``StripCoupledRepair.one_direct,
    ``StripCoupledRepair.two_direct, ``StripCoupledRepair.direct_completion,
    ``StripCoupledRepair.completion_coclosure, ``StripCoupledRepair.source_repair,
    ``StripCoupledRepair.input_trace, ``StripCoupledRepair.input_empty,
    ``StripCoupledRepair.input_nonextension]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeFiniteDecoder, `FourColor.StripIntervalRepair.data,
    `FourColor.StripIntervalRepair.proper, `FourColor.StripIntervalRepair.source_repair,
    `FourColor.StripTwoRoundRepair.data, `FourColor.StripTwoRoundRepair.proper,
    `FourColor.StripTwoRoundRepair.source_repair, `FourColor.StripCriticalRepair.source_repair,
    `FourColor.StripSymbolicRepair.source_repair]
  let axioms := [``propext, ``Classical.choice, ``Quot.sound]
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
    if root == ``StripCoupledRepair.source_repair then
      for needed in [``KempeChromogramMatching.recover_stable,
          ``KempeChromogramMatching.pair_switch, ``chordsAux, ``matchg_flip,
          ``KempeRetainedMatching.two_anchor_coclosure,
          ``KempeIntervalMatching.possible_of_matching,
          ``StripPartialColouring.fill_iff, ``StripPartialColouring.reconstruct,
          ``StripSourceExtension.complete_valid, ``StripResponseSummary.terminal_iff,
          ``TriangleStripAnchors.input0099, ``KempeCoclosure] do
        unless seen.contains needed do
          throwError m!"Missing retained-exterior dependency in {root}: {needed}"
    if root == ``StripCoupledRepair.input_nonextension then
      for needed in [``StripResponseSummary.no_trace,
          ``StripResponseSummary.valid_of_colouring, ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing source obstruction dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless axioms.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Retained matching repair: {roots.length} roots; {all.toList.length} declarations."
