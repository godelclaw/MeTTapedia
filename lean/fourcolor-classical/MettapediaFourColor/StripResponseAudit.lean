import MettapediaFourColor.StripResponseSummary
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``StripResponseSummary.attachments_complete,
    ``StripResponseSummary.edges_complete, ``StripResponseSummary.terminal_iff,
    ``StripResponseSummary.valid_of_colouring, ``StripResponseSummary.no_trace,
    ``StripResponseSummary.mate_valid, ``StripResponseSummary.same_chord_update,
    ``StripResponseSummary.only_one_port, ``StripResponseSummary.retained_port_differs,
    ``StripResponseSummary.equal_relations, ``StripResponseSummary.empty_after_update,
    ``StripResponseSummary.extends_after_update, ``StripResponseSummary.fails_after_update,
    ``StripResponseSummary.not_update_congruence]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeIntervalMatching, `FourColor.StripIntervalRepair.rejection,
    `FourColor.StripIntervalRepair.source_repair, `FourColor.StripTwoRoundRepair.source_repair]
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
    if root == ``StripResponseSummary.not_update_congruence then
      for needed in [``StripResponseSummary.terminal_iff,
          ``StripResponseSummary.valid_of_colouring, ``StripResponseSummary.no_trace,
          ``StripResponseSummary.equal_relations, ``StripResponseSummary.empty_after_update,
          ``StripResponseSummary.extends_after_update, ``StripTwoRoundRepair.proper,
          ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    if root == ``StripResponseSummary.same_chord_update then
      for needed in [``KempeMatchingChromogram.reconstruct,
          ``KempeIntervalRepair.switch_matches, ``StripResponseSummary.mate_valid] do
        unless seen.contains needed do
          throwError m!"Missing component dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Strip response: {roots.length} roots; {all.toList.length} declarations."
