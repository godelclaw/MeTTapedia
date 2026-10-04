import MettapediaFourColor.StripSpineFibre
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``StripPartialColouring.avoid_spec, ``StripPartialColouring.spine_valid,
    ``StripPartialColouring.partial_valid, ``StripPartialColouring.sourceSpine,
    ``StripPartialColouring.sourceSpine_boundary, ``StripPartialColouring.validExcept_of_source,
    ``StripPartialColouring.fill_iff, ``StripPartialColouring.reconstruct,
    ``StripPartialColouring.example_proper, ``StripPartialColouring.example_lists,
    ``StripPartialColouring.three_obstructions, ``StripPartialColouring.three_holes_necessary,
    ``StripPartialColouring.source_three_holes, ``StripPartialColouring.sharp_three_holes,
    ``StripSpineFibre.hidden_forest, ``StripSpineFibre.fibres_connected,
    ``StripSpineFibre.canonical_reachable]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripIntervalRepair.data, `FourColor.StripIntervalRepair.proper,
    `FourColor.StripIntervalRepair.source_repair, `FourColor.StripTwoRoundRepair.data,
    `FourColor.StripTwoRoundRepair.proper, `FourColor.StripTwoRoundRepair.source_repair]
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
    if root == ``StripPartialColouring.source_three_holes then
      for needed in [``StripResponseSummary.attachments_complete,
          ``StripResponseSummary.edges_complete, ``TriangleStripAnchors.input0099,
          ``StripPartialColouring.three_obstructions,
          ``StripPartialColouring.validExcept_of_source] do
        unless seen.contains needed do
          throwError m!"Missing actual-source dependency in {root}: {needed}"
    if root == ``StripPartialColouring.reconstruct then
      for needed in [``StripPartialColouring.fill_iff, ``StripSourceExtension.complete_valid,
          ``StripResponseSummary.terminal_iff, ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing reconstruction dependency in {root}: {needed}"
    if root == ``StripSpineFibre.canonical_reachable then
      for needed in [``SimpleGraph.KempeForestFibre.fibre_path,
          ``SimpleGraph.KempeForestFibre.list_connected,
          ``SimpleGraph.KempeTriangleAnchors.acyclic_of_unique_later,
          ``StripPartialColouring.sourceSpine, ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing physical-history dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Partial source colourings: {roots.length} roots; {all.toList.length} declarations."
