import MettapediaFourColor.StripContractionSupply
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripContractionSupply.edges_complete, [``TriangleStripAnchors.input0099]),
    (``StripContractionSupply.edge_valid, [``TriangleStripAnchors.input0099]),
    (``StripContractionSupply.collapse_surjective, [``StripContractionSupply.collapse]),
    (``StripContractionSupply.collapse_fibres, [``StripContractionSupply.collapse]),
    (``StripContractionSupply.colouring, [``StripContractionSupply.valid_on_source,
      ``SimpleGraph.map]),
    (``StripContractionSupply.boundary_values, [``StripContractionSupply.colouring,
      ``StripResponseSummary.port]),
    (``StripContractionSupply.no_extension, [``StripResponseSummary.r5]),
    (``StripContractionSupply.no_joint_stage, [``StripSixJointRepair.word]),
    (``StripContractionSupply.no_chain_stage, [``StripChainRepair.word]),
    (``StripContractionSupply.outside_existing_domain, [``StripResponseSummary.no_trace,
      ``StripSymbolicRepair.direct_sound, ``StripContractionSupply.no_joint_stage,
      ``StripContractionSupply.no_chain_stage]),
    (``StripContractionSupply.counterexample, [``StripResponseSummary.valid_of_colouring,
      ``StripResponseSummary.terminal_iff, ``StripContractionSupply.colouring,
      ``StripContractionSupply.outside_existing_domain]),
    (``StripContractionSupply.no_domain_supplier, [``StripContractionSupply.counterexample])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData,
    `FourColor.StripSixJointRepair.stages, `FourColor.StripChainRepair.stages]
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
  logInfo m!"Single-contraction boundary obstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
