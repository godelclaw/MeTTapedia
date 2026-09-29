import MettapediaFourColor.DiamondSplitRepair
import Lean.Util.FoldConsts

/-!
# Dependency audit of repair through boundary splitting

The generic law must be independent of catalogue instances. Its diamond
consumer must reconstruct actual graph colourings and use configuration 2's
certified repair. Configuration 1's certificate and the complete theorem are
excluded. No trust beyond the three standard axioms is permitted.
-/

open FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeBoundarySplit.closed, [``KempeBoundarySplit.match_split,
      ``KempeBoundarySplit.collapse_match, ``matchg_gramNeg]),
    (``KempeBoundarySplit.repairs_collapse, [``KempeBoundarySplit.closed,
      ``KempeBoundarySplit.coclosure_collapse]),
    (``DiamondSplitRepair.base_repair, [``Bulk.known_coclosure,
      ``Bulk.Cfg001.hgood, ``Bulk.Cfg001.hchoice, ``Bulk.Cfg001.hpairs,
      ``DiamondSplitRepair.base_coverage]),
    (``DiamondSplitRepair.reconstruct, [``DiamondInsertion.insert12,
      ``Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.restrict]),
    (``DiamondSplitRepair.transferred_repair, [``DiamondSplitRepair.base_repair,
      ``DiamondSplitRepair.reconstruct, ``KempeBoundarySplit.repairs_collapse,
      ``DiamondConfigurations.reducibilityTrace001,
      ``DiamondConfigurations.reducibilityTrace002]),
    (``DiamondSplitRepair.contract_proper, [``DiamondContract.contractTrace001,
      ``DiamondSplitRepair.boundary_edges]),
    (``DiamondSplitRepair.valid_contract, [``contract_ctreeP]),
    (``DiamondSplitRepair.reducible, [``DiamondSplitRepair.transferred_repair,
      ``DiamondSplitRepair.valid_contract, ``DiamondSplitRepair.contract_proper])]
  let forbidden : List Name := [`FourColor.Bulk.Cfg000, `FourColor.Bulk.Cfg003,
    `FourColor.kempeTree, `FourColor.kempeTreeNum, `FourColor.kempeTreeDepth,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Superseded certificate or complete theorem in {root}: {name}"
      if (`FourColor.KempeBoundarySplit).isPrefixOf root &&
          ([`FourColor.Bulk, `FourColor.DiamondConfigurations,
            `FourColor.DiamondContract].any (·.isPrefixOf name) || name == ``cfmap) then
        throwError m!"The general split law depends on a catalogue instance: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond split repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    configuration 2 retained as base, configuration 1 certificate absent."
