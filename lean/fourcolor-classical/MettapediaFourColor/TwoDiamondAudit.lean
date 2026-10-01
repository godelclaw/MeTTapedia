import MettapediaFourColor.TwoDiamondSplitRepair
import MettapediaFourColor.TwoDiamondCompositionGSLT
import Lean.Util.CollectAxioms

/-! Audit of exact joint-tip semantics, embedded insertion and transferred repair.
Configuration 6's original base certificate is intentionally retained.
Configuration 3's independent certificate and complete theorem are forbidden. -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoDiamondBoundaryElimination.coloringEquiv,
      [``DiamondBoundaryElimination.eliminate, ``TwoDiamondBoundaryElimination.reconstruct]),
    (``TwoDiamondBoundaryElimination.context_iff, [``TwoDiamondBoundaryElimination.coloringEquiv]),
    (``TwoDiamondConfigurations.summaryTrace003,
      [``TwoDiamondConfigurations.numbered003, ``TwoDiamondConfigurations.planEquiv003]),
    (``TwoDiamondConfigurations.summaryTrace006,
      [``TwoDiamondConfigurations.numbered006, ``TwoDiamondConfigurations.planEquiv006]),
    (``TwoDiamondConfigurations.shared_tip_obstruction003, []),
    (``TwoDiamondSplitRepair.insert36, []),
    (``TwoDiamondSplitRepair.rotation36, []),
    (``TwoDiamondSplitRepair.boundary36, []),
    (``TwoDiamondSplitRepair.alternatives36,
      [``BoundaryTriangleSubdivision.alternativesEquiv]),
    (``TwoDiamondCompositionGSLT.every_coloring,
      [``TwoDiamondBoundaryElimination.coloringEquiv, ``TwoDiamondCompositionGSLT.witness]),
    (``TwoDiamondCompositionGSLT.viable_iff, [``TwoDiamondCompositionGSLT.every_coloring]),
    (``TwoDiamondSplitRepair.base_repair,
      [``Bulk.known_coclosure, ``Bulk.Cfg005.hgood, ``Bulk.Cfg005.hpairs]),
    (``TwoDiamondSplitRepair.reconstruct, [``BoundaryTriangleSubdivision.restrict]),
    (``TwoDiamondSplitRepair.transferred_repair,
      [``KempeBoundarySplit.repairs_collapse, ``TwoDiamondSplitRepair.reconstruct,
        ``TwoDiamondSplitRepair.base_repair]),
    (``TwoDiamondSplitRepair.reducible003,
      [``TwoDiamondSplitRepair.valid_contract, ``TwoDiamondSplitRepair.contract_proper,
        ``TwoDiamondSplitRepair.transferred_repair])]
  let forbidden : List Name := [
    `FourColor.Bulk.Cfg000, `FourColor.Bulk.Cfg001, `FourColor.Bulk.Cfg002,
    `FourColor.Bulk.Cfg003, `FourColor.fourColorTheorem,
    `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducible_block_0]
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
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Shared-tip diamond audit: {roots.length} roots; \
    {inspected.toList.length} declarations; configuration 3's original certificate absent."
