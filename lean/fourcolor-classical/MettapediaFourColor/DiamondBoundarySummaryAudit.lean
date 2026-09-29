import MettapediaFourColor.DiamondBoundarySummary
import Lean.Util.FoldConsts

/-!
# Audit of the common diamond elimination law

The generic witness equivalence must reach all three actual configuration
rings. The boundary law has no catalogue dependency; its concrete instances
use no reducibility certificate or complete colouring theorem.
-/

open FourColor Mettapedia.GraphTheory.FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DiamondBoundaryElimination.coloringEquiv,
      [``DiamondBoundaryElimination.reconstruct_eliminate]),
    (``DiamondBoundaryElimination.context_iff,
      [``DiamondBoundaryElimination.reconstruct, ``DiamondBoundaryElimination.eliminate]),
    (``DiamondBoundarySummary.fanEquiv, [``DiamondBoundaryElimination.coloringEquiv]),
    (``DiamondBoundarySummary.graph001Iso, [``DiamondConfigurations.graph001]),
    (``DiamondBoundarySummary.graph002Iso, [``DiamondConfigurations.graph002]),
    (``DiamondBoundarySummary.graph004Iso, [``DiamondConfigurations.graph004]),
    (``DiamondBoundarySummary.context_iff, [``DiamondBoundarySummary.planEquiv]),
    (``DiamondBoundarySummary.reference001, [``DiamondConfigurations.reducibilityTrace001,
      ``DiamondBoundarySummary.context_iff, ``DiamondBoundarySummary.ring001]),
    (``DiamondBoundarySummary.reference002, [``DiamondConfigurations.reducibilityTrace002,
      ``DiamondBoundarySummary.context_iff, ``DiamondBoundarySummary.ring002]),
    (``DiamondBoundarySummary.reference004, [``DiamondConfigurations.reducibilityTrace004,
      ``DiamondBoundarySummary.context_iff, ``DiamondBoundarySummary.ring004]),
    (``DiamondBoundarySummary.compatible_history, [``DiamondInsertionGSLT.every_coloring,
      ``DiamondBoundarySummary.planEquiv, ``DiamondConfigurations.coloring004])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
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
        throwError m!"Configuration certificate or complete theorem in {root}: {name}"
    if root == ``DiamondBoundaryElimination.coloringEquiv ||
        root == ``DiamondBoundarySummary.fanEquiv then
      for name in seen.toList do
        if (`FourColor.DiamondConfigurations).isPrefixOf name then
          throwError m!"The generic elimination law depends on a catalogue instance: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond boundary summary: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
