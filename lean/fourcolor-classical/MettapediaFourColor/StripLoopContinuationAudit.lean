import MettapediaFourColor.StripLoopContinuation
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeShortBlock.restrict_pair, []),
    (``KempeShortBlock.delete_pair, [``KempeShortBlock.restrict_pair,
      ``KempeShortBlock.skip_covers]),
    (``StripLoopMatching.coordinates, []),
    (``StripLoopMatching.select, [``KempeShortBlock.restrict_pair,
      ``KempeBalancedBlock.ear_or_nested,
      ``exists_adjacent_majority]),
    (``StripLoopMatching.coclosure, [``StripLoopMatching.select,
      ``KempeChromogramMatching.recover_stable]),
    (``StripLoopContinuation.direct_coclosure, [``TriangleStripLists.guard_colouring,
      ``ColoringListPropagation.forest_colouring, ``StripChoiceLoopRepair.complete_valid]),
    (``StripLoopContinuation.coordinates, []),
    (``StripLoopContinuation.ears_ready, []),
    (``StripLoopContinuation.nested_ready, []),
    (``StripLoopContinuation.loop_single, []),
    (``StripLoopContinuation.loop_paired, []),
    (``StripLoopContinuation.short_coordinates, []),
    (``StripLoopContinuation.short_ears, []),
    (``StripLoopContinuation.punctured_ready, []),
    (``StripLoopContinuation.stages, [``KempeBalancedBlock.coclosure,
      ``KempeShortBlock.coclosure, ``StripLoopMatching.coclosure,
      ``StripLoopContinuation.direct_coclosure]),
    (``StripLoopContinuation.repair, [``StripLoopContinuation.stages,
      ``StripChoiceLoopRepair.repair]),
    (``StripLoopContinuation.compatible, [``StripLoopContinuation.repair,
      ``GraphTraceAlignment.align])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
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
  logInfo m!"Composed loop continuation: {contracts.length} roots; \
    {all.toList.length} declarations."
