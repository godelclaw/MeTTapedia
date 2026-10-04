import MettapediaFourColor.StripChoiceLoopRepair
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``ColoringListPropagation.forces_sound, []),
    (``ColoringListPropagation.path_forces, [``ColoringListPropagation.forces_sound]),
    (``StripChoiceLoops.attachments_complete, []),
    (``StripChoiceLoops.supported, []),
    (``StripChoiceLoops.no_stable_colouring, [``ColoringListPropagation.path_forces]),
    (``StripChoiceLoops.no_source, [``ColoringListPropagation.path_forces,
      ``ColoringListPropagation.run_sound, ``StripChoiceLoops.attachments_complete]),
    (``StripChoiceLoops.support_not_sufficient, [``StripChoiceLoops.no_stable_colouring,
      ``StripChoiceLoops.supported, ``StripChoiceLoops.nonempty]),
    (``StripChoiceLoopRepair.complete_valid, [``StripChoiceLoops.attachments_complete]),
    (``StripChoiceLoopRepair.guard_trace, [``TriangleStripLists.guard_colouring,
      ``ColoringListPropagation.forest_colouring, ``StripChoiceLoopRepair.complete_valid]),
    (``StripChoiceLoopRepair.guarded_answers, []),
    (``StripChoiceLoopRepair.repair, [``KempeChromogramMatching.majority_coclosure,
      ``StripChoiceLoopRepair.guard_trace, ``StripChoiceLoopRepair.guarded_answers]),
    (``StripChoiceLoopRepair.compatible, [``StripChoiceLoopRepair.repair,
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
  logInfo m!"Choice loops and forest repair: {contracts.length} roots; \
    {all.toList.length} declarations."
