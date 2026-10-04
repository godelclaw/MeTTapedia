import MettapediaFourColor.StripListTransport
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph.BoundaryListTransport

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``interpret_summary, []),
    (``transport, []),
    (``advance_comp, []),
    (``congruence, [``transport, ``interpret_summary]),
    (``StripListTransport.full_iff, [``StripChoiceLoops.attachments_complete,
      ``StripResponseSummary.attachments_complete, ``StripChoiceLoopRepair.complete_valid,
      ``StripSourceExtension.complete_valid]),
    (``StripListTransport.same_lists, []),
    (``StripListTransport.initial_fails, [``ColoringListPropagation.empty_refutes]),
    (``StripListTransport.changed_fails, [``ColoringListPropagation.empty_refutes]),
    (``StripListTransport.updated_lists, [``transport, ``interpret_summary]),
    (``StripListTransport.changed_guard, []),
    (``StripListTransport.changed_extends, [``TriangleStripLists.guard_colouring,
      ``ColoringListPropagation.forest_colouring, ``transport]),
    (``StripListTransport.source_distinguishes, [``StripListTransport.full_iff,
      ``StripListTransport.changed_fails, ``StripListTransport.changed_extends]),
    (``StripListTransport.no_list_only_transport, [``StripListTransport.same_lists,
      ``StripListTransport.source_distinguishes]),
    (``StripListTransport.refined_distinguishes, []),
    (``StripListTransport.same_chord, [``KempeMatchingChromogram.reconstruct,
      ``KempeIntervalRepair.switch_matches])]
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
  logInfo m!"Retained-cut list transport: {contracts.length} roots; \
    {all.toList.length} declarations."
