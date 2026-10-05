import MettapediaFourColor.BoundaryDistinction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.Cybernetics.DistinctionCalculus

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``BoundaryDistinction.answer_extension_iff,
      [``StripResponseSummary.terminal_iff, ``StripSourceExtension.colouring]),
    (``BoundaryDistinction.no_snapshot_prediction,
      [``BoundaryDistinction.snapshotFiber, ``StripResponseSummary.equal_relations]),
    (``BoundaryDistinction.snapshot_defect_lower_bound,
      [``BoundaryDistinction.snapshotFiber, ``Tolerance.ExpandsAtMost]),
    (``BoundaryDistinction.no_seam_prediction,
      [``CapRechoice.no_initial_extension, ``CapRechoice.repaired_outer,
        ``BoundaryDistinction.answer_extension_iff]),
    (``BoundaryDistinction.predictive_refinement_separates,
      [``BoundaryDistinction.snapshotFiber]),
    (``BoundaryDistinction.profile_update,
      [``PartitionedBoundary.observe_change]),
    (``BoundaryDistinction.profile_extension_iff,
      [``PartitionedBoundary.complete_observe, ``StripSourceExtension.colouring,
        ``StripResponseSummary.attachments_complete]),
    (``BoundaryDistinction.history_extension_iff,
      [``PartitionedBoundary.observe_run, ``BoundaryDistinction.profile_extension_iff]),
    (``BoundaryDistinction.profile_grade_zero,
      [``PartitionedBoundary.grade_zero, ``PartitionedBoundary.observe_change]),
    (``PartitionedBoundary.transport_comp, [``PartitionedBoundary.transport]),
    (``BoundaryDistinction.common_forgets_to_interval,
      [``PartitionedBoundary.common_refinement, ``PartitionedBoundary.observe_coarsen]),
    (``BoundaryDistinction.common_cap_update,
      [``CapRechoice.outer, ``PartitionedBoundary.change]),
    (``BoundaryDistinction.common_history_extension_iff,
      [``PartitionedBoundary.observe_run, ``BoundaryDistinction.source_extension_iff])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData]
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
  logInfo m!"Boundary distinctions: {contracts.length} roots; {all.toList.length} declarations."
