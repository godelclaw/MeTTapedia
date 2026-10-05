import MettapediaFourColor.StripFanReconstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeFourFan.junction, [``KempeFourFan.Related]),
    (``KempeFourFan.transport_iff, [``KempeFourFan.Transport, ``KempeFourFan.Fan]),
    (``KempeFourFan.closed, [``KempeBoundarySplit.closed, ``KempeBoundaryMerge.closed]),
    (``KempeFourFan.prepare, [``KempeChromogramMatching.recover, ``KempeFourFan.Ready]),
    (``BoundaryFourFanRepair.trace_exact, [``BoundaryFourFanRepair.grow, ``KempeFourFan.Fan]),
    (``BoundaryFourFanRepair.closed, [``BoundaryFourFanRepair.trace_exact,
      ``KempeFourFan.closed]),
    (``BoundaryFourFanRepair.colourable, [``KempeFourFan.prepare,
      ``BoundaryFourFanRepair.extend]),
    (``BoundaryFourFanRepair.three_closed, [``BoundaryFanRepair.trace_exact,
      ``KempeBoundaryFan.closed]),
    (``StripFanProgram.closed7, [``BoundaryFourFanRepair.closed,
      ``BoundaryFourFanRepair.three_closed]),
    (``StripFanProgram.colourable, [``BoundaryFourFanRepair.colourable,
      ``BoundaryFourFanRepair.three_colourable]),
    (``StripFanReconstruction.attachment_adj, [``StripResponseSummary.attachments]),
    (``StripFanReconstruction.core_adj, [``StripResponseSummary.edges]),
    (``StripFanReconstruction.reconstruct, [``StripPartialColouring.partial_valid,
      ``StripFanReconstruction.Source]),
    (``StripFanReconstruction.compatible, [``StripFanProgram.colourable,
      ``StripFanReconstruction.reconstruct]),
    (``StripFanReconstruction.from_reading, [``StripFanReconstruction.compatible,
      ``PatchDisk.Reading.exterior_closed]),
    (``StripFanReconstruction.disk_consumer, [``StripFanReconstruction.compatible,
      ``StripPhaseDisk.closed])]
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
  logInfo m!"Seven-vertex construction and geometric reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
