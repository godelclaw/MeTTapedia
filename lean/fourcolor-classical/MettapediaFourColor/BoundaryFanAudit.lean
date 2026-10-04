import MettapediaFourColor.StripParentFanExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeBoundaryFan.related_junction,
    ``KempeBoundaryFan.transport_iff, ``KempeBoundaryFan.closed,
    ``KempeBoundaryFan.repair, ``KempeBoundaryFan.repairs,
    ``BoundaryFanRepair.trace_exact, ``BoundaryFanRepair.repair,
    ``StripParentFan.sourceIso, ``StripParentFan.path_edges,
    ``StripParentFan.boundary, ``StripParentFan.parent_boundary,
    ``StripParentFan.source_trace, ``StripParentFan.source_repair,
    ``StripParentFanExample.proper, ``StripParentFanExample.answer_witness,
    ``StripParentFanExample.parent_repair, ``StripParentFanExample.source_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
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
    let required := if root == ``KempeBoundaryFan.closed then
        [``KempeBoundarySplit.closed, ``KempeBoundaryMerge.closed]
      else if root == ``StripParentFanExample.source_repair then
        [``StripParentFanExample.parent_repair, ``KempeChordExchange.answer_exists,
         ``StripParentFan.sourceIso, ``StripParentFan.boundary,
         ``BoundaryFanRepair.trace_exact, ``KempeBoundaryFan.repair,
         ``TriangleStripAnchors.input0099]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Boundary fan transport: {roots.length} roots; {all.toList.length} declarations."
