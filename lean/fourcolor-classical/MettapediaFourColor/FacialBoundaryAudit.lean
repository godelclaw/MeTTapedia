import MettapediaFourColor.FourTriangleCompletedOccurrence
import MettapediaFourColor.FanBoundaryScheme
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let geometric : List (Name × List Name) := [
    (``FacialBoundaryScheme.outer_seam, [``FacialStarCompletion.across_edge]),
    (``FacialBoundaryScheme.row_agrees, [``FacialBoundaryScheme.outer_seam]),
    (``FacialBoundaryScheme.hom, [``FacialBoundaryScheme.row_agrees]),
    (``FacialBoundaryScheme.full_turn, [``FacialBoundaryScheme.row_agrees]),
    (``FacialBoundaryScheme.ring_outside_core, [``FacialBoundaryScheme.around_injective]),
    (``FanBoundaryScheme.hom, [``FacialBoundaryScheme.hom]),
    (``FanBoundaryScheme.full_turn, [``FacialBoundaryScheme.full_turn]),
    (``FourTriangleCompletion.scheme, []),
    (``FourTriangleCompletion.hom, [``FacialBoundaryScheme.hom]),
    (``FourTriangleCompletion.full_turn, [``FacialBoundaryScheme.full_turn]),
    (``FourTriangleCompletion.ring_outside_core, [``FacialBoundaryScheme.ring_outside_core]),
    (``FourTriangleCompletedOccurrence.sourceIso, []),
    (``FourTriangleCompletedOccurrence.core_reading, []),
    (``FourTriangleCompletedOccurrence.boundary_preserved, []),
    (``FourTriangleCompletedOccurrence.boundary_alignment, []),
    (``FourTriangleCompletedOccurrence.source_turn, []),
    (``FourTriangleCompletedOccurrence.occurrence,
      [``FourTriangleCompletion.hom, ``FourTriangleCompletion.full_turn,
       ``FourTriangleCompletion.ring_outside_core]),
    (``ActualFourTrianglePatch.occurrence,
      [``FourTriangleRecognition.embedded, ``FourTriangleCompletedOccurrence.occurrence])]
  let repair : List (Name × List Name) := [
    (``ActualFourTrianglePatch.not_in_minimal,
      [``ActualFourTrianglePatch.occurrence, ``ActualDualContract.singleton_colorable,
       ``FourTriangleRepair.reference_repair, ``InjectiveEmbeddedRepair.colorable])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.DiamondProfileData,
    ``Bulk.Cfg032.hctr, ``Bulk.Cfg036.hctr]
  let mut all : NameSet := {}
  for (root, required) in geometric ++ repair do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      let permitted := repair.any (fun r => r.1 == root) &&
        ((`FourColor.Bulk.Cfg032).isPrefixOf name || (`FourColor.Bulk.Cfg036).isPrefixOf name)
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Facial boundary completion: {geometric.length + repair.length} roots; \
    {all.toList.length} declarations. One seam theorem supplies complete interfaces \
    for both chains and both four-triangle layouts. Four faces and six degrees in either layout \
    now imply actual strict reconstruction. The shared repair dispatcher retains \
    Cfg032/Cfg036; geometric roots use no rank certificates. The tripod reflection \
    preserves its full source; universal geometric supply remains open."
