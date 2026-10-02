import MettapediaFourColor.TwoFiveWheelColouring
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoFiveWheelData.insertion, []),
    (``TwoFiveWheelData.triangle, []),
    (``TwoFiveWheelData.star_edges, []),
    (``TwoFiveWheelData.core_stars, []),
    (``TwoFiveWheelData.degrees, []),
    (``TwoFiveWheelData.rotation, []),
    (``TwoFiveWheelData.source_boundary, []),
    (``TwoFiveWheelRepair.transfer,
      [``BoundaryTriangleRepair.repair, ``BoundaryRepairTransport.repairs,
       ``TwoFiveWheelData.insertion, ``TwoFiveWheelData.source_boundary]),
    (``TwoFiveWheelRepair.reconstruct, [``TwoFiveWheelRepair.transfer]),
    (``TwoFiveWheelColouring.source, []),
    (``TwoFiveWheelColouring.coloringEquiv, [``WheelColouring.coloringEquiv]),
    (``TwoFiveWheelColouring.two_sectors_iff, [``WheelColouringGSLT.split_iff]),
    (``TwoFiveWheelColouring.graphTrace_iff, [``TwoFiveWheelColouring.extends_iff]),
    (``TwoFiveWheelColouring.repaired_sectors,
      [``TwoFiveWheelRepair.transfer, ``WheelColouringGSLT.split_iff])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.Bulk.Cfg, `FourColor.Bulk.Hyb]
  let mut all : NameSet := {}
  for (root, required) in roots do
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
      if forbidden.any (·.isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-five wheel: {roots.length} roots; {all.toList.length} declarations. \
    One boundary-triangle collapse transfers the explicit source repair \
    to all six positions of the second five. Actual colourings and joint \
    exterior observations compose through two GSLT sectors. No new \
    configuration certificate or complete Four Colour endpoint is used."
