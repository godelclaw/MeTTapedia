import MettapediaFourColor.NearLinearChainExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``NearLinearChainData.input0004, []),
    (``NearLinearChainData.input0006, []),
    (``NearLinearChainData.stars_exact0004, []),
    (``NearLinearChainData.stars_exact0006, []),
    (``NearLinearChainData.degree_source0004, []),
    (``NearLinearChainData.degree_source0006, []),
    (``NearLinearChainData.boundary_source0004, []),
    (``NearLinearChainData.boundary_source0006, []),
    (``NearLinearChainData.numbered007, []),
    (``NearLinearChainData.faces007, []),
    (``NearLinearChainData.rotation007, []),
    (``NearLinearChainData.reducibilityTrace007, []),
    (``NearLinearChainData.insert46, []),
    (``NearLinearChainData.triangle46, []),
    (``NearLinearChainData.rotation46, []),
    (``NearLinearChainData.boundary46, []),
    (``NearLinearChainRepair.coverage_mask, []),
    (``NearLinearChainRepair.reference_repair,
      [``NearLinearChainRepair.coverage_mask,
        ``Bulk.Cfg006.hpairs]),
    (``NearLinearChainRepair.repair0006,
      [``NearLinearChainData.numbered007,
        ``NearLinearChainData.reducibilityTrace007]),
    (``NearLinearChainRepair.repair0004,
      [``NearLinearChainRepair.repair0006,
        ``BoundaryTriangleRepair.reconstruct,
        ``KempeBoundarySplit.repairs_collapse]),
    (``NearLinearChainRepair.reconstruct, [``NearLinearChainRepair.repair0004]),
    (``NearLinearChainExample.occurrence, []),
    (``NearLinearChainExample.injective, []),
    (``NearLinearChainExample.core_stars, []),
    (``NearLinearChainExample.covers, []),
    (``NearLinearChainExample.glue,
      [``PatchBoundaryGluing.reconstruct,
        ``NearLinearChainExample.covers]),
    (``NearLinearChainExample.repair_actual,
      [``NearLinearChainRepair.repair0004,
        ``NearLinearChainExample.glue,
        ``GraphTraceAlignment.align])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate]
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
      if forbidden.any (·.isPrefixOf name) || (name.toString.startsWith "FourColor.Bulk.Cfg" &&
          !(`FourColor.Bulk.Cfg006).isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Three-triangle chain: {roots.length} roots; {all.toList.length} declarations. \
    Configuration 7 supplies the only rank certificate; boundary subdivision \
    transfers its repair to D0004. Actual example reconstruction retains explicit \
    exterior hypotheses. No full Four Colour endpoint or global coverage."
