import MettapediaFourColor.D3009RepairGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``D3009Preembedding.source_position, [``D3009Boundary.fullSpoke]),
    (``D3009Preembedding.preembedding,
      [``D3009Preembedding.source_position, ``D3009Preembedding.source_arity]),
    (``D3009Preembedding.reading_injective, [``D3009Preembedding.endpoints_injective]),
    (``D3009Preembedding.disk_injective,
      [``D3009Preembedding.preembedding, ``D3009Preembedding.faithful]),
    (``D3009RepairGeometry.contract_endpoints, []),
    (``D3009RepairGeometry.valid_contract, [``KempeRepairContract.valid_singleton]),
    (``D3009RepairGeometry.construction_repair, [``D3009Construction.ringTrace_iff]),
    (``D3009RepairGeometry.colorable,
      [``D3009Preembedding.disk_injective, ``ActualDualContract.singleton_colorable,
       ``InjectiveEmbeddedRepair.colorable, ``D3009RepairGeometry.singleton_reducible]),
    (``D3009RepairGeometry.profile_excluded, [``ActualWheelOccurrence.occurrence]),
    (``D3009RepairGeometry.residual_high_neighbor,
      [``ActualWheelOccurrence.residual_occurrence, ``Bulk.Cfg006.hpairs])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData]
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
      let permitted := root == ``D3009RepairGeometry.residual_high_neighbor &&
        (`FourColor.Bulk.Cfg006).isPrefixOf name
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Wheel embedding and reconstruction: {roots.length} roots; \
    {all.toList.length} declarations. Full source stars preserve the same disk. \
    The singleton contract and actual strict-reduction consumer are checked. \
    The all-input wheel repair contract remains an explicit hypothesis. \
    Only the residual supply consumer retains configuration 7 and the shared profile."
