import MettapediaFourColor.TwoFiveWheelRepairGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoFiveWheelConstruction.numbered_eq, []),
    (``TwoFiveWheelConstruction.source_rotation, []),
    (``TwoFiveWheelConstruction.ringTrace_iff,
      [``TwoFiveWheelConstruction.source_graph,
       ``ConfigurationTable.Realization.forwardRingTrace]),
    (``TwoFiveWheelConstruction.embeddable, [``TwoFiveWheelConstruction.quiz_right]),
    (``TwoFiveWheelPreembedding.preembedding,
      [``TwoFiveWheelPreembedding.source_position, ``TwoFiveWheelPreembedding.source_arity,
       ``LocalPreembedding.of_radius2]),
    (``TwoFiveWheelPreembedding.disk_injective,
      [``TwoFiveWheelPreembedding.preembedding, ``TwoFiveWheelPreembedding.faithful]),
    (``TwoFiveWheelRepairGeometry.contract_endpoints, []),
    (``TwoFiveWheelRepairGeometry.valid_contract, [``KempeRepairContract.valid_singleton]),
    (``TwoFiveWheelRepairGeometry.construction_repair,
      [``TwoFiveWheelRepair.transfer, ``TwoFiveWheelConstruction.ringTrace_iff]),
    (``TwoFiveWheelRepairGeometry.colorable,
      [``TwoFiveWheelPreembedding.disk_injective, ``ActualDualContract.singleton_colorable,
       ``MinimalSingletonContract.one_zero, ``InjectiveEmbeddedRepair.colorable,
       ``TwoFiveWheelRepairGeometry.singleton_reducible]),
    (``TwoFiveWheelRepairGeometry.profile_excluded,
      [``TwoFiveWheelOccurrence.supplied, ``TwoFiveWheelRepairGeometry.not_in_minimal]),
    (``TwoFiveWheelRepairGeometry.second_high_neighbor,
      [``SecondFanWheelOccurrence.alternatives, ``D3009RepairGeometry.not_in_minimal,
       ``TwoFiveWheelRepairGeometry.not_in_minimal])]
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
  logInfo m!"Two-five wheel embedding: {roots.length} roots; {all.toList.length} declarations. \
    All six exact source constructions use one disk/reconstruction argument and \
    one source repair premise. The actual second fan supplies a high neighbour \
    after both wheel alternatives are excluded. Only standard axioms; \
    no wheel or configuration certificate and no complete Four Colour endpoint."
