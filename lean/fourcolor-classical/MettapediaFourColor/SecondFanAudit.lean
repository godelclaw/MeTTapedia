import MettapediaFourColor.SecondFanResidual
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``SecondFanResidual.second_tip, [``CyclicFanContinuation.tip_reverse]),
    (``SecondFanResidual.two_fives_exhaust, []),
    (``SecondFanResidual.extra_zero, []),
    (``ActualSecondFanResidual.star_nonadjacent,
      [``MinimalExceptionalEmbedding.triangle_facial]),
    (``ActualSecondFanResidual.profile_alternatives,
      [``SecondFanResidual.second_tip, ``SecondFanResidual.two_fives_exhaust,
       ``ExactCyclicCharge.exact_charge, ``ActualSecondFanResidual.star_nonadjacent,
       ``SecondFanResidual.extra_zero]),
    (``ActualSecondFanResidual.alternatives,
      [``ActualSecondFanResidual.profile_alternatives,
       ``D3009RepairGeometry.profile_excluded])]
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
  logInfo m!"Second fan: {roots.length} roots; {all.toList.length} declarations. \
    The geometric three-way classification assumes no wheel repair. \
    Only its two-way consumer requires the explicit full D3009 repair contract. \
    No configuration certificate or complete Four Colour endpoint is used."
