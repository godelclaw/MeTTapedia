import MettapediaFourColor.RuleFanSevenCluster
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RuleFanSevenCluster.pair_exists,
      [``ActualRuleFanSupply.not_low_fan,
       ``D3009RepairGeometry.residual_high_neighbor,
       ``TwoFiveWheelRepairGeometry.second_high_neighbor,
       ``ActualSecondFanResidual.star_nonadjacent,
       ``Bulk.Cfg006.hpairs, ``DiamondProfileReducibility.repair002]),
    (``RuleFanSevenCluster.third_other_receiver, []),
    (``RuleFanSevenCluster.three_distinct, []),
    (``RuleFanSevenCluster.unique_or_third, [``LocalCoverageAssembly.ball_recenter]),
    (``RuleFanSevenCluster.path_or_triangle, [``MinimalExceptionalEmbedding.triangle_facial]),
    (``RuleFanSevenCluster.pair_support, [``LocalCoverageAssembly.ball_recenter]),
    (``RuleFanSevenCluster.triple_support, [``RuleFanSevenCluster.pair_support]),
    (``RuleFanSevenCluster.occurs_of_joint_laws,
      [``RuleFanSevenCluster.pair_exists, ``RuleFanSevenCluster.unique_or_third,
       ``RuleFanSevenCluster.path_or_triangle, ``RuleFanSevenCluster.triple_support])]
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
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" &&
           !(`FourColor.Bulk.Cfg006).isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Seven-centre fan supply: {roots.length} roots; {all.toList.length} declarations. \
    One retained source repair and existing diamond/chain reductions supply \
    an actual adjacent pair. Its unique-neighbour, induced-path and facial-triangle \
    alternatives retain radius-five views. Joint closing laws remain explicit. \
    Only standard axioms; configuration 7 and the shared diamond profile remain."
