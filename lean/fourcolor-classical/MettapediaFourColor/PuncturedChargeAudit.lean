import MettapediaFourColor.PuncturedChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let geometric : List (Name × List Name) := [
    (``LocalCyclicRules.local_tip_rules, []),
    (``LocalCyclicRules.basic_iff, [``LocalCyclicRules.local_tip_rules]),
    (``ExactCyclicCharge.basic_iff, [``LocalCyclicRules.basic_iff]),
    (``PuncturedCyclicCharge.edge_exact, [``LocalCyclicRules.basic_iff]),
    (``PuncturedCyclicCharge.exact_charge, [``PuncturedCyclicCharge.edge_exact]),
    (``PuncturedCyclicCharge.unique_boundary, []),
    (``PuncturedCyclicCharge.flat_unique_seven,
      [``PuncturedCyclicCharge.exact_charge, ``PuncturedCyclicCharge.unique_boundary]),
    (``PuncturedPairCharge.neighbor_lower, [``ActualRuleFanSupply.degree_five]),
    (``PuncturedPairCharge.first_budget, [``PuncturedCyclicCharge.flat_unique_seven]),
    (``PuncturedPairCharge.second_budget, [``PuncturedCyclicCharge.exact_charge]),
    (``PuncturedPairCharge.isolated_pair_budget,
      [``PuncturedPairCharge.first_budget, ``PuncturedPairCharge.second_budget,
       ``NearLinearCharge.net_reverse]),
    (``PuncturedChargeExample.observations, []),
    (``PuncturedChargeExample.charges,
      [``PuncturedCyclicCharge.exact_charge, ``PuncturedCyclicCharge.unique_boundary,
       ``PuncturedChargeExample.observations])]
  let repair : List (Name × List Name) := [
    (``PuncturedPairCharge.tip_ne_five,
      [``LocalCyclicRules.basic_iff, ``ActualJointTripodRuleSupply.not_checks,
       ``ActualDualContract.singleton_colorable, ``FourTriangleRepair.reference_repair,
       ``InjectiveEmbeddedRepair.colorable])]
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
  logInfo m!"Exact charge with high boundary: {geometric.length + repair.length} roots; \
    {all.toList.length} declarations. Low-neighbour contributions retain their \
    adjacent guards; high-edge exchanges stay signed and cancel across an isolated pair. \
    A 5-6-6-5 rim excludes a five-tip through actual tripod reconstruction. \
    Only this repair root retains Cfg032/Cfg036. Joint coverage remains open."
