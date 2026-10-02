import MettapediaFourColor.ExactChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ExactCyclicCharge.basic_iff, [``CyclicFanContinuation.tip_reverse]),
    (``ExactCyclicCharge.low_sender_rules, []),
    (``ExactCyclicCharge.edge_exact,
      [``ExactCyclicCharge.basic_iff, ``ExactCyclicCharge.low_sender_rules,
       ``RuleMatcher.check_iff]),
    (``ExactCyclicCharge.exact_charge, [``ExactCyclicCharge.edge_exact]),
    (``ExactCyclicCharge.two_fives, []),
    (``ExactCyclicCharge.no_two_fives, [``ExactCyclicCharge.two_fives]),
    (``ExactCyclicCharge.residual_eq, [``ExactCyclicCharge.no_two_fives]),
    (``ExactCyclicCharge.five_count_one, []),
    (``ExactCyclicCharge.flat_seven_cases,
      [``ExactCyclicCharge.exact_charge, ``ExactCyclicCharge.residual_eq,
       ``ExactCyclicCharge.five_count_one]),
    (``ExactCyclicCharge.residual_zero_iff, []),
    (``ExactFanResidual.alternatives,
      [``ExactCyclicCharge.flat_seven_cases, ``ActualExtraChargeReduction.not_occurrence,
       ``FanBoundaryScheme.hom, ``Bulk.Cfg006.hpairs]),
    (``ExactChargeExample.eight_charge, [``ExactCyclicCharge.exact_charge]),
    (``ExactChargeExample.seven_charge, [``ExactCyclicCharge.exact_charge])]
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
      let permitted := root == ``ExactFanResidual.alternatives &&
        (`FourColor.Bulk.Cfg006).isPrefixOf name
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exact cyclic charge: {roots.length} roots; {all.toList.length} declarations. \
    All incoming rule types are accounted for. The single-five branch has two exact budgets. \
    Only the actual-map consumer retains configuration 7 and the shared profile. \
    Both residual budgets still require geometric closure."
