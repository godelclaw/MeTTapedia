import MettapediaFourColor.ActualRulePairBudget
import MettapediaFourColor.RulePairBudgetExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RulePairBudget.restrict, []),
    (``RulePairBudget.left_triangle_pattern, []),
    (``RulePairBudget.right_triangle_pattern, []),
    (``RulePairBudget.zero_of_five, [``RuleMatcher.check_iff]),
    (``RulePairBudget.one_of_left,
      [``RulePairBudget.restrict, ``RulePairBudget.left_triangle_pattern]),
    (``RulePairBudget.two_of_right,
      [``RulePairBudget.restrict, ``RulePairBudget.right_triangle_pattern]),
    (``RulePairBudget.first_four,
      [``RulePairBudget.zero_of_five, ``RulePairBudget.one_of_left,
        ``RulePairCharge.charge_lower, ``RulePairCharge.high_to_low_zero]),
    (``RulePairBudget.second_four,
      [``RulePairBudget.zero_of_five, ``RulePairBudget.two_of_right,
        ``RulePairCharge.charge_lower, ``RulePairCharge.high_to_low_zero]),
    (``RulePairBudget.distinct_senders, []),
    (``RulePairBudget.shared_candidates, [``RulePairDiamond.aligned]),
    (``RulePairBudget.joint_bound,
      [``RulePairBudget.first_four, ``RulePairBudget.second_four,
        ``RulePairBudget.distinct_senders, ``RulePairBudget.shared_candidates,
        ``RulePairCharge.third_of_checks, ``RulePairCharge.net_three]),
    (``RulePairBudget.joint_seven, [``RulePairBudget.joint_bound]),
    (``RulePairBudget.remainder_balance, []),
    (``RulePairBudget.flat_pair_remainder,
      [``RulePairBudget.joint_seven, ``RulePairBudget.remainder_balance]),
    (``ActualRulePairBudget.paired_budget,
      [``ActualRulePairDiamond.surviving_pair_degrees, ``RulePairBudget.joint_seven,
        ``DiamondProfileReducibility.repair001, ``DiamondProfileReducibility.repair002,
        ``SixPortTreeReplacement.Embedded.size_decrease,
        ``SixPortTreeReplacement.open_reconstruct_from_tree,
        ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller]),
    (``ActualRulePairBudget.flat_remainder,
      [``ActualRulePairDiamond.surviving_pair_degrees, ``RulePairBudget.flat_pair_remainder]),
    (``RulePairBudgetExample.observations, []),
    (``RulePairBudgetExample.six_branch,
      [``RulePairChargeExample.observations, ``RulePairBudget.joint_seven]),
    (``RulePairBudgetExample.five_branch,
      [``RulePairBudgetExample.observations, ``RulePairBudget.joint_seven]),
    (``RulePairBudgetExample.five_branch_eight,
      [``RulePairBudgetExample.observations, ``RulePairBudget.joint_bound])]
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
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Paired rule budget: {roots.length} roots; {all.toList.length} declarations. \
    Actual cyclic distinctness precedes addition of seven net units. Both sender degrees \
    have certified instances; the minimal-map consumer retains the two diamond repairs. \
    No original catalogue certificate, D1774 repair, full Four Colour endpoint or classification."
