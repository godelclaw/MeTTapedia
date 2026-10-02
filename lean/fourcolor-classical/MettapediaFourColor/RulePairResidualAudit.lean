import MettapediaFourColor.ActualRulePairResidual
import MettapediaFourColor.RulePairResidualExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RulePairResidual.right_flanks, []),
    (``RulePairResidual.right_mixed, [``RulePairResidual.right_flanks]),
    (``RulePairResidual.right_mixed_of_check, [``RuleMatcher.check_iff,
      ``RulePairResidual.right_mixed]),
    (``ActualRulePairResidual.not_second_five,
      [``ActualRulePairDiamond.surviving_pair_degrees,
        ``RulePairResidual.right_mixed_of_check,
        ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller,
        ``DiamondProfileReducibility.repair001, ``DiamondProfileReducibility.repair002]),
    (``ActualRulePairResidual.second_degree_six,
      [``ActualRulePairResidual.not_second_five]),
    (``ActualRulePairResidual.forced_third,
      [``ActualRulePairResidual.second_degree_six,
        ``RulePairCharge.third_of_checks, ``RulePairCharge.net_three]),
    (``RulePairResidualExample.five_sender_mixed,
      [``RulePairBudgetExample.observations, ``RulePairResidual.right_mixed_of_check])]
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
  logInfo m!"Rerooted residual: {roots.length} roots; {all.toList.length} declarations. \
    A different edge of the same reading supplies the existing mixed-diamond reduction. \
    The surviving second sender has degree six. No original catalogue certificate, \
    D1774 repair, full Four Colour endpoint or global classification."
