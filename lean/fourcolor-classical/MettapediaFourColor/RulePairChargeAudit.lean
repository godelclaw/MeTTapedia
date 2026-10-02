import MettapediaFourColor.ActualRulePairCharge
import MettapediaFourColor.RulePairChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RulePairCharge.glue, [``RuleMatcher.occurrenceOfFits]),
    (``RulePairCharge.pair_cover, []),
    (``RulePairCharge.joined, [``RulePairCharge.glue, ``RulePairCharge.pair_cover]),
    (``RulePairCharge.third_of_checks,
      [``RulePairCharge.joined, ``RulePairDiamond.identified_corner,
        ``RulePairDiamond.aligned, ``RuleMatcher.check_iff]),
    (``RulePairCharge.two_of_nine, [``RuleMatcher.check_iff]),
    (``RulePairCharge.charge_lower, []),
    (``RulePairCharge.three_of_checks,
      [``RulePairCharge.two_of_nine, ``RulePairCharge.charge_lower]),
    (``RulePairCharge.endpoint_separation, []),
    (``RulePairCharge.high_to_low_zero, [``RulePairCharge.endpoint_separation]),
    (``RulePairCharge.net_three,
      [``RulePairCharge.three_of_checks, ``RulePairCharge.high_to_low_zero]),
    (``RulePairCharge.flat_remainder, [``RulePairCharge.net_three]),
    (``RulePairCharge.reduction_or_charge,
      [``RulePairDiamond.pair_alternatives, ``RulePairCharge.third_of_checks,
        ``RulePairCharge.three_of_checks]),
    (``ActualRulePairCharge.third_and_charge,
      [``ActualRulePairDiamond.surviving_pair_degrees,
        ``RulePairCharge.third_of_checks, ``RulePairCharge.net_three,
        ``DiamondProfileReducibility.repair001, ``DiamondProfileReducibility.repair002,
        ``SixPortTreeReplacement.Embedded.size_decrease,
        ``SixPortTreeReplacement.open_reconstruct_from_tree,
        ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller]),
    (``ActualRulePairCharge.flat_remainder,
      [``ActualRulePairCharge.third_and_charge, ``RulePairCharge.flat_remainder]),
    (``RulePairChargeExample.observations, []),
    (``RulePairChargeExample.has_third,
      [``RulePairCharge.third_of_checks, ``RulePairExample.cyclic,
        ``RulePairChargeExample.observations]),
    (``RulePairChargeExample.receives_three,
      [``RulePairChargeExample.has_third, ``RulePairCharge.three_of_checks]),
    (``RulePairChargeExample.net_receives_three,
      [``RulePairChargeExample.has_third, ``RulePairCharge.net_three])]
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
  logInfo m!"Joint rule charge: {roots.length} roots; {all.toList.length} declarations. \
    The third actual occurrence is glued from shared readings. \
    Both diamond reductions remain in the minimal-map consumer; no original catalogue \
    certificate, D1774 repair, complete Four Colour endpoint or flat classification."
