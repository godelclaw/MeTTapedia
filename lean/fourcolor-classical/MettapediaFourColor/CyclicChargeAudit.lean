import MettapediaFourColor.CyclicChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CyclicCharge.tip_rules, [``RuleFanCharge.face_checks]),
    (``CyclicCharge.edge_lower, [``CyclicCharge.tip_rules,
      ``RuleFanCharge.ofFace, ``RuleFanCharge.ofReverseFace]),
    (``CyclicCharge.lower, [``CyclicCharge.edge_lower, ``RulePairCharge.high_to_low_zero,
      ``CyclicCharge.star_snd_injective]),
    (``CyclicCharge.flat_budget, [``CyclicCharge.lower]),
    (``CyclicFanContinuation.tip_reverse, [``FacialStarCompletion.across_edge]),
    (``CyclicFanContinuation.two_tips, []),
    (``CyclicFanContinuation.fan_tips,
      [``CyclicFanContinuation.tip_reverse, ``CyclicFanContinuation.two_tips]),
    (``CyclicFanContinuation.seven_bound,
      [``CyclicCharge.flat_budget, ``CyclicFanContinuation.fan_tips]),
    (``CyclicFanContinuation.eight_bound,
      [``CyclicCharge.flat_budget, ``CyclicFanContinuation.fan_tips]),
    (``CyclicFanContinuation.unique_five, []),
    (``ActualCyclicFanContinuation.opposite_nonadjacent,
      [``MinimalExceptionalEmbedding.triangle_facial, ``RuleFanSupply.walk_ne_receiver]),
    (``ActualCyclicFanContinuation.third_or_single_five,
      [``ActualCyclicFanContinuation.opposite_nonadjacent, ``ActualRuleFanSupply.degree_five,
       ``CyclicFanContinuation.seven_bound, ``CyclicFanContinuation.unique_five]),
    (``ActualCyclicFanContinuation.of_checks,
      [``RuleFanSupply.fixed_of_checks, ``ActualCyclicFanContinuation.third_or_single_five]),
    (``CyclicChargeExample.eight_counts, []),
    (``CyclicChargeExample.seven_counts, []),
    (``CyclicChargeExample.eight_positive,
      [``CyclicCharge.lower, ``ChainBoundaryExample.triangular]),
    (``CyclicChargeExample.seven_positive,
      [``CyclicCharge.lower, ``ChainBoundaryExample.triangular])]
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
  logInfo m!"Cyclic charge: {roots.length} roots; {all.toList.length} declarations. \
    Shared triangles give four units per five and two per outer tip. \
    Actual flat sevens supply a third high centre or the specified single-five profile. \
    No original rank or exceptional repair certificate is used. Coverage remains open."
