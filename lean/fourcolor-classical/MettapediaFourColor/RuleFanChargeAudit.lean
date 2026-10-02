import MettapediaFourColor.ActualRuleFanCharge
import MettapediaFourColor.RuleFanChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RuleFanCharge.ofTwoFaces, [``ExceptionalCoreOrientation.Corner.rotate]),
    (``RuleFanCharge.ofFace, [``ExceptionalCoreOrientation.Corner.rotate]),
    (``RuleFanCharge.ofReverseFace, [``ExceptionalCoreOrientation.Corner.rotate]),
    (``RuleFanCharge.swapped, [``RuleFanCharge.swap_pattern]),
    (``RuleFanCharge.face_checks, [``RuleFanCharge.ofTwoFaces, ``RuleFanCharge.swapped]),
    (``RuleFanCharge.sent_lower, []),
    (``RuleFanCharge.three_senders, [``RuleFanCharge.face_checks,
      ``RuleFanCharge.ofFace, ``RuleFanCharge.ofReverseFace, ``RuleFanCharge.sent_lower]),
    (``RuleFanCharge.wings_at_first_free, []),
    (``RuleFanCharge.window_positive, [``RulePairCharge.high_to_low_zero,
      ``ExceptionalCoreLocalInjectivity.corner_chain_injective]),
    (``RuleFanCharge.positive_of_low, [``RuleFanCharge.window_positive,
      ``RuleFanCharge.three_senders, ``FacialStarCompletion.across_edge]),
    (``RuleFanCharge.flat_has_high_neighbor, [``RuleFanCharge.positive_of_low]),
    (``ActualRuleFanCharge.opposite_not_adjacent,
      [``MinimalExceptionalEmbedding.triangle_facial]),
    (``ActualRuleFanCharge.third_center, [``RuleFanSupply.fixed_of_checks,
      ``RuleFanCharge.wings_at_first_free, ``RuleFanCharge.flat_has_high_neighbor,
      ``ActualRuleFanSupply.degree_five, ``ActualRuleFanCharge.opposite_not_adjacent]),
    (``RuleFanChargeExample.wings, []),
    (``RuleFanChargeExample.neighbors_low, []),
    (``RuleFanChargeExample.positive, [``RuleFanCharge.positive_of_low,
      ``RuleFanChargeExample.cyclic, ``RuleFanChargeExample.triangular])]
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
  logInfo m!"Shared fan charge: {roots.length} roots; {all.toList.length} declarations. \
    The 3,4,3 budget extends to twelve units from five distinct senders. \
    A flat seven supplies an adjacent high centre; actual faciality excludes the original receiver. \
    No original rank or exceptional repair certificate is used. Global coverage is open."
