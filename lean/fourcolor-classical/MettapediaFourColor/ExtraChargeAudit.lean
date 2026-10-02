import MettapediaFourColor.ExtraChargeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ExtraChargeReduction.closing, [``FacialStarCompletion.pow_degree]),
    (``ExtraChargeReduction.alternatives, [``ExtraChargeReduction.closing]),
    (``ExtraChargeReduction.mixed_of_five, [``ExtraChargeReduction.alternatives]),
    (``ExtraChargeReduction.word_of_six, [``ExtraChargeReduction.alternatives]),
    (``ExtraChargeReduction.fan_companion, []),
    (``ActualExtraChargeReduction.not_occurrence,
      [``ExtraChargeReduction.alternatives, ``ChainFanRecognition.not_in_minimal,
       ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller,
       ``NearLinearChainRepair.repair0004, ``FanBoundaryScheme.hom, ``Bulk.Cfg006.hpairs]),
    (``ActualExtraChargeReduction.check_false,
      [``ActualExtraChargeReduction.not_occurrence, ``RuleMatcher.check_iff]),
    (``ActualExtraChargeReduction.residual_check_false,
      [``ActualExtraChargeReduction.check_false, ``ExtraChargeReduction.fan_companion]),
    (``ActualExtraChargeReduction.flat_alternatives,
      [``ActualCyclicFanContinuation.third_or_single_five,
       ``ActualExtraChargeReduction.residual_check_false]),
    (``ExtraChargeExample.chain_fits, []),
    (``ExtraChargeExample.mixed_fits, []),
    (``ExtraChargeExample.chain_word, [``ExtraChargeReduction.word_of_six]),
    (``ExtraChargeExample.mixed_pattern, [``ExtraChargeReduction.mixed_of_five]),
    (``ExtraChargeExample.chainOccurrence,
      [``ExtraChargeExample.chain_word, ``ChainCoreOccurrence.occurrence, ``FanBoundaryScheme.hom])]
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
      if forbidden.any (·.isPrefixOf name) || (name.toString.startsWith "FourColor.Bulk.Cfg" &&
          !(`FourColor.Bulk.Cfg006).isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Extra charge closure: {roots.length} roots; {all.toList.length} declarations. \
    The same missing facial triangle supplies a mixed diamond or an eight-port chain. \
    Actual reconstruction excludes this extra rule in the single-five residual. \
    The shared profile and configuration 7 remain; coverage and other extra rules remain open."
