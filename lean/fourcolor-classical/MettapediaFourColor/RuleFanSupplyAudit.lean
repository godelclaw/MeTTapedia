import MettapediaFourColor.RuleFanSupplyExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RuleFanSupply.walk_near, []),
    (``RuleFanSupply.walk_ne_receiver, [``ExceptionalCoreLocalInjectivity.corner_chain_injective]),
    (``RuleFanSupply.mixed, [``FacialStarCompletion.across_edge]),
    (``RuleFanSupply.eight_word, []),
    (``RuleFanSupply.nine_word, []),
    (``RuleFanSupply.alternatives,
      [``RuleFanSupply.mixed, ``RuleFanSupply.eight_word, ``RuleFanSupply.nine_word]),
    (``RuleFanSupply.fixed_of_checks, [``RuleMatcher.check_iff, ``FacialStarCompletion.pow_pred]),
    (``ActualRuleFanSupply.degree_five,
      [``GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample,
        ``ActualRulePairDiamond.degree_dart]),
    (``ActualRuleFanSupply.not_low_fan,
      [``RuleFanSupply.alternatives,
        ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller,
        ``ChainFanRecognition.not_in_minimal,
        ``ActualExtendedChainReduction.not_degree_word,
        ``FanBoundaryScheme.hom, ``NearLinearChainRepair.repair0004,
        ``NearLinearChainRepair.reference_repair, ``Bulk.Cfg006.hpairs,
        ``DiamondProfileReducibility.repair002]),
    (``ActualRuleFanSupply.first_six, [``RuleFanSupply.mixed]),
    (``ActualRuleFanSupply.surviving_degrees,
      [``RuleFanSupply.fixed_of_checks, ``ActualRuleFanSupply.not_low_fan,
        ``ActualRuleFanSupply.first_six]),
    (``ActualRuleFanSupply.next_center,
      [``ActualRuleFanSupply.surviving_degrees, ``RuleFanSupply.walk_near,
        ``RuleFanSupply.walk_ne_receiver]),
    (``ActualRuleFanSupply.next_flat_center, [``ActualRuleFanSupply.next_center]),
    (``RuleFanSupplyExample.left_candidate, []),
    (``RuleFanSupplyExample.right_candidate, []),
    (``RuleFanSupplyExample.observations, []),
    (``RuleFanSupplyExample.free_degrees, []),
    (``RuleFanSupplyExample.fixed, [``RuleFanSupply.fixed_of_checks]),
    (``RuleFanSupplyExample.diamond,
      [``RuleFanSupply.mixed, ``RuleFanSupplyExample.observations]),
    (``RuleFanSupplyExample.eight_word,
      [``RuleFanSupply.eight_word, ``RuleFanSupplyExample.observations]),
    (``RuleFanSupplyExample.nine_word,
      [``RuleFanSupply.nine_word, ``RuleFanSupplyExample.observations]),
    (``RuleFanSupplyExample.eightOccurrence,
      [``ChainCoreOccurrence.occurrence, ``FanBoundaryScheme.hom]),
    (``RuleFanSupplyExample.nineOccurrence,
      [``ExtendedChainRecognition.occurrence, ``FanBoundaryScheme.hom])]
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
  logInfo m!"Shared rule fan: {roots.length} roots; {all.toList.length} declarations. \
    Two same-root source rules supply a diamond or one of two chain words. \
    Their actual reconstructions force a higher-degree continuation. \
    The shared diamond profile and configuration 7 remain; global coverage is open."
