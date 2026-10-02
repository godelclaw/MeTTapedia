import MettapediaFourColor.ChainBoundaryExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RuleChainRecognition.step_one, []),
    (``RuleChainRecognition.step_two, [``RuleChainRecognition.step_one]),
    (``RuleChainRecognition.neighbor_word, [``RuleChainRecognition.step_two]),
    (``RuleChainRecognition.reading, [``ChainFanRecognition.reading]),
    (``RuleChainRecognition.continuation_near, [``NearLinearCharge.Occurrence.vertex_near]),
    (``RuleChainRecognition.complete_patch_near,
      [``ChainCoreCompletion.vertex_near, ``LocalCoverageAssembly.ball_recenter]),
    (``RuleChainRecognition.not_continuation_five,
      [``ActualChainRecognition.not_in_minimal, ``NearLinearChainRepair.repair0004,
        ``ActualDualContract.singleton_colorable, ``InjectiveEmbeddedRepair.colorable,
        ``Bulk.Cfg006.hpairs]),
    (``ChainBoundaryExample.cyclic, []),
    (``ChainBoundaryExample.triangular, []),
    (``ChainBoundaryExample.neighbor_word, []),
    (``ChainBoundaryExample.occurrence, [``ChainCoreOccurrence.occurrence]),
    (``ChainBoundaryExample.complete_patch_near, [``ChainCoreCompletion.vertex_near]),
    (``ChainBoundaryExample.crosses_both_boundaries, []),
    (``ChainBoundaryExample.rule, []),
    (``ChainBoundaryExample.rule_guards, []),
    (``ChainBoundaryExample.continued_core, []),
    (``ChainBoundaryExample.continued_patch_near,
      [``RuleChainRecognition.complete_patch_near])]
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
  logInfo m!"Continued rule recognition: {roots.length} roots; {all.toList.length} declarations. \
    One further degree-five observation completes an actual chain reduction. \
    All thirteen reconstructed vertices lie within radius four of the receiver. \
    Configuration 7 remains the only rank certificate; uniform coverage is open."
