import MettapediaFourColor.ChainFanRecognition
import MettapediaFourColor.ChainRecognitionExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ChainCoreReading.star_specs, []),
    (``ChainCoreReading.turns, [``ExceptionalCoreOrientation.Corner.rotate]),
    (``ChainCoreReading.injective, [``ExceptionalCoreLocalInjectivity.corner_chain_injective]),
    (``ChainCoreReading.reflects, [``FacialPatchInduced.corner_chain_successor]),
    (``ChainCoreCompletion.fullSpoke_core, []),
    (``ChainCoreCompletion.ring_position_cases, []),
    (``ChainCoreCompletion.edge_reading, []),
    (``ChainCoreCompletion.vertex_near, []),
    (``ChainCoreCompletion.outer_seam, [``FacialStarCompletion.across_edge]),
    (``ChainCoreCompletion.row_agrees, [``ChainCoreCompletion.outer_seam]),
    (``ChainCoreCompletion.hom, [``ChainCoreCompletion.row_agrees]),
    (``ChainCoreOccurrence.full_turn, []),
    (``ChainCoreOccurrence.star_covers, []),
    (``ChainCoreOccurrence.ring_outside_core, []),
    (``ChainCoreOccurrence.source_turn, []),
    (``ChainCoreOccurrence.occurrence,
      [``ChainCoreReading.injective, ``ChainCoreOccurrence.ring_outside_core]),
    (``ActualChainRecognition.occurrence,
      [``ChainCoreReading.reflects, ``MinimalExceptionalEmbedding.triangle_facial]),
    (``ActualChainRecognition.not_in_minimal,
      [``ActualChainReduction.not_in_minimal, ``ActualChainRecognition.occurrence]),
    (``ChainFanRecognition.reading, [``ChainFanRecognition.hom]),
    (``ChainFanRecognition.not_in_minimal,
      [``ActualChainRecognition.not_in_minimal,
        ``NearLinearChainRepair.repair0004, ``ActualDualContract.singleton_colorable,
        ``InjectiveEmbeddedRepair.colorable, ``Bulk.Cfg006.hpairs]),
    (``ChainRecognitionExample.reading, []),
    (``ChainRecognitionExample.induced, []),
    (``ChainRecognitionExample.occurrence, [``ChainCoreOccurrence.occurrence]),
    (``ChainRecognitionExample.boundary_recovered, []),
    (``ChainRecognitionExample.neighbor_word, []),
    (``ChainRecognitionExample.fan_core, [])]
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
  logInfo m!"Chain recognition: {roots.length} roots; {all.toList.length} declarations. \
    The degree word 5,6,5,5 around a degree-six centre supplies an actual chain \
    reduction. Configuration 7 remains the only rank certificate. \
    Universal supply of a recognized degree word remains open."
