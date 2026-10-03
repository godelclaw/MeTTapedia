import MettapediaFourColor.ExtendedChainExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ThreeTriangleFan.injective, [``ExceptionalCoreLocalInjectivity.corner_chain_injective]),
    (``ThreeTriangleFan.reflects, [``FacialPatchInduced.corner_chain_successor]),
    (``FanBoundaryScheme.outer_seam, [``FacialStarCompletion.across_edge]),
    (``FanBoundaryScheme.row_agrees, [``FacialBoundaryScheme.outer_seam]),
    (``FanBoundaryScheme.hom, [``FacialBoundaryScheme.row_agrees]),
    (``FanBoundaryScheme.ring_outside_core, [``FacialBoundaryScheme.around_injective]),
    (``ChainCoreCompletion.hom, [``FanBoundaryScheme.hom]),
    (``ChainFanRecognition.not_in_minimal,
      [``ThreeTriangleFan.reflects, ``FanBoundaryScheme.hom,
        ``NearLinearChainRepair.repair0004, ``Bulk.Cfg006.hpairs]),
    (``ExtendedChainCore.source_edges, []),
    (``ExtendedChainCore.of_word, [``ChainFanRecognition.hom]),
    (``ExtendedChainCore.injective, [``ThreeTriangleFan.injective]),
    (``ExtendedChainCore.reflects, [``ThreeTriangleFan.reflects]),
    (``ExtendedChainCompletion.scheme, []),
    (``ExtendedChainCompletion.hom, [``FanBoundaryScheme.hom]),
    (``ExtendedChainCompletion.vertex_near, [``FanBoundaryScheme.vertex_near]),
    (``ExtendedChainOccurrence.disk_injective, [``FaithfulKernelEmbedding.disk_injective]),
    (``ExtendedChainRecognition.occurrence,
      [``ExtendedChainCore.injective, ``FanBoundaryScheme.ring_outside_core]),
    (``ExtendedChainContract.valid_contract, [``KempeRepairContract.valid_singleton]),
    (``ExtendedChainContract.singleton_reducible, [``NearLinearChainRepair.reference_repair]),
    (``ActualExtendedChainReduction.colorable,
      [``ActualDualContract.singleton_colorable, ``InjectiveEmbeddedRepair.colorable]),
    (``ActualExtendedChainReduction.not_degree_word,
      [``ExtendedChainCore.of_word, ``ThreeTriangleFan.reflects,
        ``FanBoundaryScheme.hom, ``NearLinearChainRepair.reference_repair, ``Bulk.Cfg006.hpairs]),
    (``ExtendedChainExample.neighbor_word, []),
    (``ExtendedChainExample.occurrence, [``ExtendedChainRecognition.occurrence]),
    (``ExtendedChainExample.complete_images, []),
    (``ExtendedChainExample.complete_near, [``FanBoundaryScheme.vertex_near])]
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
  logInfo m!"Shared fan completion: {roots.length} roots; {all.toList.length} declarations. \
    The degree words 5,6,5,5 and 5,6,6,5 use one geometric completion scheme. \
    Both have actual minimal-map reconstruction consumers. \
    Configuration 7 remains the only rank certificate; uniform coverage is open."
