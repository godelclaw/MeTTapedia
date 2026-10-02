import MettapediaFourColor.ActualChainReduction
import MettapediaFourColor.ChainReductionExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``NearLinearChainConstruction.numbered_eq, []),
    (``NearLinearChainConstruction.faces, []),
    (``NearLinearChainConstruction.source_rotation, []),
    (``NearLinearChainConstruction.ringTrace_iff, []),
    (``NearLinearChainConstruction.embeddable, []),
    (``NearLinearChainContract.repair,
      [``NearLinearChainRepair.repair0004,
        ``BoundaryTriangleRepair.reconstruct, ``KempeBoundarySplit.repairs_collapse]),
    (``NearLinearChainContract.contract_endpoints, []),
    (``NearLinearChainContract.valid_contract, []),
    (``NearLinearChainContract.singleton_reducible,
      [``NearLinearChainContract.valid_contract, ``NearLinearChainContract.repair]),
    (``NearLinearChainOccurrence.kernel_iff, []),
    (``NearLinearChainOccurrence.source_arity, []),
    (``NearLinearChainOccurrence.preembedding, []),
    (``NearLinearChainOccurrence.kernel_injective,
      [``Hypermap.cface_inj_embed]),
    (``NearLinearChainOccurrence.faithful, []),
    (``NearLinearChainOccurrence.disk_injective,
      [``FaithfulKernelEmbedding.disk_injective,
        ``NearLinearChainOccurrence.faithful]),
    (``ActualChainReduction.colorable,
      [``NearLinearChainContract.valid_contract,
        ``NearLinearChainRepair.repair0004,
        ``NearLinearChainOccurrence.disk_injective,
        ``ActualDualContract.singleton_colorable, ``MinimalSingletonContract.one_zero,
        ``InjectiveEmbeddedRepair.colorable, ``Bulk.Cfg006.hpairs]),
    (``ActualChainReduction.not_in_minimal,
      [``ActualChainReduction.colorable, ``ActualDualContract.not_colorable]),
    (``ChainReductionExample.cyclic, []),
    (``ChainReductionExample.triangular, []),
    (``ChainReductionExample.occurrence, []),
    (``ChainReductionExample.disk_injective,
      [``NearLinearChainOccurrence.disk_injective,
        ``ChainReductionExample.occurrence])]
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
  logInfo m!"Actual chain reduction: {roots.length} roots; {all.toList.length} declarations. \
    Configuration 7 supplies the only rank certificate. Actual minimality supplies \
    the starting contract, and planar exterior repair reconstructs the colouring. \
    Geometric occurrence supply remains open."
