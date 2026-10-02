import MettapediaFourColor.ExceptionalLocalRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``InjectiveEmbeddedRepair.contract_traces, []),
    (``InjectiveEmbeddedRepair.colorable,
      [``InjectiveEmbeddedRepair.contract_traces, ``Hypermap.embed_closure]),
    (``FaithfulKernelEmbedding.off_ring_injective, []),
    (``FaithfulKernelEmbedding.disk_injective,
      [``FaithfulKernelEmbedding.off_ring_injective]),
    (``FaithfulKernelEmbedding.colorable,
      [``FaithfulKernelEmbedding.disk_injective, ``InjectiveEmbeddedRepair.colorable]),
    (``ExceptionalDartReading.same_face_iff, []),
    (``ExceptionalDartReading.kernel_iff, [``ExceptionalDartReading.same_face_iff]),
    (``ExceptionalDartReading.source_cycles, []),
    (``ExceptionalDartReading.source_arity, [``ExceptionalDartReading.source_cycles]),
    (``ExceptionalDartReading.edge, []),
    (``ExceptionalDartReading.face, [``ExceptionalBoundaryOccurrence.full_turn]),
    (``ExceptionalDartReading.arity,
      [``ExceptionalDartReading.source_arity, ``DualGraphQuery.arity_eq_degree]),
    (``ExceptionalDartReading.kernel_injective,
      [``ExceptionalBoundaryOccurrence.around_injective]),
    (``ExceptionalDartReading.faithful, [``ExceptionalDartReading.kernel_injective]),
    (``ExceptionalDartReading.actual_faithful,
      [``ExceptionalDartReading.faithful, ``MinimalExceptionalEmbedding.joint_injective,
       ``ExceptionalCoreInduced.joint_induced, ``ExceptionalBoundaryOccurrence.ring_outside_core]),
    (``Hypermap.kernel_relabel, []),
    (``Hypermap.arity_relabel, []),
    (``LocalPreembedding.rlinkConnected, []),
    (``LocalPreembedding.of_radius2, [``LocalPreembedding.rlinkConnected]),
    (``ExceptionalPreembedding.preembedding,
      [``ExceptionalDartReading.face, ``ExceptionalDartReading.arity,
       ``ExceptionalDartReading.edge, ``LocalPreembedding.of_radius2]),
    (``ExceptionalPreembedding.faithful, [``Hypermap.kernel_relabel]),
    (``DualGraphQuery.plain, []),
    (``DualGraphQuery.cubic, []),
    (``ActualDualLocalGeometry.planar, [``ActualDualContract.map_eq_source_relabel]),
    (``ExceptionalLocalRepair.disk_injective,
      [``ExceptionalDartReading.actual_faithful, ``ExceptionalPreembedding.preembedding,
       ``ExceptionalPreembedding.faithful, ``FaithfulKernelEmbedding.disk_injective]),
    (``ExceptionalLocalRepair.colorable,
      [``ExceptionalLocalRepair.disk_injective, ``ActualDualContract.singleton_colorable,
       ``ExceptionalConstructionRepair.singleton_reducible, ``InjectiveEmbeddedRepair.colorable]),
    (``ExceptionalLocalRepair.not_in_minimal,
      [``ExceptionalLocalRepair.colorable, ``ActualDualContract.not_colorable]),
    (``ExceptionalLocalRepair.aligned_not_in_minimal,
      [``ExceptionalLocalRepair.not_in_minimal, ``ExceptionalCore.jointReading]),
    (``ExceptionalLocalRepair.overlap_supply,
      [``ExceptionalLocalRepair.aligned_not_in_minimal, ``ExceptionalOverlap.next_centered])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.Hypermap.embed_full, `FourColor.Hypermap.pre_embed_inj,
    `FourColor.Hypermap.embed_inj, `FourColor.Hypermap.embdd_inj,
    `FourColor.Hypermap.not_embed_reducible]
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
        throwError m!"Forbidden global theorem, embedding shortcut or original certificate \
          in {root}: {name}"
      unless (`FourColor.ExceptionalLocalRepair).isPrefixOf root do
        if (`FourColor.ExceptionalRepairCertificate).isPrefixOf name then
          throwError m!"Finite exceptional repair in geometric or generic root {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exceptional exterior: {roots.length} roots; {all.toList.length} declarations; \
    explicit joint preembedding, locally faithful kernel, injected disk, actual singleton \
    contract and compatible reconstruction. D1774 finite repair retained in the final consumer."
