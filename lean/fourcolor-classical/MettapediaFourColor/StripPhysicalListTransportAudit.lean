import MettapediaFourColor.StripPhysicalListTransport
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``BoundaryEndpointTransport.two, []),
    (``BoundaryEndpointTransport.three, []),
    (``StripEndpointTransport.forbidden_change,
      [``BoundaryEndpointTransport.two, ``BoundaryEndpointTransport.three]),
    (``StripEndpointTransport.lists_change, [``StripEndpointTransport.forbidden_change]),
    (``StripEndpointTransport.congruence, [``StripEndpointTransport.lists_change]),
    (``StripEndpointTransport.guard_full_change, [``StripEndpointTransport.lists_change,
      ``TriangleStripLists.guard_colouring, ``ColoringListPropagation.forest_colouring,
      ``StripListTransport.full_iff]),
    (``StripPhysicalListTransport.planar, [``GraphDiskEuler.planar]),
    (``StripPhysicalListTransport.closed, [``StripPhysicalListTransport.planar,
      ``PlanarGraphBoundaryClosure.rotation_closed]),
    (``StripPhysicalListTransport.swap_eq, [``KempeSeparatedChains.Certificate.swap_apply]),
    (``StripPhysicalListTransport.physicalStep, [``StripPhysicalListTransport.swap_eq,
      ``KempeSeparatedChains.Certificate.step, ``SimpleGraph.Coloring.swap_apply_of_chain]),
    (``StripPhysicalListTransport.same_lists, [``StripPhysicalListTransport.read_before]),
    (``StripPhysicalListTransport.endpoint_read, []),
    (``StripPhysicalListTransport.compact_guard, []),
    (``StripPhysicalListTransport.compact_reconstruct,
      [``StripEndpointTransport.guard_full_change, ``BoundaryEndpointTransport.three,
      ``ColoringListPropagation.forest_colouring]),
    (``StripPhysicalListTransport.source_distinguishes,
      [``StripPhysicalListTransport.compact_reconstruct, ``StripListTransport.changed_fails]),
    (``StripPhysicalListTransport.no_list_only_physical_transport,
      [``StripPhysicalListTransport.same_lists, ``StripPhysicalListTransport.source_distinguishes])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Physical endpoint transport: {contracts.length} roots; \
    {all.toList.length} declarations."
