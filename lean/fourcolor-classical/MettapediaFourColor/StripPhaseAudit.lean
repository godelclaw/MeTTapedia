import MettapediaFourColor.StripPhaseDisk
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor StripPhaseObstruction SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempePhaseBoundary.endpoint, [``KempeRouteProjection.changed_along_walk]),
    (``KempePhaseBoundary.phase, [``KempePairHistory.pointwise]),
    (``route_chain, [``exterior]), (``route_active, [``state]),
    (``endpoint_conflicts, [``Conflict, ``StripResponseSummary.unary]),
    (``conflict_bound, [``StripPartialColouring.ValidExcept]),
    (``prefix_lower_bound, [``conflict_bound]),
    (``routed_requires_two, [``KempePhaseBoundary.phase, ``conflict_bound]),
    (``phase_requires_two, [``routed_requires_two, ``routes]),
    (``any_pair_requires_two, [``KempePairHistory.pointwise, ``phase_requires_two]),
    (``initial_two, [``StripPartialColouring.ValidExcept]),
    (``repair_eq, [``Coloring.swapOnKempeComponent,
      ``KempeSeparatedChains.Certificate.swap_apply]),
    (``StripPhaseDisk.planar, [``GraphDiskEuler.planar, ``Hypermap.quasicubic_Euler,
      ``StripPhaseDisk.row_adjacent, ``StripPhaseDisk.face_check]),
    (``StripPhaseDisk.closed, [``PlanarGraphBoundaryClosure.rotation_closed,
      ``StripPhaseDisk.planar, ``StripPhaseDisk.ordered]),
    (``source_edges, [``TriangleStripAnchors.input0099]),
    (``core_stars, [``TriangleStripAnchors.input0099]),
    (``source_phase_requires_two, [``StripPartialColouring.validExcept_of_source,
      ``any_pair_requires_two, ``TriangleStripAnchors.input0099]),
    (``final_valid, [``StripResponseSummary.ValidCore]),
    (``reconstructed, [``Coloring.swapOnKempeComponent, ``whole_valid,
      ``Mettapedia.GSLT.Ultrainfinite.Route])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.StripCriticalRepair, `FourColor.StripCoupledRepair]
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
  logInfo m!"Physical strip phase: {contracts.length} roots; {all.toList.length} declarations."
