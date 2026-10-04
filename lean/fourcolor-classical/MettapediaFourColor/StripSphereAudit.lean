import MettapediaFourColor.StripSphereGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor StripSpherePhase SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``routes, [``exterior, ``route_chain, ``route_active]),
    (``phase_requires_two, [``StripPhaseObstruction.routed_requires_two, ``routes]),
    (``any_phase_requires_two, [``KempePairHistory.pointwise, ``phase_requires_two]),
    (``exterior_adj, [``ambient, ``exterior, ``position_include]),
    (``outside_iff, [``include_position, ``outside_include]),
    (``include_injective, [``position_include]),
    (``source_edges, [``TriangleStripAnchors.input0099, ``ambient]),
    (``source_injective, [``image]),
    (``core_stars, [``TriangleStripAnchors.input0099, ``ambient]),
    (``planar, [``GraphTriangulationEuler.planar_iff_balance, ``Hypermap.cubic_Euler,
      ``face_check, ``connected, ``dart_count]),
    (``degree_bounds, [``GraphRotationRows.Rows.degree, ``FourColor.StripSpherePhase.star]),
    (``repair_eq, [``Coloring.swapOnKempeComponent,
      ``KempeSeparatedChains.Certificate.swap_apply]),
    (``whole_repair, [``Coloring.swapOnKempeComponent, ``final_proper,
      ``Mettapedia.GSLT.Ultrainfinite.Route]),
    (``no_phase_reconstruction, [``StripPartialColouring.validExcept_of_source,
      ``any_phase_requires_two, ``source_edges, ``boundary_aligned]),
    (``history_needs_two, [``no_phase_reconstruction,
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
  logInfo m!"Spherical strip phase: {contracts.length} roots; {all.toList.length} declarations."
