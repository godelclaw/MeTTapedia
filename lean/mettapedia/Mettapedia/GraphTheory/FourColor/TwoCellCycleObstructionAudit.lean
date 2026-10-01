import Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction
import Lean.Util.CollectAxioms

/-! Audit the uniform joint-choice law and its actual fixed-exterior
consumer. Neither the acceptance law nor the obstruction uses a complete
classical endpoint or a complete source-colouring supplier. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoCellBoundaryChoice.choices_iff, []),
    (``TwoCellBoundaryChoice.equal_forced_colours, [``TwoCellBoundaryChoice.choices_iff]),
    (``TwoCellBoundaryChoice.cycle_valid, []),
    (``TwoCellBoundaryChoice.cycle_spokes, []),
    (``TwoCellBoundaryChoice.cycle_accepts,
      [``TwoCellBoundaryChoice.cycle_valid, ``TwoCellBoundaryChoice.cycle_spokes,
       ``CycleCap.accepts_spokes]),
    (``TwoCellCycleObstruction.valid, []),
    (``TwoCellCycleObstruction.source_cubic, []),
    (``TwoCellCycleObstruction.source_rotationCyclic, []),
    (``TwoCellCycleObstruction.source_face_count, []),
    (``TwoCellCycleObstruction.source_spherical, [``TwoCellCycleObstruction.source_face_count]),
    (``TwoCellCycleObstruction.source_reachable, []),
    (``TwoCellCycleObstruction.source_connected, [``TwoCellCycleObstruction.source_reachable]),
    (``TwoCellCycleObstruction.target_mapClass, [``DualTruncateMapGeometry.mapClass_of]),
    (``TwoCellCycleObstruction.source_face_length, []),
    (``TwoCellCycleObstruction.target_face_lengths,
      [``DualTruncateFaceGeometry.vertex_face_length,
       ``DualTruncateFaceGeometry.faceOrbit_two_card, ``TwoCellCycleObstruction.source_face_length]),
    (``TwoCellCycleObstruction.simple_source, []),
    (``TwoCellCycleObstruction.separated, []),
    (``TwoCellCycleObstruction.forest, []),
    (``TwoCellCycleObstruction.exterior_stars, []),
    (``TwoCellCycleObstruction.paired, []),
    (``TwoCellCycleObstruction.fibreEquiv, [``DualTruncateForestCollapse.extensionSourceEquiv]),
    (``TwoCellCycleObstruction.no_source_choice, [``TwoCellBoundaryChoice.equal_forced_colours]),
    (``TwoCellCycleObstruction.no_fixed_exterior_extension,
      [``TwoCellCycleObstruction.no_source_choice, ``TwoCellCycleObstruction.fibreEquiv]),
    (``TwoCellCycleObstruction.outer_ring_injective, []),
    (``TwoCellCycleObstruction.outer_ring_vertices, []),
    (``TwoCellCycleObstruction.outer_ring_adjacent, []),
    (``TwoCellCycleObstruction.patch_internal_edges, []),
    (``TwoCellCycleObstruction.ports_are_actual_cut, []),
    (``TwoCellCycleObstruction.boundary_injective, []),
    (``TwoCellCycleObstruction.ports_follow_ring, []),
    (``TwoCellCycleObstruction.boundary_colours, []),
    (``TwoCellCycleObstruction.cycle_accepts_actual_boundary,
      [``TwoCellBoundaryChoice.cycle_accepts, ``TwoCellCycleObstruction.boundary_colours]),
    (``TwoCellCycleObstruction.target_vertices, []),
    (``TwoCellCycleObstruction.patch_vertices, []),
    (``TwoCellCycleObstruction.exterior_vertices, []),
    (``TwoCellCycleObstruction.nominal_vertex_loss, [])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    ``DualTruncateStructuralColoring.source_of_connected_pair,
    ``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateForestExample]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Forbidden proof dependency in {root}: {name}"
      if (`Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoice).isPrefixOf root &&
          (`Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction).isPrefixOf name then
        throwError m!"Finite exterior data entered the uniform colour law {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Exact two-cell seam obstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical endpoints and source-colouring suppliers absent; \
    finite exterior values absent from the uniform joint-choice law."
