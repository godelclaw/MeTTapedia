import Mettapedia.GraphTheory.FourColor.DualTruncateInverseExample
import Lean.Util.CollectAxioms

/-! Audit inverse recognition, recovered geometry and actual colouring
consumers. The inverse and source-choice arguments are required dependencies;
previous target-colouring shortcuts and classical endpoints are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateFaceCoverFrame.fromCover_marked_iff,
      [``DualTruncateFaceCoverFrame.markedDart_unique, ``VertexCodeCyclicEncoder.rot_three]),
    (``DualTruncateInverse.pulled_slot,
      [``DualTruncateInverse.pulled_mark, ``DualTruncateInverse.pulled_next_mark]),
    (``DualTruncateInverse.source_loopless, [``DualTruncateInverse.pow_zero]),
    (``DualTruncateInverse.source, [``DualTruncateInverse.source_loopless,
      ``DualTruncateInverse.sourceAlpha_sameCycle_iff]),
    (``DualTruncateInverse.adapter_alpha, [``DualTruncateInverse.pulled_slot]),
    (``DualTruncateInverse.adapter_rho, []),
    (``DualTruncateInverseGeometry.source_cubic,
      [``DualTruncateFaceGeometry.faceOrbit_zero_card,
       ``RotationSystemExactTransport.faceOrbit_card]),
    (``DualTruncateInverseGeometry.source_spherical,
      [``DualTruncateInverseGeometry.source_cubic, ``DualTruncateFaceGeometry.euler_preserved]),
    (``DualTruncateInverseGeometry.source_connected,
      [``RotationSystemExactTransport.primalIso,
       ``GoertzelV24RotationEdgeBridge.reachable_map_of_adj_eq_or_adj]),
    (``DualTruncateInverseGeometry.source_strictly_smaller,
      [``DualTruncateInverseGeometry.source_size]),
    (``DualTruncateInverseGeometry.recognized_source,
      [``DualTruncateFaceCoverFrame.fromCover_marked_iff,
       ``DualTruncateInverseGeometry.source_spherical,
       ``DualTruncateInverseGeometry.source_connected,
       ``DualTruncateInverseGeometry.source_strictly_smaller]),
    (``DualTruncateInverseGeometry.tait,
      [``DualTruncateInverse.adapter_alpha, ``DualTruncateConstructionGSLT.tait_relabelled]),
    (``DualTruncateInverseGeometry.structural_tait,
      [``DualTruncateInverseGeometry.source_connected, ``DualTruncateCyclicSource.source]),
    (``DualTruncateInverseGeometry.every_complete_sweep,
      [``DualTruncateInverse.adapter_rho, ``DualTruncateConstructionGSLT.supported_relabelled_route]),
    (``DualTruncateInverseRoundTrip.vertexEquiv,
      [``DualTruncateInverseRoundTrip.recovered_rho]),
    (``DualTruncateInverseRoundTrip.colouring,
      [``DualTruncateInverseRoundTrip.vertexEquiv]),
    (``DualTruncateInverseRoundTrip.fromCover_data,
      [``DualTruncateInverseRoundTrip.fromCover_dart,
       ``DualTruncateFaceCoverFrame.markedDart_unique]),
    (``DualTruncateInverseExample.square_marked_iff,
      [``DualTruncateGeometryExample.source_face_length]),
    (``DualTruncateInverseExample.recovered_vertex_count,
      [``DualTruncateInverseGeometry.source_size]),
    (``DualTruncateInverseExample.recovered_edge_count, []),
    (``DualTruncateInverseExample.recovered_face_count,
      [``DualTruncateInverseGeometry.source_spherical]),
    (``DualTruncateInverseExample.recovered_colouring,
      [``DualTruncateInverseRoundTrip.fromCover_data,
       ``DualTruncateInverseRoundTrip.colouring, ``DualTruncateCyclicSource.source,
       ``DualTruncateInverseExample.square_marked_iff]),
    (``DualTruncateInverseExample.recognized_coloured_target,
      [``DualTruncateInverseGeometry.source_spherical,
       ``DualTruncateInverseGeometry.source_connected,
       ``DualTruncateInverseGeometry.source_strictly_smaller,
       ``DualTruncateInverseGeometry.tait,
       ``DualTruncateInverseExample.recovered_colouring]),
    (``DualTruncateInverseExample.every_complete_sweep,
      [``DualTruncateInverseGeometry.every_complete_sweep,
       ``DualTruncateInverseExample.recovered_colouring])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    ``DualTruncateCoupledExample.target_tait,
    ``DualTruncateCyclicSourceExample.target_tait,
    ``DualTruncateGeometryExample.target_coloured_geometry]
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
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Dual-and-truncate inverse recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    previous target-colouring shortcuts, source colour-word certificates and \
    complete classical theorem absent."
