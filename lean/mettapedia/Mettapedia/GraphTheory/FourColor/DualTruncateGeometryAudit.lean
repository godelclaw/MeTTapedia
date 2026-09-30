import Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample
import Lean.Util.CollectAxioms

/-! Audit actual face classification, geometric reconstruction and colouring
consumers. The source-cut theorem and the complete face invariant are required
proof dependencies; colour-word certificates and classical endpoints are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateFaceGeometry.sameCycle_iff_faceTag,
      [``DualTruncateFaceGeometry.pow_zero_slot, ``DualTruncateFaceGeometry.pow_two_slot]),
    (``DualTruncateFaceGeometry.faceEquiv,
      [``DualTruncateFaceGeometry.sameCycle_iff_faceTag, ``DualTruncateFaceGeometry.faceTag_surjective]),
    (``DualTruncateFaceGeometry.face_count, [``DualTruncateFaceGeometry.faceEquiv]),
    (``DualTruncateFaceGeometry.vertex_face_length, [``DualTruncateFaceGeometry.faceOrbit_zero_card]),
    (``DualTruncateFaceGeometry.faceOrbit_two_card, [``DualTruncateFaceGeometry.faceOrbit_two_eq]),
    (``DualTruncateFaceGeometry.euler_preserved, [``DualTruncateFaceGeometry.face_count]),
    (``DualTruncateFaceGeometry.fullerene,
      [``DualTruncateFaceGeometry.vertex_face_length, ``DualTruncateFaceGeometry.faceOrbit_two_card]),
    (``DualTruncateFaceGeometry.facesTwoSided, [``DualTruncateFaceGeometry.faceTag_of_sameCycle]),
    (``DualTruncateMapGeometry.edgeBridgeFree_of_facesTwoSided,
      [``GoertzelV24BridgeTwoSided.sameCycle_of_bridge]),
    (``DualTruncateMapGeometry.primalConnected,
      [``DualTruncateMapGeometry.reachable_same_vertex, ``DualTruncateMapGeometry.adjacent_alpha]),
    (``DualTruncateMapGeometry.mapClass_of,
      [``DualTruncateFaceGeometry.euler_preserved, ``DualTruncateMapGeometry.primalConnected,
       ``DualTruncateMapGeometry.edgeBridgeFree_of_facesTwoSided]),
    (``DualTruncateMapGeometry.coloured_target,
      [``DualTruncateMapGeometry.mapClass, ``DualTruncateCyclicSource.tait]),
    (``DualTruncateMapGeometry.supported_target,
      [``DualTruncateMapGeometry.mapClass, ``DualTruncateCyclicSource.every_complete_sweep]),
    (``DualTruncateGeometryExample.source_face_count, []),
    (``DualTruncateGeometryExample.source_spherical, [``DualTruncateGeometryExample.source_face_count]),
    (``DualTruncateGeometryExample.target_mapClass, [``DualTruncateMapGeometry.mapClass_of]),
    (``DualTruncateGeometryExample.target_face_count, [``DualTruncateFaceGeometry.face_count]),
    (``DualTruncateGeometryExample.target_face_lengths,
      [``DualTruncateFaceGeometry.vertex_face_length, ``DualTruncateFaceGeometry.faceOrbit_two_card]),
    (``DualTruncateGeometryExample.target_coloured_geometry,
      [``DualTruncateGeometryExample.target_mapClass, ``DualTruncateCyclicSource.tait])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring]
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
  logInfo m!"Dual-and-truncate face geometry: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    source colour-word certificates and complete classical theorem absent."
