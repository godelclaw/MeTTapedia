import Mettapedia.GraphTheory.FourColor.PentagonalPaddedCapReduction
import Lean.Util.CollectAxioms

/-! Audit pentagonal cap recognition, strict whole-map decrease and actual
colouring reconstruction. Geometry certificates are retained explicitly;
no new colouring table, classical certificate replacement or occurrence
coverage theorem is claimed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PartialCubicDartSeparation.Realization.fourPathCheck_sound,
      [``PartialCubicDartSeparation.Realization.ne_of_path_four]),
    (``PartialCubicDartSeparation.Realization.routeCheck_sound,
      [``PartialCubicDartSeparation.Realization.girthApart_sound,
       ``PartialCubicDartSeparation.Realization.rotate_eq,
       ``PartialCubicDartSeparation.Realization.flip_eq]),
    (``PaddedCycleCap.PartialDiagram.realization,
      [``PaddedCycleCap.PartialDiagram.interpreted_flip,
       ``PaddedCycleCap.FaceTraversal.dart_alpha,
       ``PaddedCycleCap.FaceTraversal.atStar_rotate]),
    (``PaddedCycleCap.PentagonalSeparation.flip_eq, []),
    (``PaddedCycleCap.PentagonalSeparation.shiftedRealization,
      [``PaddedCycleCap.PentagonalSeparation.shift_flip]),
    (``PaddedCycleCap.PentagonalSeparation.certified_routes, []),
    (``PaddedCycleCap.PentagonalSeparation.vertex_injective,
      [``PaddedCycleCap.PentagonalSeparation.certified_routes,
       ``PaddedCycleCap.PentagonalSeparation.shiftedRealization,
       ``PartialCubicDartSeparation.Realization.routeCheck_sound]),
    (``PaddedCycleCap.PentagonalSeparation.actual_vertex_injective,
      [``PaddedCycleCap.PartialDiagram.realization,
       ``PaddedCycleCap.PentagonalSeparation.flip_eq,
       ``PaddedCycleCap.PentagonalSeparation.vertex_injective]),
    (``PaddedCycleCap.PentagonalFaceReduction.vertex_injective_of_normal_form,
      [``PaddedCycleCap.PentagonalSeparation.actual_vertex_injective,
       ``PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive,
       ``SphericalVertexLowerBound.twenty_le_card_vertices]),
    (``PaddedCycleCap.PentagonalFaceReduction.smaller,
      [``PaddedCycleCap.PentagonalFaceReduction.vertex_injective_of_normal_form,
       ``PaddedCycleCap.FaceTraversal.recognition]),
    (``PaddedCycleCap.PentagonalFaceReduction.strict_reduction_of_face_pattern,
      [``PaddedCycleCap.PentagonalFaceReduction.vertex_injective_of_normal_form,
       ``PaddedCycleCap.FaceTraversal.face_traced_vertex_count,
       ``PaddedCycleCap.FaceTraversal.face_traced_strict_reduction,
       ``PaddedCycleCap.FaceTraversal.face_traced_exterior_connected,
       ``PaddedCycleCap.recognized_cap_reconstruct,
       ``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing]),
    (``PaddedCycleCap.PentagonalFaceReduction.not_in_minimal_counterexample_of_face_pattern,
      [``PaddedCycleCap.PentagonalFaceReduction.strict_reduction_of_face_pattern,
       ``GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample,
       ``GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.five_tube_normalize,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.tube_support_eq,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.transfer_adjacent_of_stabilizes,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.full_transfer_after_word_bound]
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
        throwError m!"Finite stabilization or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Pentagonal cap recognition and actual strict reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
