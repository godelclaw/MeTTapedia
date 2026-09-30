import Mettapedia.GraphTheory.FourColor.PaddedCycleCapExteriorConnectivity
import Lean.Util.CollectAxioms

/-! Audit short-face exterior connectivity and its actual all-width strict
reduction consumer. Vertex injectivity remains explicit; coverage and
additional classical certificate replacements are not claimed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``Compositional.ShortFacePortExclusion.exterior_arc, []),
    (``Compositional.ShortFaceBoundaryConnectivity.consecutive_reachable,
      [``Compositional.ShortFacePortExclusion.exterior_arc]),
    (``Compositional.ShortFaceBoundaryConnectivity.endpoints_reachable,
      [``Compositional.ShortFaceBoundaryConnectivity.consecutive_reachable]),
    (``Compositional.ShortFaceBoundaryConnectivity.exterior_connected,
      [``Compositional.ShortFaceBoundaryConnectivity.endpoints_reachable,
       ``GoertzelV24CyclicThreeCutConnectedSides.inducedReachableSide]),
    (``PaddedCycleCap.FaceTraversal.port_rotated_mate_mem, []),
    (``PaddedCycleCap.FaceTraversal.outgoing_is_port,
      [``PaddedCycleCap.FaceTraversal.darts,
       ``PaddedCycleCap.FaceTraversal.ambient_alpha]),
    (``PaddedCycleCap.FaceTraversal.face_traced_exterior_connected,
      [``Compositional.ShortFaceBoundaryConnectivity.exterior_connected,
       ``PaddedCycleCap.FaceTraversal.outgoing_is_port,
       ``PaddedCycleCap.FaceTraversal.port_rotated_mate_mem,
       ``PaddedCycleCap.FaceTraversal.port_not_deleted,
       ``PaddedCycleCap.FaceTraversal.port_arc]),
    (``PaddedCycleCap.FaceTraversal.face_traced_vertex_count,
      [``PaddedCycleCap.FaceTraversal.vertices,
       ``GoertzelV24VertexSideReassembly.complementaryVertexEquiv]),
    (``PaddedCycleCap.FaceTraversal.face_traced_strict_reduction,
      [``PaddedCycleCap.FaceTraversal.face_traced_exterior_connected,
       ``PaddedCycleCap.FaceTraversal.recognition,
       ``PaddedCycleCap.recognized_cap_strict_reduction,
       ``PaddedCycleCap.recognized_cap_reconstruct,
       ``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing]),
    (``PaddedCycleCap.FaceTraversal.no_face_traced_cap_of_short_faces,
      [``PaddedCycleCap.FaceTraversal.face_traced_strict_reduction,
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
  logInfo m!"Short-face exterior connectivity and actual cap reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
