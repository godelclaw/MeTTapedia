import Mettapedia.GraphTheory.FourColor.PaddedCycleCapRecognition
import Lean.Util.CollectAxioms

/-! Audit the actual face trace, the uniform short-face port exclusion and
the recognition consumed by strict reduction. Vertex separation and exterior
connectivity remain explicit hypotheses. No global coverage is claimed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PaddedCycleCap.FaceTraversal.outer_middle_edge, []),
    (``PaddedCycleCap.FaceTraversal.outer_closing, []),
    (``PaddedCycleCap.FaceTraversal.dart_alpha,
      [``PaddedCycleCap.FaceTraversal.middle_closing,
       ``PaddedCycleCap.FaceTraversal.outer_middle_edge,
       ``PaddedCycleCap.FaceTraversal.outer_closing]),
    (``PaddedCycleCap.FaceTraversal.dart_rotation, []),
    (``Compositional.ShortFacePortExclusion.reflection, []),
    (``Compositional.ShortFacePortExclusion.no_port_edge,
      [``Compositional.ShortFacePortExclusion.reflection]),
    (``PaddedCycleCap.FaceTraversal.port_arc,
      [``PaddedCycleCap.FaceTraversal.boundary_arc_false,
       ``PaddedCycleCap.FaceTraversal.boundary_arc_true]),
    (``PaddedCycleCap.FaceTraversal.port_two_apart,
      [``PaddedCycleCap.FaceTraversal.dart_injective]),
    (``PaddedCycleCap.FaceTraversal.port_outside,
      [``Compositional.ShortFacePortExclusion.no_port_edge,
       ``PaddedCycleCap.FaceTraversal.port_arc,
       ``PaddedCycleCap.FaceTraversal.port_two_apart,
       ``PaddedCycleCap.FaceTraversal.dart_alpha]),
    (``PaddedCycleCap.FaceTraversal.darts,
      [``PaddedCycleCap.FaceTraversal.dart_injective,
       ``PaddedCycleCap.FaceTraversal.atStar_surjective_at]),
    (``PaddedCycleCap.FaceTraversal.recognition,
      [``OpenTangleIsomorphism.ofRetainedDarts,
       ``PaddedCycleCap.FaceTraversal.dart_alpha,
       ``PaddedCycleCap.FaceTraversal.dart_rotation,
       ``PaddedCycleCap.FaceTraversal.port_outside]),
    (``PaddedCycleCap.FaceTraversal.no_face_traced_cap,
      [``PaddedCycleCap.FaceTraversal.recognition,
       ``PaddedCycleCap.no_recognized_cap,
       ``PaddedCycleCap.recognized_cap_strict_reduction,
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
  logInfo m!"Face-traced padded-cap recognition and strict reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
