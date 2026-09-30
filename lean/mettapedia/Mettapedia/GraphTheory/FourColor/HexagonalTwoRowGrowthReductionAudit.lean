import Mettapedia.GraphTheory.FourColor.AlternatingCycleRecognition
import Lean.Util.CollectAxioms

/-! Audit the constructed successor, actual two-row assembly, strict
reduction and immediate pentagonal-seam consumers. No complete classical
endpoint or finite tube-stabilization certificate is permitted. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TubeSlab.ZigzagSlab.successor_matching,
      [``TubeSlab.ZigzagSlab.nextRow_inEquiv]),
    (``TubeSlab.ZigzagSlab.twoRowSlab,
      [``TubeSlab.SlabOf.assembleWith,
       ``TubeSlab.ZigzagSlab.collarVertex_injective,
       ``TubeSlab.ZigzagSlab.successor_matching]),
    (``TubeSlab.ZigzagSlab.twoRowSlab_rotation,
      [``TubeSlab.SlabOf.assembleWith_rotationCompatible,
       ``TubeSlab.ZigzagSlab.hexagonalNextRow_rotation]),
    (``TubeSlab.ZigzagSlab.twoRowSlab_vertex_loss,
      [``TubeSlab.SlabOf.wire_vertex_loss]),
    (``TubeSlab.ZigzagSlab.constructed_two_row_reduction,
      [``TubeSlab.SlabOf.wire_reduction_of_short_end_faces,
       ``TubeSlab.SlabOf.wire_reconstruct,
       ``TubeSlab.SlabOf.wire_return_of_short_end_faces,
       ``TubeSlab.SlabOf.wireTwoShores]),
    (``TubeSlab.ZigzagSlab.no_hexagonal_seam,
      [``TubeSlab.ZigzagSlab.twoRowSlab,
       ``TubeSlab.SlabOf.no_two_row_short_end_faces,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable]),
    (``TubeSlab.ZigzagSlab.pentagonalSeam_of_minimal,
      [``TubeSlab.ZigzagSlab.no_hexagonal_seam]),
    (``TubeSlab.Tube.short_face_length_le_one,
      [``TubeSlab.ZigzagSlab.no_hexagonal_seam]),
    (``AlternatingCycleRecognition.recognized_pentagonalSeam,
      [``AlternatingCycleRecognition.row,
       ``AlternatingCycleRecognition.row_rotation,
       ``TubeSlab.ZigzagSlab.pentagonalSeam_of_minimal]),
    (``AlternatingCycleRecognition.recognized_outgoing_pentagon,
      [``AlternatingCycleRecognition.recognized_pentagonalSeam])]
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
  logInfo m!"Constructed two-row growth reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
