import Mettapedia.GraphTheory.FourColor.HexagonalTwoRowWiringRecognition
import Lean.Util.CollectAxioms

/-! Audit short ambient end faces, the derived boundary return and exterior
components, and their actual strict-reduction and minimality consumers.
No complete Four Colour endpoint or finite tube stabilization is permitted. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RotationSystemExactTransport.faceOrbit_card,
      [``RotationSystemExactTransport.phi_commute]),
    (``OpenTangleFaceReturnConnectivity.return_reach,
      [``OpenTangleFaceReturnConnectivity.phi_reach]),
    (``ZigzagRing.ShiftedWiring.Geometry.returnCode_of_short_end_faces,
      [``ZigzagRing.ShiftedWiring.Geometry.phi_cube_oldExterior_boundary]),
    (``ZigzagRing.ShiftedWiring.Geometry.twoShores_of_return,
      [``OpenTangleFaceReturnConnectivity.return_reach]),
    (``TubeSlab.SlabOf.wire_return_of_short_end_faces,
      [``ZigzagRing.ShiftedWiring.Geometry.returnCode_of_short_end_faces,
       ``RotationSystemExactTransport.faceOrbit_card]),
    (``TubeSlab.SlabOf.wireTwoShores,
      [``ZigzagRing.ShiftedWiring.Geometry.twoShores_of_return,
       ``TubeSlab.SlabOf.wireExterior_visible, ``TubeSlab.SlabOf.wireShore_edge,
       ``TubeSlab.SlabOf.wire_return_of_short_end_faces]),
    (``TubeSlab.SlabOf.wire_reduction_of_short_end_faces,
      [``TubeSlab.SlabOf.wire_reduction, ``TubeSlab.SlabOf.wireTwoShores,
       ``TubeSlab.SlabOf.wire_return_of_short_end_faces]),
    (``TubeSlab.SlabOf.no_two_row_short_end_faces,
      [``TubeSlab.SlabOf.no_two_row_wire_domain,
       ``TubeSlab.SlabOf.wireTwoShores,
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
  logInfo m!"Short-face two-row recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
