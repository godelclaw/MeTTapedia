import Mettapedia.GraphTheory.FourColor.HexagonalTwoRowWiringReduction
import Lean.Util.CollectAxioms

/-! Audit the actual free-wire rotation, its cut and face arguments,
strict decrease, exterior colour retention and embedded minimality consumer.
Neither a complete Four Colour endpoint nor finite tube stabilization may
supply this family theorem. Exterior recognition and coverage are separate. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ZigzagRing.ShiftedWiring.Geometry.data, []),
    (``ZigzagRing.ShiftedWiring.Geometry.cut_cost,
      [``OpenTangleCutDartSum.twice_cutSize]),
    (``ZigzagRing.ShiftedWiring.Geometry.structural,
      [``ZigzagRing.ShiftedWiring.Geometry.cut_cost,
       ``ZigzagRing.ShiftedWiring.Geometry.original_constant_cost,
       ``RotationCutDartSum.constant_of_structural]),
    (``ZigzagRing.ShiftedWiring.Geometry.face_count,
      [``BoundaryRewireCycles.cycle_count_rewire]),
    (``ZigzagRing.ShiftedWiring.Geometry.euler_preserved,
      [``ZigzagRing.ShiftedWiring.Geometry.face_count_opposite,
       ``ZigzagRing.tube_eulerMass, ``OpenTanglePortFaceCount.face_count]),
    (``ZigzagRing.ShiftedWiring.Geometry.reconstruct_colour,
      [``ZigzagRing.ShiftedWiring.closed_reconstruction,
       ``ZigzagRing.ShiftedWiring.Geometry.restrict_colour]),
    (``ZigzagRing.ShiftedWiring.Geometry.strict_reduction,
      [``ZigzagRing.ShiftedWiring.Geometry.replacement_class,
       ``ZigzagRing.ShiftedWiring.Geometry.vertex_loss,
       ``ZigzagRing.ShiftedWiring.Geometry.reconstruct_colour]),
    (``TubeSlab.SlabOf.wireOriginal_class,
      [``TubeSlab.SlabOf.reassembled_class, ``RotationSystemExactTransport.mapClass]),
    (``TubeSlab.SlabOf.wire_reconstruct,
      [``ZigzagRing.ShiftedWiring.Geometry.reconstruct_colour,
       ``GoertzelV24VertexSideReassembly.exists_taitColoring_of_dartEquiv]),
    (``TubeSlab.SlabOf.wire_reduction,
      [``ZigzagRing.ShiftedWiring.Geometry.replacement_class,
       ``TubeSlab.SlabOf.wireOriginal_class, ``TubeSlab.SlabOf.wire_reconstruct]),
    (``TubeSlab.SlabOf.no_two_row_wire_domain,
      [``TubeSlab.SlabOf.wire_reduction,
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
  logInfo m!"Two-row free-wire strict reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
