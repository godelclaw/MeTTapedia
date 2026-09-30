import Mettapedia.GraphTheory.FourColor.HexagonalTubeTwistReduction
import Mettapedia.GraphTheory.FourColor.ZigzagTubeTwistGSLT
import Lean.Util.CollectAxioms

/-! Audit the algebra, actual geometry, directed witness reconstruction and
minimality consumers separately. Finite ring-stabilization certificates and
the complete classical theorem must not supply this reduction. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoSidedBoundaryReindex.cubic_reindex, []),
    (``TwoSidedBoundaryReindex.rotationCyclic_reindex, []),
    (``ZigzagRing.transfer_insert_two,
      [``ZigzagRing.Step.two_ring_shift, ``ZigzagRing.Step.rotate_step]),
    (``ZigzagRing.twistedTube_reconstruct,
      [``ZigzagRing.transfer_insert_two, ``TwoSidedBoundaryReindex.accepts_reindex,
       ``ZigzagRing.tube_accepts_iff]),
    (``ZigzagRing.twistedTube_returnCode,
      [``TwoSidedBoundaryJoint.face_reindex, ``ZigzagRing.tube_face_code]),
    (``ZigzagRing.twistedTube_class,
      [``ZigzagRing.twistedTube_returnCode, ``TwoSidedBoundaryJoint.mass_reindex,
       ``OpenTangleInternalReplacement.replacement_structural,
       ``TwoSidedBoundaryReindex.cubic_reindex, ``TwoSidedBoundaryReindex.rotationCyclic_reindex]),
    (``ZigzagRing.twistedTube_closed_reconstruct,
      [``OpenTangleClosedWitness.replace, ``ZigzagRing.twistedTube_reconstruct]),
    (``ZigzagRing.strict_twistedTube_reduction,
      [``ZigzagRing.twistedTube_vertex_loss, ``ZigzagRing.twistedTube_class,
       ``ZigzagRing.twistedTube_closed_reconstruct]),
    (``TubeSlab.SlabOf.twist_reduction,
      [``ZigzagRing.strict_twistedTube_reduction, ``TubeSlab.SlabOf.reassembled_class]),
    (``TubeSlab.SlabOf.twist_reconstruct,
      [``ZigzagRing.twistedTube_closed_reconstruct,
       ``GoertzelV24VertexSideReassembly.exists_taitColoring_of_dartEquiv]),
    (``TubeSlab.Tube.hexagonal_length_le_two,
      [``TubeSlab.Tube.literalSlab, ``TubeSlab.SlabOf.twist_reduction,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable]),
    (``TubeSlab.ZigzagSlab.pentagonWithin_one,
      [``TubeSlab.Tube.hexagonal_length_le_two, ``TubeSlab.ZigzagSlab.tube_of_not_stops,
       ``TubeSlab.ZigzagSlab.stopsWithin_iff_pentagonWithin]),
    (``ZigzagTubeTwistGSLT.boundary_predicate,
      [``ZigzagTubeTwistGSLT.reconstruction,
       ``Mettapedia.GSLT.RelationalRouteSemantics.Semantics.replaceInContext])]
  let forbidden : List Name := [
    `FourColor, `Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion,
    ``ZigzagRing.five_tube_normalize, ``ZigzagRing.tube_support_eq,
    ``ZigzagRing.transfer_adjacent_of_stabilizes, ``ZigzagRing.full_transfer_after_word_bound]
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
  logInfo m!"Cyclic-seam tube reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
