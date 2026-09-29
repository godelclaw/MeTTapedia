import Mettapedia.GraphTheory.FourColor.HexagonalTubeExclusion
import Mettapedia.GraphTheory.FourColor.HexagonalTubeReduction
import Mettapedia.GraphTheory.FourColor.HexagonalCollarProgress
import Mettapedia.GraphTheory.FourColor.AlternatingCycleRecognition
import Mettapedia.GraphTheory.FourColor.AlternatingWalkLobes
import Mettapedia.GraphTheory.FourColor.CycleSeamTransfer
import Lean.Util.FoldConsts

/-!
# Dependency audit of geometric recognition and physical tube reduction

The checked endpoints must consume actual face geometry, colouring-witness
composition, exact exterior sewing and physical strict reduction. None may use the classical Four
Colour theorem or its configuration catalogue.
-/

open Mettapedia.GraphTheory.FourColor
open TubeSlab

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``CyclicPortSeam.translation_of_six_steps,
      [``CyclicPortSeam.successor_of_six_steps, ``CyclicPortSeam.translation_of_successor]),
    (``CyclicPortSeam.six_steps_of_successor, [``CyclicPortSeam.three_steps_left]),
    (``ZigzagSlab.seam_eq_add, [``CyclicPortSeam.translation_of_six_steps,
      ``ZigzagSlab.seam_mate, ``ZigzagSlab.input_three_steps, ``ZigzagSlab.output_three_steps,
      ``GoertzelV24HexFaceRungType.faceOrbit_isCycleOn]),
    (``ZigzagSlab.two_row_support, [``ZigzagSlab.seam_eq_add,
      ``ZigzagSlab.mem_sideSupport_inner'_iff, ``ZigzagRing.Step.rotate_step]),
    (``Tube.Hexagonal.cyclicCoherent, [``ZigzagSlab.seam_eq_add]),
    (``Tube.sideSet_aligned, [``ZigzagSlab.sideSet_atOrigin,
      ``ZigzagSlab.mem_sideSupport_inner'_iff]),
    (``Tube.sideSet_aligned_stable, [``Tube.sideSet_aligned, ``Tube.stepS_iterate_stable]),
    (``le_of_tube_nodes, [``le_of_stationary_nodes, ``Tube.sideSet_eq_of_le]),
    (``Tube.hexagonal_five_length_bound, [``Tube.Hexagonal.cyclicCoherent,
      ``Tube.sideSet_aligned_eq_of_le, ``GoertzelV24FiveTubeExclusion.five_ring_stabilizes,
      ``le_of_stationary_nodes, ``GoertzelV24MajorityShoreStateDescent.cardPhasedState_ne_of_ssubset]),
    (``FacialCycleChord.toSlab_rotationCompatible,
      [``FacialCycleLayer.BoundsFaces.embedding_rho]),
    (``FacialCycleChord.prepend_hexagonal,
      [``FacialCycleChord.toSlab_rotationCompatible]),
    (``FacialCycleChord.chain_length_bound, [``FacialCycleChord.prepend_hexagonal,
      ``FacialCycleChord.toSlab, ``FacialCycleChord.toCycle,
      ``Tube.le_of_hexagonal, ``CyclicPortSeam.translation_of_six_steps,
      ``GoertzelV24MajorityShoreStateDescent.cardPhasedState_ne_of_ssubset])]
  let contracts := contracts ++ [
    (``SlabOf.assemble_rotationCompatible, [``SlabOf.matching_mate]),
    (``Tube.literalSlab, [``Tube.assembleRings, ``SlabOf.assembleWith,
      ``SlabOf.shiftRing, ``ZigzagSlab.seam_eq_add]),
    (``SlabOf.reassembled_colorable_iff, [``SlabOf.outsidePort_surjective,
      ``SlabOf.reassemblyDartEquiv_alpha, ``SlabOf.reassemblyDartEquiv_vert]),
    (``SlabOf.reassembled_class, [``SlabOf.reassemblyDartEquiv_rho,
      ``RotationSystemExactTransport.mapClass]),
    (``OpenTangleClosedWitness.replace, [``OpenTangleClosedWitness.restrict,
      ``OpenTangleClosedWitness.glue]),
    (``SlabOf.five_vertex_loss, [``SlabOf.exteriorVertexEquiv, ``ZigzagRing.tube_vertex_card]),
    (``SlabOf.five_reduction, [``SlabOf.reassembled_class,
      ``ZigzagRing.tube_replacement_class, ``OpenTangleClosedWitness.colorable_iff,
      ``ZigzagRing.five_tube_support, ``GoertzelV24FiveTubeExclusion.five_ring_stabilizes]),
    (``SlabOf.five_reconstruct, [``OpenTangleClosedWitness.replace,
      ``GoertzelV24VertexSideReassembly.exists_taitColoring_of_dartEquiv]),
    (``Tube.hexagonal_five_length_le_four, [``Tube.literalSlab, ``SlabOf.five_reduction,
      ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable]),
    (``FacialCycleChord.chain_length_le_four, [``FacialCycleChord.prepend_hexagonal,
      ``FacialCycleChord.toSlab, ``FacialCycleChord.toCycle,
      ``Tube.hexagonal_five_length_le_four])]
  let contracts := contracts ++ [
    (``ZigzagSlab.collar_three_steps, [``ZigzagSlab.output_three_steps,
      ``ZigzagSlab.seam_six_steps]),
    (``ZigzagSlab.nextRow, [``ZigzagSlab.collar_second_edge,
      ``ZigzagSlab.collarDart_injective, ``ZigzagSlab.collarVertex_outside,
      ``ZigzagSlab.collar_output_no_chord, ``CyclicPortChordExclusion.Arcs.no_chord,
      ``ZigzagSlab.outPort_surjective]),
    (``ZigzagSlab.nextRow_inEquiv, [``ZigzagSlab.nextRow]),
    (``ZigzagSlab.collarVertex_eq_successor, [``ZigzagSlab.seam_mate]),
    (``ZigzagSlab.exists_nextRow_iff, [``ZigzagSlab.nextRow,
      ``ZigzagSlab.collarVertex_injective_of_successor]),
    (``ZigzagSlab.nextRow_support, [``ZigzagSlab.nextRow_inEquiv,
      ``ZigzagSlab.mem_sideSupport_inner'_iff]),
    (``ZigzagSlab.tube_of_not_stops, [``ZigzagSlab.nextRow,
      ``ZigzagSlab.clean_of_no_obstruction]),
    (``ZigzagSlab.stopsWithin_three, [``ZigzagSlab.tube_of_not_stops,
      ``Tube.hexagonal_five_length_le_four, ``SlabOf.five_reduction])]
  let contracts := contracts ++ [
    (``ZigzagSlab.collarMiddle_outside, [``ZigzagSlab.collar_second_edge,
      ``ZigzagSlab.outPort_surjective]),
    (``ZigzagSlab.collarReflection_impossible, [``ZigzagSlab.collarReflection_step,
      ``ZigzagSlab.collar_second_edge]),
    (``ZigzagSlab.collarVertex_injective, [``ZigzagSlab.collarReflection_impossible,
      ``ZigzagSlab.collarInput_vertex_injective, ``ZigzagSlab.collarMiddle_vertex_injective]),
    (``ZigzagSlab.hexagonalNextRow, [``ZigzagSlab.collarVertex_injective,
      ``ZigzagSlab.nextRow]),
    (``ZigzagSlab.hexagonalNextRow_support, [``ZigzagSlab.collarVertex_injective,
      ``ZigzagSlab.nextRow_support]),
    (``ZigzagSlab.collarObstruction_iff_pentagonalSeam, [``ZigzagSlab.collarVertex_injective]),
    (``ZigzagSlab.pentagonWithin_card, [``ZigzagSlab.stopsWithin_iff_pentagonWithin,
      ``ZigzagSlab.tube_of_not_stops, ``Tube.literalSlab]),
    (``ZigzagSlab.pentagonWithin_three, [``ZigzagSlab.collarVertex_injective,
      ``ZigzagSlab.stopsWithin_three, ``SlabOf.five_reduction])]
  let contracts := contracts ++ [
    (``InducedCycleLayer.Frame.exists_cycle, [``InducedCycleLayer.rowIndex_injective,
      ``InducedCycleLayer.rowIndex_next]),
    (``AlternatingCycleRecognition.exists_facial_sides,
      [``InducedCycleLayer.Frame.exists_cycle,
      ``GoertzelV24PrimalCycleFacialBond.exists_faceSet_bond_of_isCycle,
      ``GoertzelV24PrimalCycleFacialBond.face_sides_connected_of_isCycle]),
    (``AlternatingCycleRecognition.alternating_degrees,
      [``FacialCycleLayer.BoundsFaces.rotation_at]),
    (``AlternatingCycleRecognition.row, [``AlternatingCycleRecognition.exists_facial_sides,
      ``AlternatingCycleRecognition.alternating_degrees, ``FacialCycleChord.toSlab]),
    (``AlternatingCycleRecognition.row_support, [``AlternatingCycleRecognition.row,
      ``ZigzagSlab.mem_sideSupport_inner'_iff]),
    (``AlternatingCycleRecognition.recognized_pentagonWithin,
      [``AlternatingCycleRecognition.row, ``ZigzagSlab.pentagonWithin_card]),
    (``AlternatingCycleRecognition.recognized_pentagonWithin_three,
      [``AlternatingCycleRecognition.row, ``ZigzagSlab.pentagonWithin_three,
      ``SlabOf.five_reduction])]
  let contracts := contracts ++ [
    (``AlternatingWalkLobes.exists_simple_segment,
      [``Finite.exists_ne_map_eq_of_infinite, ``SimpleGraph.Walk.ofDarts]),
    (``AlternatingWalkLobes.trajectory_phase, [``AlternatingWalkLobes.step]),
    (``AlternatingWalkLobes.internal_transition, [``AlternatingWalkLobes.trajectory_succ]),
    (``AlternatingWalkLobes.step_nonbacktracking,
      [``PhysicalForkCodeFaces.Cubic3.cube, ``PhysicalForkCodeFaces.Cubic3.moves]),
    (``AlternatingWalkLobes.exists_simple_lobe, [``AlternatingWalkLobes.exists_simple_segment,
      ``AlternatingWalkLobes.step_nonbacktracking]),
    (``AlternatingWalkLobes.exists_separating_lobe, [``AlternatingWalkLobes.exists_simple_lobe,
      ``GoertzelV24PrimalCycleFacialBond.exists_faceSet_bond_of_isCycle,
      ``GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided])]
  let contracts := contracts ++ [
    (``CycleSeamTransfer.marked_iff, [``CycleSeamTransfer.edges_valid,
      ``CycleSeamTransfer.spokes_edges, ``CycleCap.coloringOf_isTait]),
    (``CycleSeamTransfer.spokes_collapse, [``CycleSeamTransfer.skip_next]),
    (``CycleSeamTransfer.reconstruct_spokes, [``CycleSeamTransfer.spokes_insert,
      ``BoundaryWordFrontier.expand_contract]),
    (``CycleSeamTransfer.marked_contract_iff, [``CycleSeamTransfer.marked_iff,
      ``CycleSeamTransfer.collapse_valid, ``CycleSeamTransfer.reconstruct_valid,
      ``CycleSeamTransfer.reconstruct_spokes]),
    (``CycleSeamTransfer.marked_contract_in_context,
      [``CycleSeamTransfer.marked_contract_iff]),
    (``CycleSeamTransfer.accepts_contract_iff,
      [``CycleSeamTransfer.marked_contract_iff, ``CycleSeamTransfer.accepts_iff_marked]),
    (``CycleSeamTransfer.blockedWord_not_accepted,
      [``CycleSeamTransfer.blockedWord_no_edges, ``CycleSeamTransfer.marked_iff]),
    (``CycleSeamTransfer.blockedWord_contraction_accepted,
      [``CycleSeamTransfer.marked_iff, ``CycleCap.coloringOf_isTait])]
  let mut inspected : NameSet := {}
  for (root, required) in contracts do
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
      if (`FourColor).isPrefixOf name then
        throwError m!"Classical FourColor dependency in geometric seam theorem {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Hexagonal recognition and reduction: {contracts.length} roots; \
    {inspected.toList.length} declarations in their combined dependency closure; \
    no classical FourColor dependencies."
