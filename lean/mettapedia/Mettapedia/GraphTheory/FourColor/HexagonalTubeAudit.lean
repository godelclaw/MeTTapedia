import Mettapedia.GraphTheory.FourColor.HexagonalTubeExclusion
import Mettapedia.GraphTheory.FourColor.HexagonalTubeReduction
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
