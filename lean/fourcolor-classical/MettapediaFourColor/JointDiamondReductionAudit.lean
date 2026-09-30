import MettapediaFourColor.JointDiamondOccurrenceReduction
import Lean.Util.CollectAxioms

/-! Audit of the strict coupled-wiring reduction at an actual occurrence.
The class proof must consume the joint cut lifting and exact ordered face
return. The minimal-counterexample consumer must use strict decrease and
whole-map colouring reconstruction. The local occurrence remains an input. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RotationCutDartSum.twice_cutSize, [``RotationCutDartSum.edgeDartEquiv]),
    (``RotationCutDartSum.cost_transport, []),
    (``RotationCutDartSum.structural_of_cost, [``RotationCutDartSum.twice_cutSize]),
    (``RotationCutDartSum.composite_cost, []),
    (``InternalSixCutCost.ten_le_selected, [``InternalSixCutCost.cost_crossing, ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two]),
    (``InternalSixCutCost.small_selected, [``CyclicEdgeCutRealization.hasShoreOfSizeAtMost_five]),
    (``DiamondCoupledWiring.Rotation.block_cases, []),
    (``DiamondCoupledWiring.Rotation.cut_cost, [``OpenTangleCutDartSum.twice_cutSize]),
    (``DiamondCoupledWiring.Rotation.structural, [``DiamondCoupledWiring.Rotation.cut_cost, ``RotationCutDartSum.structural_of_cost]),
    (``JointDiamondPatch.Tangle.CutLifting.extension_cost, []),
    (``JointDiamondPatch.Tangle.CutLifting.extension_size, []),
    (``JointDiamondPatch.Tangle.CutLifting.block_impossible, [``JointDiamondPatch.Tangle.CutLifting.extension_cost, ``JointDiamondPatch.Tangle.CutLifting.extension_size]),
    (``JointDiamondPatch.Tangle.CutLifting.structural, [``JointDiamondPatch.Tangle.CutLifting.block_impossible, ``DiamondCoupledWiring.Rotation.block_cases]),
    (``JointDiamondPatch.Tangle.Occurrence.source_cost, [``RotationCutDartSum.cost_transport, ``JointDiamondPatch.Tangle.Occurrence.sourceDarts_alpha, ``JointDiamondPatch.Tangle.Occurrence.sourceDarts_vertex]),
    (``JointDiamondPatch.Tangle.Occurrence.sourceDarts_rotation, [``OpenTangleIsomorphism.boundaryReindex]),
    (``JointDiamondPatch.Tangle.Occurrence.wired_structural, [``JointDiamondPatch.Tangle.CutLifting.structural, ``InternalSixCutCost.ten_le_selected, ``InternalSixCutCost.small_selected, ``JointDiamondPatch.Tangle.Occurrence.source_cost, ``JointDiamondPatch.Tangle.Occurrence.exterior_connected]),
    (``OpenTanglePortFaceCount.face_count, [``FaceReturnSum.nextHitPerm_sum, ``OpenTangleReplacementEuler.observed_face_count]),
    (``DiamondCoupledWiring.Rotation.face_phi, []),
    (``DiamondCoupledWiring.Rotation.face_count, [``DiamondCoupledWiring.Rotation.face_phi, ``BoundaryRewireCycles.cycle_count_rewire]),
    (``DiamondCoupledWiring.Rotation.face_count_opposite, [``DiamondCoupledWiring.Rotation.face_count]),
    (``DiamondCoupledWiring.Rotation.cubic, []),
    (``DiamondCoupledWiring.Rotation.rotation_cyclic, []),
    (``JointDiamondPatch.Tangle.Occurrence.original_class, [``RotationSystemExactTransport.mapClass, ``JointDiamondPatch.Tangle.Occurrence.sourceDarts_rotation]),
    (``JointDiamondPatch.Tangle.Occurrence.normalized_return, [``JointDiamondPatch.Tangle.Occurrence.exterior_order, ``OpenTangleIsomorphism.Iso.returnCode]),
    (``JointDiamondPatch.Tangle.Occurrence.wired_face_decrease, [``JointDiamondPatch.Tangle.Occurrence.normalized_return, ``OpenTanglePortFaceCount.face_count, ``DiamondCoupledWiring.Rotation.face_count_opposite]),
    (``JointDiamondPatch.Tangle.Occurrence.wired_class, [``JointDiamondPatch.Tangle.Occurrence.wired_structural, ``JointDiamondPatch.Tangle.Occurrence.wired_face_decrease, ``DiamondCoupledWiring.Rotation.cubic, ``DiamondCoupledWiring.Rotation.rotation_cyclic]),
    (``JointDiamondPatch.Tangle.Occurrence.strict_reduction_of_occurrence, [``JointDiamondPatch.Tangle.Occurrence.wired_vertex_decrease, ``JointDiamondPatch.Tangle.Occurrence.wired_class, ``JointDiamondPatch.Tangle.Occurrence.colorable_of_actual_wiring, ``DiamondProfileReducibility.repair004]),
    (``JointDiamondPatch.Tangle.Occurrence.not_in_minimal_counterexample_of_occurrence, [``JointDiamondPatch.Tangle.Occurrence.strict_reduction_of_occurrence, ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
  let forbidden : List Name := [
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondSplitRepair.base_repair, `FourColor.DiamondBoundaryRepair.repair,
    `FourColor.DiamondJointRepair.contract_repair, `FourColor.coversRec,
    `FourColor.coversRec_sound, `FourColor.PentagonalLobePatch.repair,
    `FourColor.PentagonalLobePatch.boundary_repair,
    `FourColor.PentagonalLobePatch.terminalCodes,
    `FourColor.PentagonalLobePatch.terminal_supported,
    `Mettapedia.GraphTheory.FourColor.PentagonalCoronaSeparation.separates_all]
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
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.contains "finite_translation" || name.toString.contains "finiteArcWitness" then
        throwError m!"Enumerated translation, superseded repair, catalogue certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Joint-diamond strict occurrence reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
