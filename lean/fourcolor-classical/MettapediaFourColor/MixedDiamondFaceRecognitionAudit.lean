import MettapediaFourColor.MixedDiamondFaceRecognition
import Lean.Util.CollectAxioms

/-! Audit of mixed-diamond recognition and exact whole-colouring transport.
The physical seven-port exterior closure remains an explicit endpoint premise.
This audit certifies no strict reduction or additional catalogue replacement. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PartialCubicDartSeparation.Realization.separatesWith_sound, []),
    (``MixedDiamond.separates_all, [``PartialCubicDartSeparation.Diagram.separatesWith]),
    (``MixedDiamond.vertex_injective, [``MixedDiamond.separates_all, ``PartialCubicDartSeparation.Realization.separatesWith_sound, ``PartialCubicDartSeparation.Realization.ne_of_path_four]),
    (``MixedDiamond.realization, [``FacialCoronaTraversal.pentagonal_last, ``FacialCoronaTraversal.hexagonal_last, ``PentagonalCoronaGeometry.diagramDart_rotation]),
    (``MixedDiamond.vertex_injective_of_girth, [``MixedDiamond.realization, ``MixedDiamond.vertex_injective]),
    (``PartialCubicDartSeparation.Realization.unpaired_leaves_of_internalSix, [``CyclicFiveBoundary.five_le_crossing_card, ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two, ``GoertzelV24MinimalTriangleFree.card_crossingEdgeFinset_add_twice_internal_eq_three_mul]),
    (``OpenTangleIsomorphism.Iso.mapColor_valid, []),
    (``OpenTangleIsomorphism.Iso.coloringEquiv, [``OpenTangleIsomorphism.Iso.mapColor_valid, ``OpenTangleIsomorphism.Iso.mapColor_symm]),
    (``OpenTangleKempeRepair.trace_transport, [``OpenTangleIsomorphism.Iso.mapColor_valid, ``OpenTangleIsomorphism.Iso.mapColor_boundary]),
    (``OpenTangleKempeRepair.glue_of_repair, [``OpenTangleClosedWitness.glueOpen]),
    (``OpenTangleKempeRepair.trace_valid, [``GoertzelV24PortTangleCutParity.taitSupport_subset_zeroSum]),
    (``MixedDiamondPatch.Tangle.colouring_valid, []),
    (``MixedDiamondPatch.Tangle.boundary_colouring, []),
    (``MixedDiamondPatch.Tangle.repair, [``DiamondProfileReducibility.repair002, ``DiamondProfileFamilyRepair.repair1, ``DiamondBoundarySummary.reference002]),
    (``MixedDiamondPatch.Tangle.open_repair, [``MixedDiamondPatch.Tangle.repair, ``MixedDiamondPatch.Tangle.colouring_valid, ``MixedDiamondPatch.Tangle.boundary_colouring]),
    (``MixedDiamondPatch.Tangle.Recognition.recognized, [``OpenTangleIsomorphism.ofRetainedDarts, ``PartialCubicDartSeparation.Realization.unpaired_leaves_of_internalSix, ``MixedDiamondPatch.Tangle.coordinate_flip, ``MixedDiamondPatch.Tangle.coordinate_rotate]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.recognized, [``MixedDiamond.vertex_injective_of_girth, ``MixedDiamondPatch.Tangle.Recognition.recognized, ``PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.recognized_of_minimality, [``MixedDiamondPatch.Tangle.FaceRecognition.recognized, ``cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.actual_repair, [``OpenTangleKempeRepair.trace_transport, ``MixedDiamondPatch.Tangle.open_repair, ``MixedDiamondPatch.Tangle.FaceRecognition.recognized]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.deleted_card, [``MixedDiamondPatch.Tangle.FaceRecognition.recognized]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.colorable_of_exterior_closure, [``OpenTangleKempeRepair.colorable_of_exterior, ``OpenTangleClosedWitness.glueOpen, ``DiamondProfileReducibility.repair002, ``MixedDiamondPatch.Tangle.FaceRecognition.recognized])]
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
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" then
        throwError m!"Superseded repair, catalogue certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Mixed diamond face recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    separate corona repair and original catalogue certificates absent."
