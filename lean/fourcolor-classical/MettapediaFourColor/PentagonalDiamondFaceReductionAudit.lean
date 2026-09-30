import MettapediaFourColor.PentagonalDiamondFaceReduction
import Lean.Util.CollectAxioms

/-! Audit of the four-face recognition, shared repair and strict reduction.
The older corona repair is excluded from every audited dependency closure. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PartialCubicDartSeparation.Realization.ne_of_path_four, [``PartialCubicDartSeparation.Realization.ne_of_path_two]),
    (``PentagonalDiamond.separates_or_ends, [``PartialCubicDartSeparation.Diagram.separates]),
    (``PentagonalDiamond.vertex_injective, [``PentagonalDiamond.separates_or_ends, ``PartialCubicDartSeparation.Realization.separates_sound, ``PartialCubicDartSeparation.Realization.ne_of_path_four]),
    (``PentagonalDiamond.realization, [``FacialCoronaTraversal.pentagonal_last, ``PentagonalCoronaGeometry.diagramDart_rotation]),
    (``PentagonalDiamond.vertex_injective_of_girth, [``PentagonalDiamond.realization, ``PentagonalDiamond.vertex_injective]),
    (``PartialCubicDartSeparation.Realization.unpaired_leaves_of_cyclicallyFive, [``CyclicFiveBoundary.five_le_crossing_card, ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two, ``GoertzelV24MinimalTriangleFree.card_crossingEdgeFinset_add_twice_internal_eq_three_mul]),
    (``PentagonalDiamondPatch.Tangle.colouring_valid, []),
    (``PentagonalDiamondPatch.Tangle.boundary_colouring, []),
    (``PentagonalDiamondPatch.Tangle.repair, [``DiamondProfileReducibility.repair001, ``DiamondProfileFamilyRepair.repair0, ``DiamondProfileReducibility.supports_graph]),
    (``PentagonalDiamondPatch.Tangle.open_repair, [``PentagonalDiamondPatch.Tangle.repair, ``PentagonalDiamondPatch.Tangle.colouring_valid, ``PentagonalDiamondPatch.Tangle.boundary_colouring]),
    (``SixPortTreeReplacement.open_colorable, [``PentagonalLobePatch.Tangle.open_exterior_closed, ``OpenTangleClosedWitness.glueOpen]),
    (``SixPortTreeReplacement.tree_replacement_class, [``OpenTangleConnectedReplacement.replacement_structural, ``SixPortTreeReplacement.tree_replacement_euler]),
    (``SixPortTreeReplacement.Embedded.strict_reduction, [``SixPortTreeReplacement.Embedded.size_decrease, ``SixPortTreeReplacement.open_reconstruct_from_tree, ``SixPortTreeReplacement.Embedded.exterior_noncrossing]),
    (``PentagonalDiamondPatch.Tangle.Recognition.recognized, [``OpenTangleIsomorphism.ofRetainedDarts, ``PartialCubicDartSeparation.Realization.unpaired_leaves_of_cyclicallyFive, ``PentagonalDiamondPatch.Tangle.coordinate_flip, ``PentagonalDiamondPatch.Tangle.coordinate_rotate]),
    (``PentagonalDiamondPatch.Tangle.FaceReduction.recognized, [``PentagonalDiamond.vertex_injective_of_girth, ``PentagonalDiamondPatch.Tangle.Recognition.recognized, ``PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive]),
    (``PentagonalDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern, [``PentagonalDiamondPatch.Tangle.FaceReduction.recognized, ``SixPortTreeReplacement.Embedded.strict_reduction, ``SixPortTreeReplacement.Embedded.exterior_connected, ``DiamondProfileReducibility.repair001]),
    (``PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern, [``PentagonalDiamondPatch.Tangle.FaceReduction.recognized, ``SixPortTreeReplacement.Embedded.not_in_minimal_counterexample_of_recognition, ``SixPortTreeReplacement.Embedded.size_decrease]),
    (``PentagonalDiamondPatch.Tangle.FaceReduction.corona_excluded_via_diamond, [``PentagonalDiamondPatch.Tangle.FaceReduction.ofCorona, ``PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern, ``DiamondProfileReducibility.repair001])]
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
  logInfo m!"Pentagonal diamond face reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    separate corona repair and original catalogue certificates absent."
