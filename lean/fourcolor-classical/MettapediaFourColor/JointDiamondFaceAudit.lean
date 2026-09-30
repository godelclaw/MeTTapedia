import MettapediaFourColor.JointDiamondFaceReduction
import Lean.Util.CollectAxioms

/-! Audit of recognition from the four-face traversal. The distinctness
proof must consume joint equality transport and the cut obstruction. The
strict reduction must consume the constructed occurrence. The outgoing-port
check remains an explicit hypothesis, rather than an audited conclusion. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CubicDartStar.injective, []),
    (``CubicDartStar.surjective_at, []),
    (``PartialCubicDartSeparation.Realization.crossing_card_le_of_internal,
      [``PartialCubicDartSeparation.Realization.crossingIndex_injective]),
    (``JointDiamond.separates_nonexceptional, []),
    (``JointDiamond.terminal_sound, [``PartialCubicDartSeparation.Realization.ne_of_path_four]),
    (``JointDiamond.exceptional_dart_eq, [``JointDiamond.separates_nonzero_phase,
      ``PartialCubicDartSeparation.Realization.separatesWith_sound]),
    (``JointDiamond.twelve_le_image, [``JointDiamond.ne_nonexceptional]),
    (``JointDiamond.exceptional_internal, []),
    (``JointDiamond.exceptional_ne, [``JointDiamond.exceptional_dart_eq,
      ``JointDiamond.exceptional_internal, ``JointDiamond.twelve_le_image,
      ``PartialCubicDartSeparation.Realization.crossing_card_le_of_internal,
      ``CyclicFiveBoundary.five_le_crossing_card]),
    (``JointDiamond.vertex_injective, [``JointDiamond.exceptional_ne, ``JointDiamond.separates_all]),
    (``JointDiamond.realization, [``FacialCoronaTraversal.pentagonal_last,
      ``FacialCoronaTraversal.hexagonal_last, ``CubicDartStar.surjective_at]),
    (``JointDiamondPatch.Tangle.coordinate_rotate, []),
    (``JointDiamondPatch.Tangle.coordinate_flip, []),
    (``JointDiamondPatch.Tangle.Recognition.recognized, [``JointDiamond.realization,
      ``OpenTangleIsomorphism.ofRetainedDarts]),
    (``JointDiamondPatch.Tangle.FaceReduction.vertex_injective, [``JointDiamond.vertex_injective,
      ``JointDiamond.realization, ``PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive]),
    (``JointDiamondPatch.Tangle.FaceReduction.strict_reduction_of_checked_face_pattern,
      [``JointDiamondPatch.Tangle.FaceReduction.vertex_injective,
       ``JointDiamondPatch.Tangle.Recognition.recognized,
       ``JointDiamondPatch.Tangle.Occurrence.strict_reduction_of_occurrence,
       ``DiamondProfileReducibility.repair004]),
    (``JointDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_checked_face_pattern,
      [``JointDiamondPatch.Tangle.FaceReduction.recognized,
       ``JointDiamondPatch.Tangle.Occurrence.not_in_minimal_counterexample_of_occurrence,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
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
  logInfo m!"Joint-diamond face recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
