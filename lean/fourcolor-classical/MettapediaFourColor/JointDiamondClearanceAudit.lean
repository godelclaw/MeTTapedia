import MettapediaFourColor.JointDiamondFaceClearance
import Lean.Util.CollectAxioms

/-! Audit of complete four-face recognition and strict reduction. Boundary
clearance must follow from the actual capped-face transport and planar bond,
with no occurrence isomorphism or colouring supplied as a local premise. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PartialCubicDartSeparation.Realization.unpaired_mate,
      [``PartialCubicDartSeparation.Realization.dart_injective]),
    (``PartialCubicDartSeparation.Realization.unpaired_no_short_path,
      [``PartialCubicDartSeparation.Realization.unpaired_not_recorded]),
    (``PartialCubicDartSeparation.Realization.image_connected,
      [``PartialCubicDartSeparation.Realization.reachable_of_path]),
    (``PartialCubicDartSeparation.Realization.allowed_leaves_of_six,
      [``PartialCubicDartSeparation.Realization.crossing_card_le_of_internal,
       ``CyclicFiveBoundary.five_le_crossing_card]),
    (``JointDiamondPatch.Tangle.Chord.remaining_card, []),
    (``JointDiamondPatch.Tangle.Chord.label_invariant, []),
    (``JointDiamondPatch.Tangle.Chord.not_sameCycle,
      [``JointDiamondPatch.Tangle.Chord.label_invariant,
       ``JointDiamondPatch.Tangle.Chord.separated_ports]),
    (``JointDiamondPatch.Tangle.FaceClearance.side_card,
      [``JointDiamond.vertex_injective]),
    (``JointDiamondPatch.Tangle.FaceClearance.twenty_lt_vertices,
      [``SphericalVertexLowerBound.twenty_lt_card_vertices_of_long_face]),
    (``JointDiamondPatch.Tangle.FaceClearance.inside_connected,
      [``PartialCubicDartSeparation.Realization.image_connected]),
    (``JointDiamondPatch.Tangle.FaceClearance.outside_connected,
      [``EightPortBoundaryConnectivity.connected_of_seven_le_card_of_boundary_card_le_eight]),
    (``JointDiamondPatch.Tangle.FaceClearance.ports_cofacial,
      [``OpenTangleVertexSideReturn.ports_cofacial_of_planarBond,
       ``OpenTangleVertexSideReturn.face_perm]),
    (``JointDiamondPatch.Tangle.FaceClearance.remaining_leaves,
      [``PartialCubicDartSeparation.Realization.allowed_leaves_of_six]),
    (``JointDiamondPatch.Tangle.FaceClearance.chord_face_perm,
      [``JointDiamondPatch.Tangle.FaceClearance.remaining_leaves,
       ``JointDiamondPatch.Tangle.coordinate_flip,
       ``JointDiamondPatch.Tangle.coordinate_rotate]),
    (``JointDiamondPatch.Tangle.FaceClearance.boundary_clear,
      [``PartialCubicDartSeparation.Realization.unpaired_mate,
       ``PartialCubicDartSeparation.Realization.unpaired_no_short_path,
       ``JointDiamondPatch.Tangle.FaceClearance.ports_cofacial,
       ``JointDiamondPatch.Tangle.FaceClearance.chord_face_perm,
       ``JointDiamondPatch.Tangle.Chord.not_sameCycle]),
    (``JointDiamondPatch.Tangle.FaceClearance.recognized,
      [``JointDiamondPatch.Tangle.FaceClearance.boundary_clear,
       ``OpenTangleIsomorphism.ofRetainedDarts]),
    (``JointDiamondPatch.Tangle.FaceClearance.strict_reduction_of_face_pattern,
      [``JointDiamondPatch.Tangle.FaceClearance.boundary_clear,
       ``JointDiamondPatch.Tangle.Occurrence.strict_reduction_of_occurrence,
       ``DiamondProfileReducibility.repair004]),
    (``JointDiamondPatch.Tangle.FaceClearance.not_in_minimal_counterexample_of_face_pattern,
      [``JointDiamondPatch.Tangle.FaceClearance.boundary_clear,
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
  logInfo m!"Joint-diamond boundary clearance: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
