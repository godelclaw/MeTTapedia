import MettapediaFourColor.JointDiamondWiredOccurrence
import Lean.Util.CollectAxioms

/-! Audit of actual joint-diamond exterior closure and wiring reconstruction.
The occurrence is supplied as an exact isomorphism. Normal form derives the
wire separation, exterior connectivity and physical Kempe closure. Ambient
class preservation of the wiring and face-pattern recognition remain open. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``EightPortBoundaryConnectivity.connected_of_seven_le_card_of_boundary_card_le_eight, [``CyclicEdgeCutRealization.hasShoreOfSizeAtMost_five, ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two]),
    (``SphericalVertexLowerBound.twenty_lt_card_vertices_of_long_face, [``GoertzelV24FaceOrbitIncidence.sum_card_orbitFaceDarts_eq_card_darts]),
    (``OpenTangleIsomorphism.boundaryReindex, [``GoertzelV24OpenTangleComposition.OpenTangleData.reindexBoundary]),
    (``JointDiamondPatch.Tangle.piece_connected, []),
    (``JointDiamondPatch.Tangle.piece_returnCode, [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``JointDiamondPatch.Tangle.piece_eulerMass, [``JointDiamondPatch.Tangle.piece_face_count]),
    (``JointDiamondPatch.Tangle.Occurrence.actual_injective, []),
    (``JointDiamondPatch.Tangle.Occurrence.actual_alpha, []),
    (``JointDiamondPatch.Tangle.Occurrence.actual_rho, []),
    (``JointDiamondPatch.Tangle.Occurrence.long_face, [``JointDiamondPatch.Tangle.Occurrence.actual_injective, ``JointDiamondPatch.Tangle.Occurrence.actual_hex_step]),
    (``JointDiamondPatch.Tangle.Occurrence.twenty_lt_vertices, [``JointDiamondPatch.Tangle.Occurrence.long_face, ``SphericalVertexLowerBound.twenty_lt_card_vertices_of_long_face]),
    (``JointDiamondPatch.Tangle.Occurrence.inside_connected, [``JointDiamondPatch.Tangle.piece_connected, ``OpenTangleIsomorphism.Iso.connected]),
    (``JointDiamondPatch.Tangle.Occurrence.exterior_card, []),
    (``JointDiamondPatch.Tangle.Occurrence.exterior_connected, [``EightPortBoundaryConnectivity.connected_of_seven_le_card_of_boundary_card_le_eight, ``JointDiamondPatch.Tangle.Occurrence.twenty_lt_vertices]),
    (``JointDiamondPatch.Tangle.Occurrence.exterior_order, [``JointDiamondPatch.Tangle.piece_returnCode, ``JointDiamondPatch.Tangle.Occurrence.exterior_connected, ``GoertzelV24ComplementaryShoreBoundaryOrder.boundarySuccessors_opposite_of_planarBond]),
    (``JointDiamondPatch.Tangle.Occurrence.exterior_closed, [``JointDiamondPatch.Tangle.Occurrence.exterior_order, ``KempeMatchingChromogram.reconstruct, ``OpenTangleKempeRepair.closed_of_physical_noncrossing]),
    (``JointDiamondPatch.Tangle.Occurrence.colorable_of_joint_exterior, [``JointDiamondPatch.Tangle.Occurrence.exterior_closed, ``DiamondProfileReducibility.repair004, ``OpenTangleClosedWitness.glueOpen, ``OpenTangleIsomorphism.Iso.sewn_colorable_iff]),
    (``JointDiamondPatch.Tangle.Occurrence.wire_separated, [``PartialCubicDartSeparation.Realization.girth_of_cyclicallyFive]),
    (``JointDiamondPatch.Tangle.Occurrence.wired_vertex_decrease, [``JointDiamondPatch.Tangle.Occurrence.exterior_card]),
    (``JointDiamondPatch.Tangle.Occurrence.colorable_of_actual_wiring, [``DiamondCoupledWiring.Rotation.colorable_iff, ``OpenTangleIsomorphism.boundaryReindex, ``OpenTangleKempeRepair.trace_transport, ``JointDiamondPatch.Tangle.Occurrence.exterior_closed, ``DiamondProfileReducibility.repair004, ``OpenTangleClosedWitness.glueOpen])]
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
  logInfo m!"Joint-diamond actual occurrence: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
