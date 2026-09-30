import MettapediaFourColor.MixedDiamondExteriorClosure
import Lean.Util.CollectAxioms

/-! Audit the arbitrary-width codec and its actual seven-port consumer.
Every matching answer reconstructs through the same physical components.
Initial exterior colourability remains explicit; strict reduction is not claimed. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``NoncrossingMatchingStack.stack_close, [``NoncrossingMatchingStack.stack_advance]),
    (``OrderedCyclicArcs.witness_of_lt, [``OrderedCyclicArcs.iterate_val]),
    (``KempeMatchingChromogram.Stack.accepted, [``NoncrossingMatchingStack.stack_close, ``KempeMatchingChromogram.Stack.matchStep_eq]),
    (``KempeMatchingChromogram.Stack.mask_constant, [``KempeMatchingChromogram.Stack.paired_read, ``NoncrossingMatchingStack.stack_close]),
    (``KempeMatchingChromogram.translation, [``KempeMatchingChromogram.Stack.accepted, ``KempeMatchingChromogram.Stack.mask_constant, ``KempeMatchingChromogram.liftMate_noncrossing]),
    (``KempeMatchingChromogram.reconstruct, [``KempeMatchingChromogram.translation, ``KempeMatchingChromogram.difference_paired, ``KempeMatchingChromogram.matches_related]),
    (``PhysicalKempeBoundary.ordered_closed, [``KempeMatchingChromogram.reconstruct, ``NoncrossingMatchingStack.stack_close]),
    (``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing, [``OrderedCyclicArcs.witness_of_lt, ``GoertzelV24PhysicalKempeNoncrossing.no_distinct_kempe_components_between_boundary_arcs]),
    (``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing_five, [``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing]),
    (``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing_inverse, [``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing, ``Compositional.CyclicBoundaryMatching.rev_cycle]),
    (``OpenTangleKempeRepair.closed_of_physical_noncrossing, [``KempeMatchingChromogram.reconstruct, ``Compositional.BoundaryKempeSwitch.switchBoundaryWord_mem_supportInCoordinates, ``OpenTangleKempeRepair.trace_of_support]),
    (``SevenPortBoundaryConnectivity.connected_of_cycles_of_boundary_card_lt_eight, [``SixPortBoundaryConnectivity.three_le_componentPorts, ``GoertzelV24CyclicThreeCutConnectedSides.hasCycleOnSide_inducedReachableSide]),
    (``SevenPortBoundaryConnectivity.connected_of_six_le_card_of_boundary_card_le_seven, [``SevenPortBoundaryConnectivity.connected_of_cycles_of_boundary_card_lt_eight, ``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two]),
    (``MixedDiamondPatch.Tangle.piece_connected, []),
    (``MixedDiamondPatch.Tangle.piece_returnCode, [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``MixedDiamondPatch.Tangle.piece_eulerMass, [``MixedDiamondPatch.Tangle.piece_face_count]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.exterior_connected, [``SevenPortBoundaryConnectivity.connected_of_six_le_card_of_boundary_card_le_seven, ``MixedDiamondPatch.Tangle.FaceRecognition.recognized, ``SphericalVertexLowerBound.twenty_le_card_vertices]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.exterior_order, [``MixedDiamondPatch.Tangle.FaceRecognition.exterior_connected, ``MixedDiamondPatch.Tangle.piece_returnCode, ``GoertzelV24ComplementaryShoreBoundaryOrder.boundarySuccessors_opposite_of_planarBond]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.exterior_closed, [``OpenTangleKempeRepair.closed_of_physical_noncrossing, ``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing_inverse, ``MixedDiamondPatch.Tangle.FaceRecognition.exterior_order]),
    (``MixedDiamondPatch.Tangle.FaceRecognition.colorable_of_exterior, [``MixedDiamondPatch.Tangle.FaceRecognition.exterior_closed, ``OpenTangleClosedWitness.glueOpen, ``DiamondProfileReducibility.repair002])]
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
  logInfo m!"Uniform matching and mixed-diamond exterior: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
