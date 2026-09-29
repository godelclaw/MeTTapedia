import MettapediaFourColor.PentagonalLobeEmbeddedReduction
import Lean.Util.CollectAxioms

/-! Dependency audit of exact embedded recognition, geometry and reconstruction. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OpenTangleClosedWitness.restrictOpen, [``OpenTangleClosedWitness.IsColor]),
    (``OpenTangleClosedWitness.glueOpen,
      [``GoertzelV24RotationDartColoring.edgeColoringOfDartColor]),
    (``OpenTangleIsomorphism.Iso.returnCode,
      [``GoertzelV24RetainedRegionBoundaryOrder.nextHitPerm_permCongr]),
    (``OpenTangleIsomorphism.Iso.sewn_class,
      [``RotationSystemExactTransport.mapClass]),
    (``OpenTangleVertexSideReturn.returnCode_eq,
      [``GoertzelV24RetainedRegionBoundaryOrder.nextHitPerm_permCongr,
        ``OpenTangleVertexSideReturn.face_perm]),
    (``VertexSideExactReassembly.mapClass,
      [``RotationSystemExactTransport.mapClass, ``VertexSideExactReassembly.rotation]),
    (``SixPortBoundaryReflection.orderedPhysicalMate_isNoncrossing_inverse,
      [``GoertzelV24PhysicalKempeNoncrossingClosure.orderedPhysicalMate_isNoncrossing,
        ``SixPortBoundaryReflection.chordsCross_rev_iff]),
    (``PentagonalLobePatch.Tangle.piece_connected, []),
    (``PentagonalLobePatch.Tangle.Embedded.inside_connected,
      [``PentagonalLobePatch.Tangle.piece_connected, ``OpenTangleIsomorphism.Iso.connected]),
    (``PentagonalLobePatch.Tangle.Embedded.exterior_order,
      [``GoertzelV24ComplementaryShoreBoundaryOrder.boundarySuccessors_opposite_of_planarBond,
        ``OpenTangleIsomorphism.Iso.returnCode, ``OpenTangleVertexSideReturn.returnCode_eq,
        ``PentagonalLobePatch.Tangle.piece_returnCode]),
    (``PentagonalLobePatch.Tangle.Embedded.exterior_noncrossing,
      [``PentagonalLobePatch.Tangle.Embedded.exterior_order,
        ``SixPortBoundaryReflection.orderedPhysicalMate_isNoncrossing_inverse,
        ``GoertzelV24FaceDualConnectedness.orbitFaceInteriorDual_connected]),
    (``PentagonalLobePatch.Tangle.Embedded.strict_reduction,
      [``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.tree_replacement_class,
        ``PentagonalLobePatch.Tangle.Embedded.exterior_noncrossing,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree,
        ``PentagonalLobePatch.compatible_colouring,
        ``OpenTangleClosedWitness.restrictOpen, ``OpenTangleClosedWitness.glueOpen,
        ``PentagonalLobePatch.Tangle.Embedded.reassembled_colorable_iff]),
    (``PentagonalLobePatch.Tangle.Embedded.not_in_minimal_counterexample,
      [``PentagonalLobePatch.Tangle.Embedded.strict_reduction])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondConfigurations, `FourColor.DiamondFamilyReducibility,
    `FourColor.DiamondProfileReducibility]
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
        throwError m!"Configuration certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Embedded pentagonal lobe reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
