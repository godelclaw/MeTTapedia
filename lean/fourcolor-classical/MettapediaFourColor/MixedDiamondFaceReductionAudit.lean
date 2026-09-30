import MettapediaFourColor.MixedDiamondFaceReduction
import MettapediaFourColor.SixPortTreeReplacement
import Lean.Util.CollectAxioms

/-! Audit of the mixed-diamond strict reduction and its shared geometric law.
The complete colouring reconstruction retains actual exterior witnesses and
physical Kempe components. Thirteen removed vertices and five introduced
vertices are counted in the whole-map decrease of eight. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OpenTangleReplacementClass.mapClass, [``OpenTanglePortReplacement.euler_eq_iff_mass, ``OpenTangleConnectedReplacement.replacement_structural, ``OpenTangleVertexReflection.exterior_isCubic, ``OpenTangleVertexReflection.exterior_rotationCyclic]),
    (``SixPortTreeReplacement.tree_replacement_class, [``OpenTangleReplacementClass.mapClass]),
    (``SevenPortTree.cubic, []),
    (``SevenPortTree.cyclic, []),
    (``SevenPortTree.connected, []),
    (``SevenPortTree.ports_surjective, []),
    (``SevenPortTree.piece_returnCode, [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``SevenPortTree.piece_eulerMass, [``SevenPortTree.piece_face_count]),
    (``MixedDiamondPatch.Tangle.FaceReduction.reassembled_class, [``MixedDiamondPatch.Tangle.FaceRecognition.recognized, ``OpenTangleIsomorphism.Iso.sewn_class, ``VertexSideExactReassembly.mapClass]),
    (``MixedDiamondPatch.Tangle.FaceReduction.smaller_class, [``OpenTangleReplacementClass.mapClass, ``MixedDiamondPatch.Tangle.FaceRecognition.exterior_connected, ``SevenPortTree.ports_surjective, ``SevenPortTree.piece_returnCode, ``SevenPortTree.piece_eulerMass]),
    (``MixedDiamondPatch.Tangle.FaceReduction.size_decrease, [``MixedDiamondPatch.Tangle.FaceRecognition.exterior_card]),
    (``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller, [``OpenTangleClosedWitness.restrictOpen, ``MixedDiamondPatch.Tangle.FaceRecognition.exterior_closed, ``KempeMatchingChromogram.reconstruct, ``OpenTangleClosedWitness.glueOpen, ``DiamondProfileReducibility.repair002]),
    (``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern, [``MixedDiamondPatch.Tangle.FaceReduction.smaller_class, ``MixedDiamondPatch.Tangle.FaceReduction.size_decrease, ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller]),
    (``MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern, [``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern, ``GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample, ``cubicDualInternallySixConnected_of_vertexMinimalTaitCounterexample])]
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
  logInfo m!"Mixed-diamond strict reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    enumerated matching translations, original catalogue certificates and complete endpoints absent."
