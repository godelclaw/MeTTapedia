import MettapediaFourColor.PentagonalLobeTreeReduction
import Lean.Util.CollectAxioms

/-! Dependency audit of geometric tree replacement and colouring reconstruction. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OpenTangleConnectedReplacement.replacement_structural,
      [``OpenTangleConnectedReplacement.essential_left,
        ``OpenTangleConnectedReplacement.stays_left,
        ``GoertzelV24BoundaryEssentialGluing.glue_bridgeless,
        ``OpenTangleSmallCutReplacement.composite_structural_iff]),
    (``OpenTangleCompositionSwap.mapClass,
      [``RotationSystemExactTransport.mapClass,
        ``OpenTangleCompositionSwap.alpha, ``OpenTangleCompositionSwap.vertex,
        ``OpenTangleCompositionSwap.rotation]),
    (``PentagonalLobePatch.Tangle.Tree.connected,
      [``PentagonalLobePatch.Tangle.Tree.piece,
        ``GoertzelV24CompositeSeamMultigraph.sideMultigraph_ends]),
    (``PentagonalLobePatch.Tangle.piece_returnCode,
      [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``PentagonalLobePatch.Tangle.tree_returnCode,
      [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``PentagonalLobePatch.Tangle.tree_replacement_euler,
      [``OpenTanglePortReplacement.euler_eq_iff_mass,
        ``PentagonalLobePatch.Tangle.piece_eulerMass,
        ``PentagonalLobePatch.Tangle.tree_eulerMass]),
    (``PentagonalLobePatch.Tangle.tree_replacement_face_count,
      [``OpenTanglePortReplacement.face_count_replacement,
        ``PentagonalLobePatch.Tangle.piece_face_count,
        ``PentagonalLobePatch.Tangle.tree_face_count]),
    (``PentagonalLobePatch.Tangle.tree_replacement_exterior_faces,
      [``OpenTanglePortReplacement.exterior_sameCycle_iff]),
    (``PentagonalLobePatch.Tangle.sewn_tree_class,
      [``PentagonalLobePatch.Tangle.tree_replacement_class,
        ``OpenTangleConnectedReplacement.replacement_structural,
        ``OpenTangleConnectedReplacement.essential_of_surjective,
        ``PentagonalLobePatch.Tangle.Tree.connected,
        ``PentagonalLobePatch.Tangle.Tree.cubic,
        ``PentagonalLobePatch.Tangle.Tree.cyclic,
        ``PentagonalLobePatch.Tangle.tree_replacement_euler,
        ``OpenTangleCompositionSwap.mapClass]),
    (``PentagonalLobePatch.Tangle.reconstruct_from_tree,
      [``OpenTangleClosedWitness.restrict,
        ``PentagonalLobePatch.Tangle.sewn_colorable_of_physical_noncrossing,
        ``OpenTangleClosedWitness.glue]),
    (``PentagonalLobePatch.Tangle.strict_tree_reduction,
      [``PentagonalLobePatch.Tangle.sewn_tree_class,
        ``PentagonalLobePatch.Tangle.reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.colorable_of_smallerColorable,
      [``PentagonalLobePatch.Tangle.strict_tree_reduction])]
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
  logInfo m!"Pentagonal lobe tree reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
