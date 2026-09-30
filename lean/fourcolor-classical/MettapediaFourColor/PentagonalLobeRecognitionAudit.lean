import MettapediaFourColor.PentagonalLobeRecognition
import Lean.Util.CollectAxioms

/-! Dependency audit of exact geometric recognition and its strict reduction consumer. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ElevenLobeSpokeOrder.Incidence.innerBySpoke_rotation,
      [``ElevenLobeSpokeOrder.Incidence.innerBySpoke_star,
        ``ElevenLobeSpokeOrder.Incidence.matching_symm_next]),
    (``ElevenLobeSpokeOrder.Incidence.outward_spoke_not_inner,
      [``CubicCycleIncidence.Frame.adjacent_iff]),
    (``ElevenLobeSpokeOrder.Incidence.patchDartEquiv,
      [``CubicCycleIncidence.Frame.star_surjective_at,
        ``ElevenLobeSpokeOrder.Incidence.coordinateDart_injective]),
    (``ElevenLobeSpokeOrder.Incidence.coordinateDart_boundary,
      [``ElevenLobeSpokeOrder.Incidence.outward_spoke_not_inner,
        ``ElevenLobeSpokeOrder.Incidence.outer_spoke]),
    (``ElevenLobeSpokeOrder.Incidence.coordinateDart_flip,
      [``ElevenLobeSpokeOrder.Incidence.outer_spoke]),
    (``OpenTangleIsomorphism.ofRetainedDarts,
      [``OpenTangleIsomorphism.internalCoordinate,
        ``OpenTangleIsomorphism.boundaryCoordinate,
        ``OpenTangleIsomorphism.sumCoordinate]),
    (``PentagonalLobePatch.Tangle.Coordinates.alpha, []),
    (``PentagonalLobePatch.Tangle.Coordinates.rotation, []),
    (``PentagonalLobePatch.Tangle.Recognition.withOrientation,
      [``OpenTangleIsomorphism.ofRetainedDarts,
        ``ElevenLobeSpokeOrder.Incidence.patchDartEquiv,
        ``ElevenLobeSpokeOrder.Incidence.coordinateDart_boundary,
        ``ElevenLobeSpokeOrder.Incidence.coordinateDart_flip,
        ``ElevenLobeSpokeOrder.Incidence.coordinateDart_turn,
        ``PentagonalLobePatch.Tangle.Coordinates.alpha,
        ``PentagonalLobePatch.Tangle.Coordinates.rotation]),
    (``PentagonalLobePatch.Tangle.Recognition.recognized,
      [``ElevenLobeSpokeOrder.Incidence.inner_geometry,
        ``PentagonalLobePatch.Tangle.Recognition.withOrientation]),
    (``PentagonalLobePatch.Tangle.Recognition.strict_reduction_of_geometry,
      [``PentagonalLobePatch.Tangle.Recognition.recognized,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction_of_minimum_face_size,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Recognition.not_in_minimal_counterexample,
      [``PentagonalLobePatch.Tangle.Recognition.recognized,
        ``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimality,
        ``PentagonalLobePatch.Tangle.Embedded.strict_reduction,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree])]
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
  logInfo m!"Pentagonal lobe geometric recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
