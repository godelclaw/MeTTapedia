import Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder
import Lean.Util.CollectAxioms

/-! Dependency audit of actual lobe boundary walks and their induced spoke order. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CycleSpokeConnectivity.connected_complement_of_boundary_reachable, []),
    (``CycleSpokeConnectivity.exterior_connected_of_spokes_in_connected_side,
      [``CycleSpokeConnectivity.connected_complement_of_boundary_reachable,
        ``CubicCycleIncidence.Frame.adjacent_iff]),
    (``CycleSpokeConnectivity.uniform_geometry_of_spokes_in_connected_side,
      [``CycleSpokeConnectivity.exterior_connected_of_spokes_in_connected_side,
        ``CubicCycleIncidence.Frame.uniform_geometry]),
    (``ElevenLobeSpokeOrder.eq_shift_or_reflection_of_step, []),
    (``ElevenLobeSpokeOrder.Incidence.exterior_connected,
      [``CycleSpokeConnectivity.exterior_connected_of_spokes_in_connected_side,
        ``CubicCycleIncidence.Frame.connected]),
    (``ElevenLobeSpokeOrder.Incidence.boundary_return,
      [``ElevenLobeSpokeOrder.Incidence.face_port,
        ``ElevenLobeSpokeOrder.Incidence.face_prev,
        ``ElevenLobeSpokeOrder.Incidence.outer_spoke,
        ``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``ElevenLobeSpokeOrder.Incidence.inner_geometry,
      [``ElevenLobeSpokeOrder.Incidence.exterior_connected,
        ``ElevenLobeSpokeOrder.Incidence.boundary_return,
        ``ElevenLobeSpokeOrder.Incidence.complement_port,
        ``CubicCycleIncidence.Frame.uniform_geometry,
        ``GoertzelV24ComplementaryShoreBoundaryOrder.boundarySuccessors_opposite_of_planarBond]),
    (``ElevenLobeSpokeOrder.Incidence.inner_geometry_affine,
      [``ElevenLobeSpokeOrder.Incidence.inner_geometry,
        ``ElevenLobeSpokeOrder.eq_shift_or_reflection_of_step])]
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
  logInfo m!"Eleven-lobe spoke order: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
