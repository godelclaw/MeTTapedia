import MettapediaFourColor.PentagonalCoronaReduction
import Lean.Util.CollectAxioms

/-! Audit of the face-traversal construction and its strict reduction consumer. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FacialCoronaTraversal.outside_arc,
      [``FacialCoronaTraversal.incoming_face, ``FacialCoronaTraversal.first_eq]),
    (``PentagonalCoronaGeometry.period_of_face_length,
      [``GoertzelV24OrbitFaceCyclicOrder.phi_isCycleOn_faceOrbit]),
    (``PentagonalCoronaGeometry.outerStar_edge,
      [``FacialCoronaTraversal.pentagonal_last, ``FacialCoronaTraversal.hexagonal_last,
        ``PentagonalCoronaGeometry.center_step]),
    (``PentagonalCoronaGeometry.outerStar_spoke_outside,
      [``PentagonalCoronaGeometry.outerStar_injective,
        ``PentagonalCoronaGeometry.outerStar_next_snd,
        ``PentagonalCoronaGeometry.outerStar_prev_snd]),
    (``PentagonalCoronaGeometry.incidence,
      [``PentagonalCoronaGeometry.outerFrame, ``PentagonalCoronaGeometry.innerFrame,
        ``PentagonalCoronaGeometry.spoke_at_inward]),
    (``PentagonalCoronaGeometry.incidence_rotation,
      [``PentagonalCoronaGeometry.outerFrame_star, ``PentagonalCoronaGeometry.outerStar_rotation]),
    (``PentagonalLobePatch.Tangle.Corona.strict_reduction,
      [``PentagonalCoronaGeometry.FaceLengths.central_period,
        ``PentagonalCoronaGeometry.FaceLengths.neighbour_periods,
        ``PentagonalCoronaGeometry.incidence_rotation,
        ``PentagonalLobePatch.Tangle.Recognition.strict_reduction_of_geometry,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Corona.not_in_minimal_counterexample,
      [``PentagonalCoronaGeometry.incidence,
        ``PentagonalCoronaGeometry.incidence_rotation,
        ``PentagonalLobePatch.Tangle.Recognition.not_in_minimal_counterexample,
        ``PentagonalLobePatch.Tangle.Embedded.exterior_connected_of_minimality,
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
  logInfo m!"Pentagonal corona face reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
