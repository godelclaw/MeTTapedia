import MettapediaFourColor.PentagonalCoronaFaceReduction
import Lean.Util.CollectAxioms

/-! Audit of exact dart separation and the reduction from actual face lengths. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PartialCubicDartSeparation.Diagram.pathCheck_sound, []),
    (``PartialCubicDartSeparation.Realization.separates_sound,
      [``PartialCubicDartSeparation.Realization.apart_sound,
        ``PartialCubicDartSeparation.Diagram.pathCheck_sound,
        ``PartialCubicDartSeparation.Realization.ne_of_path_two,
        ``PartialCubicDartSeparation.Realization.ne_of_path_three,
        ``PartialCubicDartSeparation.Realization.neighbor_unique]),
    (``PartialCubicDartSeparation.Realization.vertex_injective,
      [``PartialCubicDartSeparation.Realization.separates_sound]),
    (``PentagonalCoronaSeparation.separates_all,
      [``PartialCubicDartSeparation.Diagram.separates]),
    (``PentagonalCoronaGeometry.diagramDart_flip,
      [``PentagonalCoronaGeometry.outerStar_edge,
        ``PentagonalCoronaGeometry.center_back_edge]),
    (``PentagonalCoronaGeometry.coronaRealization,
      [``PentagonalCoronaGeometry.diagramDart_rotation,
        ``PentagonalCoronaGeometry.diagramDart_flip,
        ``PentagonalCoronaGeometry.diagramDart_surjective_at,
        ``PentagonalCoronaGeometry.outerStar_injective,
        ``PentagonalCoronaGeometry.innerStar_injective]),
    (``PentagonalCoronaGeometry.tracedVertex_injective_of_triangleFree,
      [``PentagonalCoronaGeometry.coronaRealization,
        ``PentagonalCoronaSeparation.separates_all,
        ``PartialCubicDartSeparation.Realization.vertex_injective]),
    (``PentagonalCoronaGeometry.triangleFree_of_cyclicallyFive_of_four_lt_card,
      [``GoertzelV24MinimalTriangleFree.natCard_complement_triangle_eq_one_of_cyclicallyFive,
        ``GoertzelV24MinimalTriangleFree.fintype_card_eq_four_of_triangle_complement_natCard_eq_one]),
    (``PentagonalCoronaGeometry.tracedVertex_injective_of_cyclicallyFive,
      [``PentagonalCoronaGeometry.tracedVertex_injective_of_triangleFree,
        ``PentagonalCoronaGeometry.triangleFree_of_cyclicallyFive_of_four_lt_card]),
    (``PentagonalCoronaGeometry.tracedVertex_injective_of_minimality,
      [``PentagonalCoronaGeometry.tracedVertex_injective_of_triangleFree,
        ``GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample]),
    (``PentagonalLobePatch.Tangle.Corona.strict_reduction_of_face_pattern,
      [``PentagonalCoronaGeometry.tracedVertex_injective_of_cyclicallyFive,
        ``PentagonalCoronaGeometry.outerInduced_of_cyclicallyFive,
        ``PentagonalLobePatch.Tangle.Corona.strict_reduction_of_cyclicallyFive,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Corona.not_in_minimal_counterexample_of_face_pattern,
      [``PentagonalCoronaGeometry.tracedVertex_injective_of_minimality,
        ``PentagonalCoronaGeometry.outerInduced_of_minimality,
        ``PentagonalLobePatch.Tangle.Corona.not_in_minimal_counterexample_of_distinct_vertices,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
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
  logInfo m!"Pentagonal corona noncollision and face-pattern reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
