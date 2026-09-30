import MettapediaFourColor.PentagonalCoronaMinimalReduction
import Lean.Util.CollectAxioms

/-! Audit of chord exclusion and the face-derived reduction with weakened inputs. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PentagonalCoronaGeometry.crossing_origin,
      [``PentagonalCoronaGeometry.outerStar_surjective_at,
        ``PentagonalCoronaGeometry.outerStar_next_snd,
        ``PentagonalCoronaGeometry.outerStar_prev_snd,
        ``PentagonalCoronaGeometry.outerStar_inward_snd,
        ``CubicCycleIncidence.Frame.adjacent_iff]),
    (``PentagonalCoronaGeometry.crossing_card_le_four_of_chord,
      [``PentagonalCoronaGeometry.chord_spoke,
        ``PentagonalCoronaGeometry.crossing_card_le_of_slots,
        ``PentagonalCoronaGeometry.crossingIndex_injective]),
    (``PentagonalCoronaGeometry.card_tracedSide, []),
    (``PentagonalCoronaGeometry.tracedSide_hasCycle,
      [``PentagonalCoronaGeometry.innerFrame,
        ``MatchingBoundaryConnectivity.hasCycle_of_injective_boundary]),
    (``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two,
      [``GoertzelV24MinimalTriangleFree.natCard_edgeSet_add_one_le_of_isAcyclic,
        ``GoertzelV24MinimalTriangleFree.card_crossingEdgeFinset_add_twice_internal_eq_three_mul]),
    (``CyclicFiveBoundary.five_le_crossing_card,
      [``CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two,
        ``GoertzelV24CubicSmallBoundaryCycle.card_crossingEdgeFinset_eq_card_crossingSideDart]),
    (``PentagonalCoronaGeometry.outerInduced_of_cyclicallyFive,
      [``CyclicFiveBoundary.five_le_crossing_card,
        ``PentagonalCoronaGeometry.crossing_card_le_four_of_chord,
        ``PentagonalCoronaGeometry.tracedSide_hasCycle,
        ``PentagonalCoronaGeometry.card_tracedSide]),
    (``PentagonalCoronaGeometry.outerInduced_of_minimality,
      [``PentagonalCoronaGeometry.outerInduced_of_cyclicallyFive,
        ``GoertzelV24FourEdgeCutGluing.cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample,
        ``SphericalVertexLowerBound.twenty_le_card_vertices,
        ``GoertzelV24MinimalFaceSize.orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample]),
    (``PentagonalLobePatch.Tangle.Corona.strict_reduction_of_cyclicallyFive,
      [``PentagonalCoronaGeometry.outerInduced_of_cyclicallyFive,
        ``PentagonalLobePatch.Tangle.Corona.strict_reduction,
        ``PentagonalLobePatch.Tangle.Embedded.size_decrease,
        ``PentagonalLobePatch.Tangle.open_reconstruct_from_tree]),
    (``PentagonalLobePatch.Tangle.Corona.not_in_minimal_counterexample_of_distinct_vertices,
      [``PentagonalCoronaGeometry.outerInduced_of_minimality,
        ``PentagonalLobePatch.Tangle.Corona.not_in_minimal_counterexample,
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
  logInfo m!"Pentagonal corona chord exclusion and reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
