import Mettapedia.GraphTheory.FourColor.PaddedCycleCapTransport
import Lean.Util.CollectAxioms

/-! Audit the uniform cap colouring law, geometric replacement, strict even
family reduction, exact representation transport and actual GSLT consumers.
Odd widths retain the nonconstant boundary guard; their general monochromatic
escape and broader geometric coverage are not claimed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CyclicColourAvoidance.exists_cycle, []),
    (``PaddedCycleCap.tangle, [``PaddedCycleCap.position_star, ``PaddedCycleCap.star_position]),
    (``PaddedCycleCap.colouringOf_isTait, [``PaddedCycleCap.colouringOf]),
    (``PaddedCycleCap.accepts_of_nonconstant,
      [``CyclicColourAvoidance.exists_cycle, ``PaddedCycleCap.colouringOf_isTait]),
    (``PaddedCycleCap.cycleWitness_of_edges, [``PaddedCycleCap.portIndex]),
    (``PaddedCycleCap.reconstruct_cycle,
      [``PaddedCycleCap.accepts_of_nonconstant, ``CycleSeamTransfer.edges_valid,
       ``CycleSeamTransfer.spokes_edges]),
    (``PaddedCycleCap.reconstruct_indexed,
      [``PaddedCycleCap.reconstruct_cycle, ``TwoSidedBoundaryReindex.accepts_reindex]),
    (``PaddedCycleCap.reconstructCell,
      [``PaddedCycleCap.reconstruct_indexed, ``PaddedCycleCap.guardedCycle]),
    (``PaddedCycleCap.reconstructInContext_exterior,
      [``PaddedCycleCap.reconstructCell, ``Mettapedia.GSLT.LooseRelationEquipment.Cell.hcomp]),
    (``PaddedCycleCap.reconstruct_closed,
      [``PaddedCycleCap.reconstruct_indexed, ``OpenTangleClosedWitness.restrict,
       ``OpenTangleClosedWitness.glue]),
    (``PaddedCycleCap.closed_vertex_loss, []),
    (``CyclicColourAvoidance.exists_cycle_of_even, [``CyclicColourAvoidance.exists_cycle]),
    (``PaddedCycleCap.face_count, [``PaddedCycleCap.face_sameCycle_iff]),
    (``PaddedCycleCap.encode_cap, [``PaddedCycleCap.boundary_first_return]),
    (``PaddedCycleCap.cap_connected_bridgeless,
      [``PaddedCycleCap.cap_cut_decomposition, ``SmallCutReplacementCore.permutation_small_cut]),
    (``CycleCap.face_count, [``CycleCap.face_sameCycle_iff]),
    (``CycleCap.encode_cap, [``CycleCap.boundary_first_return]),
    (``CycleCap.cap_connected_bridgeless, [``SmallCutReplacementCore.permutation_small_cut]),
    (``PaddedCycleCap.indexed_returnCode,
      [``PaddedCycleCap.encode_cap, ``TwoSidedBoundaryJoint.face_reindex]),
    (``PaddedCycleCap.replacement_class,
      [``OpenTangleInternalReplacement.replacement_structural,
       ``OpenTanglePortReplacement.euler_eq_iff_mass, ``PaddedCycleCap.indexed_returnCode,
       ``PaddedCycleCap.cap_connected_bridgeless, ``CycleCap.cap_connected_bridgeless,
       ``CycleCap.cap_isCubic, ``CycleCap.cap_rotationCyclic]),
    (``PaddedCycleCap.reconstruct_even,
      [``CyclicColourAvoidance.exists_cycle_of_even, ``PaddedCycleCap.colouringOf_isTait]),
    (``PaddedCycleCap.evenInContext_exterior,
      [``PaddedCycleCap.evenCell, ``Mettapedia.GSLT.LooseRelationEquipment.Cell.hcomp]),
    (``PaddedCycleCap.even_closed_reconstruct,
      [``PaddedCycleCap.reconstruct_even, ``OpenTangleClosedWitness.replace]),
    (``PaddedCycleCap.strict_even_reduction,
      [``PaddedCycleCap.replacement_class, ``PaddedCycleCap.even_closed_reconstruct,
       ``PaddedCycleCap.closed_vertex_loss]),
    (``PaddedCycleCap.exact_reduction,
      [``PaddedCycleCap.strict_even_reduction, ``RotationSystemExactTransport.mapClass]),
    (``PaddedCycleCap.no_even_cap,
      [``PaddedCycleCap.exact_reduction,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
  let forbidden : List Name := [
    `FourColor, `Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.five_tube_normalize, `Mettapedia.GraphTheory.FourColor.ZigzagRing.tube_support_eq,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.transfer_adjacent_of_stabilizes, `Mettapedia.GraphTheory.FourColor.ZigzagRing.full_transfer_after_word_bound]
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
        throwError m!"Finite stabilization or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Padded-cap reconstruction and strict even-family reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
