import Mettapedia.GraphTheory.FourColor.PaddedCycleCapPhysicalGeometry
import Lean.Util.CollectAxioms

/-! Audit the adjacent physical repair, the all-width cap reduction on its
physical noncrossing domain, the recognized connected-exterior geometric
consumer and the actual joint GSLT witness maps. Universal cap recognition,
disconnected odd-width exteriors and catalogue coverage are not claimed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``Compositional.CyclicBoundaryMatching.exists_adjacent, []),
    (``CycleAdjacentBoundaryRepair.accepts_adjacent, [``CycleCap.accepts_spokes]),
    (``CycleAdjacentBoundaryRepair.word_nonconstant, []),
    (``Compositional.ConstantBoundaryKempeRepair.repair,
      [``Compositional.CyclicBoundaryMatching.exists_adjacent,
       ``Compositional.BoundaryKempeSwitch.switchBoundaryWord_mem_supportInCoordinates]),
    (``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing,
      [``Compositional.ConstantBoundaryKempeRepair.repair,
       ``CycleAdjacentBoundaryRepair.accepts_adjacent, ``CycleAdjacentBoundaryRepair.word_nonconstant,
       ``PaddedCycleCap.reconstruct_indexed, ``OpenTangleClosedWitness.restrict,
       ``OpenTangleClosedWitness.glue]),
    (``PaddedCycleCap.strict_reduction_of_physical_noncrossing,
      [``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing,
       ``PaddedCycleCap.replacement_class, ``PaddedCycleCap.closed_vertex_loss]),
    (``PaddedCycleCap.physicalClosedCell,
      [``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing]),
    (``PaddedCycleCap.physicalClosedInContext_outer,
      [``PaddedCycleCap.physicalClosedCell, ``Mettapedia.GSLT.LooseRelationEquipment.Cell.hcomp]),
    (``PaddedCycleCap.recognized_cap_connected, [``OpenTangleIsomorphism.Iso.connected]),
    (``PaddedCycleCap.recognized_cap_exterior_order,
      [``OpenTangleIsomorphism.Iso.returnCode,
       ``GoertzelV24ComplementaryShoreBoundaryOrder.boundarySuccessors_opposite_of_planarBond,
       ``PaddedCycleCap.indexed_returnCode]),
    (``PaddedCycleCap.physical_noncrossing_recognized_cap,
      [``PaddedCycleCap.recognized_cap_exterior_order,
       ``Compositional.CyclicBoundaryMatching.physicalMateInCoordinates_isNoncrossing]),
    (``PaddedCycleCap.recognized_cap_reconstruct,
      [``PaddedCycleCap.closed_reconstruct_of_physical_noncrossing,
       ``PaddedCycleCap.physical_noncrossing_recognized_cap,
       ``GoertzelV24VertexSideReassembly.rotationSystemTaitColorable_complementaryComposite_iff]),
    (``PaddedCycleCap.recognized_cap_strict_reduction,
      [``PaddedCycleCap.strict_reduction_of_physical_noncrossing,
       ``PaddedCycleCap.recognized_cap_reconstruct, ``OpenTangleIsomorphism.Iso.sewn_class]),
    (``PaddedCycleCap.no_recognized_cap,
      [``PaddedCycleCap.recognized_cap_strict_reduction,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
  let forbidden : List Name := [
    `FourColor, `Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.five_tube_normalize,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.tube_support_eq,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.transfer_adjacent_of_stabilizes,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.full_transfer_after_word_bound]
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
  logInfo m!"Padded-cap physical repair and recognized all-width reduction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
