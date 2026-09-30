import Mettapedia.GraphTheory.FourColor.PaddedCycleCapContext
import Lean.Util.CollectAxioms

/-! Audit the unbounded cap colouring law and its actual exterior and GSLT
consumers. The nonconstant boundary guard is retained. This audit does not
claim the geometric replacement or the missing monochromatic escape. -/

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
    (``PaddedCycleCap.closed_vertex_loss, [])]
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
  logInfo m!"Guarded padded-cap reconstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
