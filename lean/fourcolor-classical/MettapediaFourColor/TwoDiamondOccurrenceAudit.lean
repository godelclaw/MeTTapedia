import MettapediaFourColor.TwoDiamondOccurrenceReduction
import Lean.Util.CollectAxioms

/-! Exact occurrence transport and its strict-reduction consumer. Generic
source transport and geometry exclude all configuration certificates;
reconstruction retains only configuration 6, without a complete colouring
endpoint. Required dependencies ensure the actual source bridge is used. -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OpenTangleVertexOccurrence.darts_alpha, []),
    (``OpenTangleVertexOccurrence.darts_vertex,
      [``OpenTangleIsomorphism.Iso.sewn_vert]),
    (``OpenTangleVertexOccurrence.darts_rotation,
      [``OpenTangleIsomorphism.Iso.sewn_rotation, ``VertexSideExactReassembly.rotation]),
    (``OpenTangleVertexOccurrence.assembled_class,
      [``RotationSystemExactTransport.mapClass,
       ``OpenTangleVertexOccurrence.darts_alpha,
       ``OpenTangleVertexOccurrence.darts_vertex,
       ``OpenTangleVertexOccurrence.darts_rotation]),
    (``OpenTangleVertexOccurrence.reassemble_colouring,
      [``GoertzelV24VertexSideReassembly.exists_taitColoring_of_dartEquiv]),
    (``OpenTangleVertexOccurrence.colorable_iff,
      [``GoertzelV24VertexSideReassembly.rotationSystemTaitColorable_iff_of_dartEquiv]),
    (``OpenTangleVertexOccurrence.vertex_count,
      [``OpenTangleVertexOccurrence.vertices]),
    (``TwoDiamondOccurrenceReduction.vertex_loss,
      [``OpenTangleVertexOccurrence.vertex_count,
       ``TwoDiamondCycleReplacement.whole_vertex_loss]),
    (``TwoDiamondOccurrenceReduction.smaller_class,
      [``OpenTangleVertexOccurrence.assembled_class,
       ``TwoDiamondCycleReplacement.replacement_class]),
    (``TwoDiamondOccurrenceReduction.reconstruct,
      [``OpenTangleVertexOccurrence.colorable_iff,
       ``TwoDiamondHubColoring.reconstruct, ``Bulk.Cfg005.hgood]),
    (``TwoDiamondOccurrenceReduction.strict_reduction_of_occurrence,
      [``TwoDiamondOccurrenceReduction.vertex_loss,
       ``TwoDiamondOccurrenceReduction.smaller_class,
       ``TwoDiamondOccurrenceReduction.reconstruct]),
    (``TwoDiamondOccurrenceReduction.not_in_minimal_counterexample_of_occurrence,
      [``TwoDiamondOccurrenceReduction.strict_reduction_of_occurrence,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable])]
  let repairRoots : List Name := [``TwoDiamondOccurrenceReduction.reconstruct,
    ``TwoDiamondOccurrenceReduction.strict_reduction_of_occurrence,
    ``TwoDiamondOccurrenceReduction.not_in_minimal_counterexample_of_occurrence]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all, `FourColor.reducible_block_0]
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
        throwError m!"Complete colouring endpoint in {root}: {name}"
      if (!repairRoots.contains root && (`FourColor.Bulk).isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" &&
            !(`FourColor.Bulk.Cfg005).isPrefixOf name) then
        throwError m!"Unexpected colour certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Shared-tip occurrence audit: {roots.length} roots; \
    {inspected.toList.length} declarations; actual source reconstruction and strict reduction; only the retained configuration-6 base allowed."
