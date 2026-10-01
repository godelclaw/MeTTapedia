import Mettapedia.GraphTheory.FourColor.CappedLadderFamilyGSLT
import Lean.Util.CollectAxioms

/-! Audit the literal face classification, exact retained-dart sewing,
arbitrary-input physical repair, strict reconstruction, and terminating
family routes. The two-vertex base is used only by the complete family
construction; structural and arbitrary-input laws are independent of it. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CappedLadderRotation.flip_involutive, []),
    (``CappedLadderRotation.cubic, []),
    (``CappedLadderRotation.rotationCyclic, []),
    (``CappedLadderRotation.spanningFace, [``CappedLadderRotation.outer_sameCycle]),
    (``CappedLadderRotation.connected, []),
    (``CappedLadderRotation.face_sameCycle_iff, [``CappedLadderRotation.faceRoot_sameCycle]),
    (``CappedLadderRotation.face_count,
      [``Mettapedia.GraphTheory.OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant]),
    (``CappedLadderRotation.edge_count, [``RotationSystem.card_darts_eq_twice_card_edges]),
    (``CappedLadderRotation.spherical, [``CappedLadderRotation.face_count, ``CappedLadderRotation.edge_count]),
    (``CappedLadderRotation.twoSided, [``CappedLadderRotation.face_sameCycle_iff, ``CappedLadderRotation.folded_succ_ne]),
    (``CappedLadderEndReduction.project_embed, []),
    (``CappedLadderEndReduction.project_rev, []),
    (``CappedLadderEndReduction.sewnFlip_embed, [``CappedLadderEndReduction.embed_rev]),
    (``CappedLadderEndReduction.embed_project, []),
    (``CappedLadderEndReduction.sewnFlip_retains_intact, []),
    (``CappedLadderEndReduction.retainedDartEquiv,
      [``CappedLadderEndReduction.project_embed, ``CappedLadderEndReduction.embed_project]),
    (``CappedLadderEndReduction.sewnAlpha_val, [``CappedLadderEndReduction.sewnFlip_embed]),
    (``CappedLadderEndReduction.sewnAlpha_involutive, []),
    (``CappedLadderEndReduction.sewnAlpha_fixfree, []),
    (``CappedLadderEndReduction.retained_rho, []),
    (``CappedLadderEndReduction.restored, [``CappedLadderEndReduction.project_next_vertex]),
    (``CappedLadderEndReduction.restored_retained, [``CappedLadderEndReduction.project_embed]),
    (``CappedLadderEndReduction.restored_stars, [``CappedLadderEndReduction.project_alpha_embed]),
    (``CappedLadderEndReduction.target_strict_decrease, [``CappedLadderEndReduction.target_vertices_removed]),
    (``CappedLadderEndReduction.target_geometry,
      [``CappedLadderRotation.spherical, ``CappedLadderRotation.connected, ``DualTruncateMapGeometry.mapClass_of]),
    (``CappedLadderEndReduction.strict_operation,
      [``CappedLadderEndReduction.sewnAlpha_val, ``CappedLadderEndReduction.sewnFlip_retains_intact]),
    (``CappedLadderEndReduction.calibrated,
      [``DualTruncateSpanningFace.sourceColouring, ``CappedLadderRotation.spanningFace, ``CappedLadderRotation.twoSided]),
    (``CappedLadderEndReduction.initial, [``DualTruncateSpanningFace.sourceValues_difference]),
    (``CappedLadderEndReduction.history, [``DualTruncateFacePhaseGSLT.repair]),
    (``CappedLadderEndReduction.history_physical, [``DualTruncateFacePhaseGSLT.physical_history]),
    (``CappedLadderEndReduction.cross_preserved, [``DualTruncateFacePhaseKempe.normalize_cross_preserved]),
    (``CappedLadderEndReduction.terminalSource,
      [``DualTruncateCornerCoherence.sourceColouring, ``DualTruncateFacePhaseKempe.normalize_error]),
    (``CappedLadderEndReduction.terminal_is_source_image,
      [``CappedLadderEndReduction.terminal_values, ``CappedLadderEndReduction.terminal_exact]),
    (``CappedLadderEndReduction.restored_terminal_stars,
      [``CappedLadderEndReduction.restored_stars, ``CappedLadderEndReduction.terminal_is_source_image]),
    (``CappedLadderEndReduction.operational_reconstruction,
      [``CappedLadderEndReduction.strict_operation, ``CappedLadderEndReduction.terminalSource,
       ``CappedLadderEndReduction.history_physical]),
    (``CappedLadderEndReduction.every_complete_sweep,
      [``CappedLadderEndReduction.terminalSource, ``DualTruncateConstructionGSLT.supported_encoded_route]),
    (``CappedLadderFamilyGSLT.baseWitness, []),
    (``CappedLadderFamilyGSLT.presentation, []),
    (``CappedLadderFamilyGSLT.event_operation, [``CappedLadderEndReduction.strict_operation]),
    (``CappedLadderFamilyGSLT.grow_retained, [``CappedLadderEndReduction.restored_retained]),
    (``CappedLadderFamilyGSLT.construction_length, [``CappedLadderFamilyGSLT.advance_length]),
    (``CappedLadderFamilyGSLT.witness,
      [``CappedLadderFamilyGSLT.baseWitness, ``CappedLadderEndReduction.restored]),
    (``CappedLadderFamilyGSLT.target_tait, [``CappedLadderFamilyGSLT.witness]),
    (``CappedLadderFamilyGSLT.reduction_length, [``CappedLadderFamilyGSLT.reverse_length]),
    (``CappedLadderFamilyGSLT.reduction_wellFounded, [``CappedLadderFamilyGSLT.reduction_rank]),
    (``CappedLadderFamilyGSLT.unbounded_vertices, [``CappedLadderFamilyGSLT.expanded_vertex_count]),
    (``CappedLadderFamilyGSLT.every_complete_sweep,
      [``CappedLadderFamilyGSLT.witness, ``DualTruncateConstructionGSLT.supported_encoded_route])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.ProperWord,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_connected_pair,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization.GraphBackedVertexMinimalTaitCounterexample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24ThetaPresentationCounterexample]
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
        throwError m!"Forbidden dependency in {root}: {name}"
    if !(`Mettapedia.GraphTheory.FourColor.CappedLadderFamilyGSLT).isPrefixOf root &&
        seen.contains ``CappedLadderFamilyGSLT.baseWitness then
      throwError m!"Family base entered structural or arbitrary-input root {root}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Literal capped-ladder family: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    all-width face recognition, parallel-edge sewing, physical arbitrary-input repair, \
    six-vertex reduction and terminating compatible construction checked; complete \
    colouring endpoints and unrelated finite fixtures absent."
