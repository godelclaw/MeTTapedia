import Mettapedia.GraphTheory.FourColor.PrismRungReduction
import Lean.Util.CollectAxioms

/-! Audit original prism geometry, the exact canonical retained-dart splice,
transported spanning-face domain, physical arbitrary-input repair and actual
strict reconstruction. No finite family colouring base is consumed. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PrismRungCoordinates.dartEquiv, [``PrismRungCoordinates.graphDart_injective, ``PrismRungCoordinates.graphDart_surjective]),
    (``PrismRungCoordinates.dartEquiv_alpha, []),
    (``PrismRungCoordinates.graph_rotation, []),
    (``PrismRungCoordinates.ordered_pair, [``PrismRungCoordinates.rotation_ports]),
    (``PrismRungSplice.vertexEquiv, []),
    (``PrismRungSplice.spliceDartEquiv, [``PrismRungSplice.retainedEquiv]),
    (``PrismRungSplice.underlying_equiv, []),
    (``PrismRungSplice.vertex_commute, []),
    (``PrismRungSplice.rho_commute, [``PrismRungSplice.underlying_injective]),
    (``PrismRungSplice.sewnFlip_embed, [``CappedLadderEndReduction.sewnFlip_embed]),
    (``PrismRungSplice.exposed_unique, []),
    (``PrismRungSplice.left_underlying, [``PrismRungSplice.exposed_unique]),
    (``PrismRungSplice.right_underlying, [``PrismRungSplice.exposed_unique]),
    (``PrismRungSplice.sewnFlip_retains_intact, [``PrismRungSplice.exposed_removed]),
    (``PrismRungSplice.underlying_alpha, [``PrismRungSplice.sewnFlip_retains_intact, ``PrismRungSplice.left_underlying, ``PrismRungSplice.right_underlying]),
    (``PrismRungSplice.alpha_commute, [``PrismRungSplice.underlying_alpha, ``PrismRungSplice.sewnFlip_embed]),
    (``PrismRungSplice.spanningFace, [``PrismRungSplice.alpha_commute, ``PrismRungSplice.rho_commute, ``CappedLadderRotation.spanningFace, ``RotationSystemExactTransport.sameFace_iff]),
    (``PrismRungSplice.twoSided, [``CappedLadderRotation.twoSided, ``PrismRungSplice.alpha_commute]),
    (``PrismRungSplice.spherical, [``CappedLadderRotation.spherical, ``RotationSystemExactTransport.spherical]),
    (``PrismRungSplice.connected, [``PrismRungSplice.alpha_commute]),
    (``PrismRungSplice.retained_connected, [``PrismRungSplice.sewn_original_adjacent]),
    (``PrismRungGeometry.face_sameCycle_iff, [``PrismRungGeometry.faceRoot_sameCycle]),
    (``PrismRungGeometry.face_count, [``PrismRungGeometry.face_sameCycle_iff]),
    (``PrismRungGeometry.spherical, [``PrismRungGeometry.face_count, ``PrismRungGeometry.edge_count]),
    (``PrismRungGeometry.twoSided, [``PrismRungGeometry.quad_rev_ne, ``PrismRungGeometry.face_sameCycle_iff]),
    (``PrismRungGeometry.connected, []),
    (``PrismRungGeometry.graph_spherical, [``PrismRungGeometry.spherical, ``RotationSystemExactTransport.spherical]),
    (``PrismRungGeometry.graph_twoSided, [``PrismRungGeometry.twoSided, ``RotationSystemExactTransport.twoSided]),
    (``PrismRungReduction.target_counts, [``PrismRungSplice.spliceDartEquiv]),
    (``PrismRungReduction.witness, [``PrismRungSplice.spanningFace, ``PrismRungGeometry.graph_spherical, ``PrismRungSplice.retained_connected]),
    (``PrismRungReduction.history, [``DualTruncateFacePhaseGSLT.repair]),
    (``PrismRungReduction.restoredSource, [``AdjacentSourceSplice.sourceColouring, ``AdjacentSourceFacePhaseReduction.repairedSource]),
    (``PrismRungReduction.operational_reconstruction, [``AdjacentSourceFacePhaseReduction.operational_reconstruction, ``PrismRungSplice.spanningFace, ``PrismRungGeometry.graph_spherical]),
    (``PrismRungReduction.every_complete_sweep, [``AdjacentSourceFacePhaseReduction.every_complete_sweep])]
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
    if seen.contains `Mettapedia.GraphTheory.FourColor.CappedLadderFamilyGSLT.baseWitness then
      throwError m!"Finite family base entered arbitrary-input prism root {root}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Prism rung family: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    original geometry, exact parallel-edge recognition, arbitrary-input physical repair, \
    strict reconstruction and complete GSLT sweeps checked; complete colouring \
    endpoints, finite colour bases and unrelated fixtures absent."
