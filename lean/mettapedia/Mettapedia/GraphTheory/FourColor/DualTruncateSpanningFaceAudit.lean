import Mettapedia.GraphTheory.FourColor.AdjacentSourceSpanningFaceReduction
import Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample
import Lean.Util.CollectAxioms

/-! Audit exact edge integration, spanning-face calibration, cross-edge
preservation and strict/GSLT splice reconstruction. Finite geometry is
audited separately and is absent from the general proof dependency closure. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RotationClosedEdgePotential.edgeSum_eq_zero_of_faces,
      [``GoertzelV24RotationCycleSpace.range_faceBoundaryLinearMap_eq_cycleSpace]),
    (``RotationClosedEdgePotential.potential_difference_of_cycle_vanishing,
      [``GoertzelV24RotationWalkCycleParity.incidenceMatrix_mulVec_single_edge]),
    (``RotationClosedEdgePotential.potential_difference,
      [``RotationClosedEdgePotential.edgeSum_eq_zero_of_faces]),
    (``DualTruncateSpanningFace.sum_crossField_face_eq_zero,
      [``DualTruncateCornerSemantics.cross_of_star]),
    (``DualTruncateSpanningFace.cross_potential_difference,
      [``RotationClosedEdgePotential.potential_difference]),
    (``DualTruncateSpanningFace.phase_phi,
      [``DualTruncateSpanningFace.cross_potential_difference]),
    (``DualTruncateSpanningFace.phase_sameCycle, [``DualTruncateSpanningFace.phase_phi]),
    (``DualTruncateSpanningFace.sourceValues_eq_corner,
      [``DualTruncateSpanningFace.phase_sameCycle]),
    (``DualTruncateSpanningFace.sourceValues_nonzero,
      [``DualTruncateSpanningFace.sourceValues_eq_corner]),
    (``DualTruncateSpanningFace.sourceValues_difference,
      [``DualTruncateSpanningFace.cross_potential_difference]),
    (``DualTruncateSpanningFace.sourceColouring,
      [``DualTruncateSpanningFace.sourceValues_nonzero,
       ``DualTruncateSpanningFace.sourceValues_difference]),
    (``DualTruncateSpanningFace.preserves_cross,
      [``DualTruncateSpanningFace.sourceValues_difference]),
    (``AdjacentSourceSpanningFaceReduction.sourceWitness,
      [``DualTruncateSpanningFace.sourceColouring, ``AdjacentSourceSplice.smaller_spherical]),
    (``AdjacentSourceSpanningFaceReduction.smaller_cross_preserved,
      [``DualTruncateSpanningFace.preserves_cross]),
    (``AdjacentSourceSpanningFaceReduction.restoredSource,
      [``DualTruncateSpanningFace.sourceColouring, ``AdjacentSourceSplice.exists_repair]),
    (``AdjacentSourceSpanningFaceReduction.strict_reconstruction,
      [``DualTruncateSpanningFace.sourceColouring, ``AdjacentSourceSplice.reduction_reconstruction]),
    (``AdjacentSourceSpanningFaceReduction.every_complete_sweep,
      [``DualTruncateSpanningFace.sourceColouring, ``AdjacentSourceSplice.every_complete_sweep]),
    (``DualTruncateSpanningFaceExample.twoSided, []),
    (``DualTruncateSpanningFaceExample.face, []),
    (``DualTruncateSpanningFaceExample.all_cross_preserved,
      [``DualTruncateSpanningFace.preserves_cross]),
    (``DualTruncateSpanningFaceExample.nonvacuous_input,
      [``DualTruncateSpanningFaceExample.all_cross_preserved])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.ProperWord,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_connected_pair,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairBoundary.AdjacentPairData.exists_cyclicallyOrdered_deletedColoring_join01_23_compatible,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization.GraphBackedVertexMinimalTaitCounterexample]
  let fixtures : List Name := [
    `Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24ThetaPresentationCounterexample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample,
    `Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples,
    `Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair]
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
      if !(`Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFaceExample).isPrefixOf root &&
          fixtures.any (·.isPrefixOf name) then
        throwError m!"Finite fixture in general root {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Spanning-face calibration: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    exact literal-edge integration, arbitrary target witness extraction, joint cross-edge \
    preservation, strict splice and GSLT reconstruction present; complete theorem, \
    supplied source colour words and Brooks suppliers absent; finite geometry checked separately."
