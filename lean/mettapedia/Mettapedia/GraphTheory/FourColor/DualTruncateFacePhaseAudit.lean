import Mettapedia.GraphTheory.FourColor.AdjacentSourceFacePhaseReduction
import Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample
import Lean.Util.CollectAxioms

/-! Audit physical region normalization, actual intermediate Tait witnesses,
authored GSLT histories and their strict splice consumer. The nontrivial
parallel-edge fixture is excluded from every general proof closure. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateFacePhaseKempe.phase_swap, []),
    (``DualTruncateFacePhaseKempe.error_phi, [``DualTruncateCornerSemantics.cross_of_star]),
    (``DualTruncateFacePhaseKempe.mask_at_star, [``DualTruncateFacePhaseKempe.error_phi_symm]),
    (``DualTruncateFacePhaseKempe.selected_cross, []),
    (``DualTruncateFacePhaseKempe.physical_region,
      [``DualTruncateFacePhaseKempe.selected_cross, ``DualTruncateFacePhaseKempe.phase_swap]),
    (``DualTruncateFacePhaseKempe.nextCorners_valid, [``DualTruncateFacePhaseKempe.nextCorners_cross]),
    (``DualTruncateFacePhaseKempe.exact_effect, [``DualTruncateFacePhaseKempe.phase_swap]),
    (``DualTruncateFacePhaseKempe.step_cross_preserved, [``DualTruncateFacePhaseKempe.exact_effect]),
    (``DualTruncateFacePhaseKempe.step_error, [``DualTruncateCornerSemantics.corner_edgeColours]),
    (``DualTruncateFacePhaseKempe.normalize_error, [``DualTruncateFacePhaseKempe.step_error]),
    (``DualTruncateFacePhaseKempe.normalize_exact, [``DualTruncateFacePhaseKempe.normalize_error]),
    (``DualTruncateFacePhaseKempe.normalize_cross_preserved,
      [``DualTruncateFacePhaseKempe.step_cross_preserved]),
    (``DualTruncateFacePhaseGSLT.presentation, []),
    (``DualTruncateFacePhaseGSLT.event_physical,
      [``DualTruncateFacePhaseKempe.physical_region, ``DualTruncateFacePhaseKempe.exact_effect]),
    (``DualTruncateFacePhaseGSLT.route_cross_preserved,
      [``Mettapedia.GSLT.Ultrainfinite.Route.observe_eq_of_route]),
    (``DualTruncateFacePhaseGSLT.physical_history, [``DualTruncateFacePhaseGSLT.event_physical]),
    (``DualTruncateFacePhaseGSLT.repair, []),
    (``DualTruncateFacePhaseGSLT.repair_length, []),
    (``DualTruncateFacePhaseGSLT.repair_terminal, [``DualTruncateFacePhaseKempe.normalize_exact]),
    (``AdjacentSourceFacePhaseReduction.initial,
      [``DualTruncateSpanningFace.sourceColouring, ``DualTruncateSpanningFace.preserves_cross]),
    (``AdjacentSourceFacePhaseReduction.history, [``DualTruncateFacePhaseGSLT.repair]),
    (``AdjacentSourceFacePhaseReduction.terminal_coherent, [``DualTruncateFacePhaseKempe.normalize_error]),
    (``AdjacentSourceFacePhaseReduction.repairedSource,
      [``DualTruncateFacePhaseKempe.normalize, ``DualTruncateCornerCoherence.sourceColouring]),
    (``AdjacentSourceFacePhaseReduction.terminal_cross_preserved,
      [``DualTruncateFacePhaseKempe.normalize_cross_preserved]),
    (``AdjacentSourceFacePhaseReduction.strict_reconstruction,
      [``AdjacentSourceFacePhaseReduction.repairedSource, ``AdjacentSourceSplice.reduction_reconstruction]),
    (``AdjacentSourceFacePhaseReduction.operational_reconstruction,
      [``DualTruncateFacePhaseGSLT.physical_history, ``AdjacentSourceFacePhaseReduction.strict_reconstruction]),
    (``AdjacentSourceFacePhaseReduction.every_complete_sweep,
      [``AdjacentSourceFacePhaseReduction.repairedSource, ``AdjacentSourceSplice.every_complete_sweep]),
    (``DualTruncateFacePhaseExample.inputCorners_valid, []),
    (``DualTruncateFacePhaseExample.input_requires_repair, []),
    (``DualTruncateFacePhaseExample.repair_exact, [``DualTruncateFacePhaseKempe.normalize_exact]),
    (``DualTruncateFacePhaseExample.all_cross_preserved,
      [``DualTruncateFacePhaseKempe.normalize_cross_preserved]),
    (``DualTruncateFacePhaseExample.history_length, [])]
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
    `Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample,
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
      if !(`Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseExample).isPrefixOf root &&
          fixtures.any (·.isPrefixOf name) then
        throwError m!"Finite fixture in general root {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Physical face-phase normalization: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    exact physical region stages, intermediate target Tait witnesses, joint cross-edge \
    preservation and strict/GSLT splice consumer present; complete theorem and generic \
    source suppliers absent; nontrivial literal parallel-edge fixture checked separately."
