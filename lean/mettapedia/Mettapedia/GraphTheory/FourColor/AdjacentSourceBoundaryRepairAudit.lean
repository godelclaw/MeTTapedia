import Mettapedia.GraphTheory.FourColor.AdjacentSourceBoundaryRepair
import Lean.Util.CollectAxioms

/-! Audit the derived adjacent-pair order and its actual source, target,
physical-switch and GSLT consumers. The order proof must use local cubic
rotations and planar complementary shores. Whole-colouring suppliers,
classical endpoints and finite graph fixtures are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``AdjacentSourceBoundaryRepair.reflection_rotate, []),
    (``AdjacentSourceBoundaryRepair.frame,
      [``GoertzelV24AdjacentPairBoundary.AdjacentPairData.rotationOrderedData]),
    (``AdjacentSourceBoundaryRepair.complement_connected, []),
    (``AdjacentSourceBoundaryRepair.deletedDart_bijective,
      [``GoertzelV24AdjacentPairBoundary.AdjacentPairData.rotationBoundaryDart_edgeOf]),
    (``AdjacentSourceBoundaryRepair.deletedOrder_successor,
      [``GoertzelV24AdjacentPairBoundary.AdjacentPairData.rotationBoundarySuccessor_apply_port]),
    (``AdjacentSourceBoundaryRepair.exists_retained_order,
      [``AdjacentSourceBoundaryRepair.deletedOrder_successor,
       ``GoertzelV24PlanarBondBoundaryOrder.retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond]),
    (``AdjacentSourceBoundaryRepair.geometry,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``GoertzelV24FaceDualConnectedness.orbitFaceInteriorDual_connected]),
    (``AdjacentSourceBoundaryRepair.repair,
      [``AdjacentSourceBoundaryRepair.geometry,
       ``SourceAlternatingBoundaryRepair.exists_repair]),
    (``AdjacentSourceBoundaryRepair.sourceColouring,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``SourceAlternatingBoundaryRepair.exists_repair,
       ``TwoCellSourceRepair.Frame.complete]),
    (``AdjacentSourceBoundaryRepair.target_tait,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateColoring.colouring_nonzero]),
    (``AdjacentSourceBoundaryRepair.physical_region,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateKempeTransport.physical_region]),
    (``AdjacentSourceBoundaryRepair.reconstructs,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateKempeTransport.exact_effect,
       ``TwoCellSourceRepair.Frame.reconstructed_extends]),
    (``AdjacentSourceBoundaryRepair.every_complete_sweep,
      [``AdjacentSourceBoundaryRepair.exists_retained_order,
       ``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateConstructionGSLT.supported_encoded_route])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.ProperWord,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_connected_pair,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairBoundary.AdjacentPairData.exists_cyclicallyOrdered_deletedColoring_join01_23_compatible,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization.GraphBackedVertexMinimalTaitCounterexample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    `Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair,
    `Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples,
    `Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample]
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
        throwError m!"Forbidden proof dependency in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Adjacent source boundary adapter: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    local rotation order, planar complementary shores, actual repair and whole reconstruction \
    and GSLT consumer present; complete classical endpoints, full-colouring suppliers \
    and finite graph fixtures absent."
