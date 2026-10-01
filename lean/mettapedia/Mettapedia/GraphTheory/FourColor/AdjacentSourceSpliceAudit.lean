import Mettapedia.GraphTheory.FourColor.AdjacentSourceSplice
import Lean.Util.CollectAxioms

/-! Audit the actual opposite-pair splice, its smaller embedded target,
exact vertex decrease, witness extraction, coupled repair and physical/GSLT
reconstruction. Classical endpoints, full-colouring suppliers and finite
geometric fixtures are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``AdjacentSourceSplice.smaller_spherical,
      [``GoertzelV24PlanarBondSpliceEuler.orbitSphericalCubicMapData_orderedCutSplice_of_planar_bond,
       ``GoertzelV24AdjacentPairBoundary.AdjacentPairData.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder]),
    (``AdjacentSourceSplice.smaller_rotation, []),
    (``AdjacentSourceSplice.smaller_connected, []),
    (``AdjacentSourceSplice.smaller_target_geometry,
      [``AdjacentSourceSplice.smaller_spherical, ``DualTruncateMapGeometry.mapClass_of]),
    (``AdjacentSourceSplice.target_strict_decrease, [``AdjacentSourceSplice.smaller_spherical]),
    (``AdjacentSourceSplice.source_vertices_removed, []),
    (``AdjacentSourceSplice.target_vertices_removed,
      [``AdjacentSourceSplice.source_vertices_removed, ``AdjacentSourceSplice.smaller_spherical]),
    (``AdjacentSourceSplice.exterior_proper, [``AdjacentSourceSplice.interior]),
    (``AdjacentSourceSplice.seam_constraints,
      [``GoertzelV24AdjacentPairBoundary.AdjacentPairData.reductionRotationSystem_alpha_leftSeamDart]),
    (``AdjacentSourceSplice.choices_or_alternating, [``TwoCellBoundaryChoice.choices_iff]),
    (``AdjacentSourceSplice.smaller_observations, [``AdjacentSourceSplice.interior]),
    (``AdjacentSourceSplice.exists_repair,
      [``AdjacentSourceSplice.seam_constraints, ``AdjacentSourceSplice.choices_or_alternating,
       ``AdjacentSourceBoundaryRepair.geometry, ``SourceAlternatingBoundaryRepair.exists_repair]),
    (``AdjacentSourceSplice.sourceColouring,
      [``AdjacentSourceSplice.exterior_proper, ``AdjacentSourceSplice.exists_repair,
       ``TwoCellSourceRepair.Frame.complete]),
    (``AdjacentSourceSplice.reduction_reconstruction,
      [``AdjacentSourceSplice.smaller_target_geometry, ``AdjacentSourceSplice.target_vertices_removed,
       ``AdjacentSourceSplice.exists_repair, ``DualTruncateColoring.colouring_nonzero]),
    (``AdjacentSourceSplice.physical_region,
      [``AdjacentSourceSplice.exists_repair, ``DualTruncateKempeTransport.physical_region]),
    (``AdjacentSourceSplice.reconstructs,
      [``AdjacentSourceSplice.exists_repair, ``DualTruncateKempeTransport.exact_effect,
       ``TwoCellSourceRepair.Frame.reconstructed_extends]),
    (``AdjacentSourceSplice.every_complete_sweep,
      [``AdjacentSourceSplice.exists_repair, ``DualTruncateConstructionGSLT.supported_encoded_route])]
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
  logInfo m!"Adjacent source splice: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    actual smaller spherical cubic target, exact six-vertex decrease, smaller witness extraction, \
    coupled geometric repair and physical/GSLT reconstruction present; \
    complete classical endpoints, full-colouring suppliers and finite graph fixtures absent."
