import Mettapedia.GraphTheory.FourColor.SourceAlternatingBoundaryRepair
import Lean.Util.CollectAxioms

/-! Audit the actual planar-separation dependency, the constructed source
region, full witness reconstruction, physical effect and faithful GSLT
consumer. Finite graph fixtures and full-colouring suppliers are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``SourceAlternatingBoundaryRepair.no_disjoint_four_port_paths,
      [``GoertzelV24CyclicBoundaryAlternatingTrail.no_disjoint_trail_between_boundary_arcs,
       ``GoertzelV24CyclicBoundaryClosure.boundaryClosure_isTrail]),
    (``SourceAlternatingBoundaryRepair.colour_walk_edges_disjoint, []),
    (``SourceAlternatingBoundaryRepair.alternating_pair_separation,
      [``SourceAlternatingBoundaryRepair.no_disjoint_four_port_paths,
       ``SourceAlternatingBoundaryRepair.colour_walk_edges_disjoint]),
    (``SourceAlternatingBoundaryRepair.third_pair, []),
    (``SourceAlternatingBoundaryRepair.component_region,
      [``SourceAlternatingBoundaryRepair.reachable_colour]),
    (``SourceAlternatingBoundaryRepair.exists_repair,
      [``SourceAlternatingBoundaryRepair.alternating_pair_separation,
       ``SourceAlternatingBoundaryRepair.component_region,
       ``TwoCellBoundaryChoice.repair_one_pin]),
    (``SourceAlternatingBoundaryRepair.Repair.complete,
      [``TwoCellSourceRepair.Frame.complete, ``SourcePatchKempe.switched_exterior]),
    (``SourceAlternatingBoundaryRepair.Geometry.repair,
      [``SourceAlternatingBoundaryRepair.exists_repair]),
    (``SourceAlternatingBoundaryRepair.Geometry.sourceColouring,
      [``SourceAlternatingBoundaryRepair.exists_repair,
       ``SourceAlternatingBoundaryRepair.Repair.complete]),
    (``SourceAlternatingBoundaryRepair.Geometry.target_tait,
      [``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateColoring.colouring_nonzero]),
    (``SourceAlternatingBoundaryRepair.Geometry.physical_region,
      [``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateKempeTransport.physical_region]),
    (``SourceAlternatingBoundaryRepair.Geometry.reconstructs,
      [``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateKempeTransport.exact_effect,
       ``TwoCellSourceRepair.Frame.reconstructed_extends]),
    (``SourceAlternatingBoundaryRepair.Geometry.every_complete_sweep,
      [``SourceAlternatingBoundaryRepair.exists_repair,
       ``DualTruncateConstructionGSLT.supported_encoded_route])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.ProperWord,
    `Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateStructuralColoring.source_of_connected_pair,
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
  logInfo m!"Alternating source boundary repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    actual cyclic-boundary separation, constructed source region, whole reconstruction \
    and GSLT consumer present; complete classical endpoints, full-colouring suppliers \
    and finite graph fixtures absent."
