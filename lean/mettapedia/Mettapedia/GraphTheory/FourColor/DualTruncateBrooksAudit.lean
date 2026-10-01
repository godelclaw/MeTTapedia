import Mettapedia.GraphTheory.FourColor.DualTruncateBrooksExample
import Lean.Util.CollectAxioms

/-! Audit the general subcubic theorem, its boundary extension mechanisms,
and target-only inverse/GSLT consumers. Source-specific colour suppliers,
colour-word tables and complete classical endpoints are excluded. -/

open Lean Elab Command
open Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OrderedBoundaryColouring.extend, []),
    (``OrderedBoundaryColouring.low_degree_extension, [``OrderedBoundaryColouring.extend]),
    (``OrderedBoundaryColouring.coupled_region_extension, [``OrderedBoundaryColouring.extend]),
    (``OrderedBoundaryColouring.coupled_extension_of_connected_deletion,
      [``OrderedBoundaryColouring.coupled_region_extension,
       ``OrderedBoundaryColouring.regionOrder_of_connected_deletion]),
    (``SubcubicPathSelection.exists_maximal, [``SubcubicPathSelection.StartedPath.append]),
    (``SubcubicPathSelection.fullPathOrder, [``SubcubicPathSelection.StartedPath.indexEquiv]),
    (``SubcubicCycleExtension.StartedPath.tailOrder, []),
    (``SubcubicCycleExtension.selected_tail_extension,
      [``SubcubicCycleExtension.StartedPath.tailOrder,
       ``OrderedBoundaryColouring.coupled_region_extension]),
    (``SubcubicThreeColouring.colourable,
      [``OrderedBoundaryColouring.low_degree_extension,
       ``SubcubicPathSelection.exists_maximal, ``SubcubicPathSelection.fullPathOrder,
       ``CoupledThreeColouring.colouring_of_coupledOrder,
       ``SubcubicCycleExtension.selected_tail_extension,
       ``SubcubicThreeColouring.combine, ``SubcubicThreeColouring.cliqueFree_induce]),
    (``SubcubicCliqueDomain.cliqueFree_of_connected_card_gt, []),
    (``SubcubicCliqueDomain.colourable_of_connected_card_gt,
      [``SubcubicThreeColouring.colourable, ``SubcubicCliqueDomain.cliqueFree_of_connected_card_gt]),
    (``DualTruncateBrooksSource.source_of_cliqueFree,
      [``SubcubicThreeColouring.colourable, ``DualTruncateStructuralColoring.ofPrimalColouring]),
    (``DualTruncateBrooksSource.source_of_connected_large,
      [``DualTruncateBrooksSource.source_of_cliqueFree,
       ``SubcubicCliqueDomain.cliqueFree_of_connected_card_gt]),
    (``DualTruncateBrooksSource.inverse_source,
      [``DualTruncateInverseGeometry.source_size, ``DualTruncateInverseGeometry.source_connected,
       ``DualTruncateInverseGeometry.source_cubic, ``DualTruncateBrooksSource.source_of_connected_large]),
    (``DualTruncateBrooksSource.inverse_tait,
      [``DualTruncateBrooksSource.inverse_source, ``DualTruncateInverseGeometry.tait]),
    (``DualTruncateBrooksSource.recognized_tait,
      [``DualTruncateBrooksSource.inverse_tait, ``DualTruncateInverse.fromCover]),
    (``DualTruncateBrooksSource.every_complete_sweep,
      [``DualTruncateBrooksSource.inverse_source, ``DualTruncateInverseGeometry.every_complete_sweep]),
    (``DualTruncateBrooksExample.prism_recovered_colouring,
      [``DualTruncateBrooksSource.inverse_source, ``DualTruncateSourceDomainExample.unmarked_hexagons]),
    (``DualTruncateBrooksExample.prism_target_tait, [``DualTruncateBrooksSource.inverse_tait]),
    (``DualTruncateBrooksExample.cube_recovered_colouring,
      [``DualTruncateBrooksSource.inverse_source, ``DualTruncateInverseExample.unmarked_hexagons]),
    (``DualTruncateBrooksExample.cube_target_tait, [``DualTruncateBrooksSource.inverse_tait]),
    (``DualTruncateBrooksExample.prism_every_complete_sweep,
      [``DualTruncateBrooksExample.prism_recovered_colouring,
       ``DualTruncateInverseGeometry.every_complete_sweep]),
    (``DualTruncateBrooksExample.cube_every_complete_sweep,
      [``DualTruncateBrooksExample.cube_recovered_colouring,
       ``DualTruncateInverseGeometry.every_complete_sweep]),
    (``DualTruncateBrooksExample.four_clique_exception, [])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    ``DualTruncateStructuralColoring.source_of_connected_pair,
    ``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    ``DualTruncateSourceDomainExample.source_shared_colouring,
    ``DualTruncateSourceDomainExample.recovered_colouring,
    ``DualTruncateSourceDomainExample.recognized_coloured_target,
    ``DualTruncateInverseExample.recovered_colouring,
    ``DualTruncateInverseExample.recognized_coloured_target,
    ``DualTruncateGeometryExample.target_coloured_geometry]
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
  logInfo m!"Subcubic Brooks source bridge: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    previous source-specific colouring suppliers, colour-word tables and \
    complete classical theorem absent."
