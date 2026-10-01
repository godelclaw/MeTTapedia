import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample
import Lean.Util.CollectAxioms

/-! Audit exact corner elimination, fixed-exterior reconstruction, the
source-collapse criterion, and genuine patch/GSLT consumers. The general
theorems exclude diagnostic corner data and all source-colouring suppliers. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateCornerSemantics.cross_of_star, []),
    (``DualTruncateCornerSemantics.corners_valid,
      [``DualTruncateCornerSemantics.cross_of_star, ``DualTruncateCornerSemantics.star_of_tait]),
    (``DualTruncateCornerSemantics.colouring,
      [``DualTruncateCornerSemantics.cross_edge, ``DualTruncateCornerSemantics.edgeColours_star]),
    (``DualTruncateCornerSemantics.colouringEquiv,
      [``DualTruncateCornerSemantics.corners_valid, ``DualTruncateCornerSemantics.colouring,
       ``DualTruncateCornerSemantics.corner_edgeColours, ``DualTruncateCornerSemantics.edgeColours_corners]),
    (``DualTruncateCornerCoherence.difference_alpha, []),
    (``DualTruncateCornerCoherence.coherent_of_difference_zero, []),
    (``DualTruncateCornerCoherence.source_witness_iff,
      [``DualTruncateCornerCoherence.sourceColouring, ``DualTruncateCornerCoherence.vertexColour_dart]),
    (``DualTruncateCornerCoherence.source_witness_iff_difference_zero,
      [``DualTruncateCornerCoherence.source_witness_iff,
       ``DualTruncateCornerCoherence.coherent_of_difference_zero]),
    (``DualTruncateOpenPatch.polygon_visible_iff, []),
    (``DualTruncateOpenPatch.cross_visible_iff, []),
    (``DualTruncateOpenPatch.extends_iff_visible_edges, []),
    (``DualTruncateOpenPatch.summary_valid,
      [``DualTruncateCornerSemantics.corners_balanced_of_stars]),
    (``DualTruncateOpenPatch.reconstructed_extends,
      [``DualTruncateOpenPatch.summary_valid, ``DualTruncateCornerSemantics.cross_of_star]),
    (``DualTruncateOpenPatch.summary_of_extension,
      [``DualTruncateCornerSemantics.corners_valid]),
    (``DualTruncateOpenPatch.extensionEquiv,
      [``DualTruncateOpenPatch.summary_valid, ``DualTruncateOpenPatch.reconstructed_extends,
       ``DualTruncateOpenPatch.summary_of_extension,
       ``DualTruncateCornerSemantics.corner_edgeColours, ``DualTruncateCornerSemantics.edgeColours_corners]),
    (``DualTruncateOpenPatch.extension_count, [``DualTruncateOpenPatch.extensionEquiv]),
    (``DualTruncateOpenPatch.vertexRegion_closed, []),
    (``DualTruncateOpenPatch.every_complete_sweep,
      [``DualTruncateOpenPatch.summary_valid, ``DualTruncateCornerSemantics.colouring,
       ``SourceConstructionGSLT.encoded_support_iff]),
    (``DualTruncateOpenPatchExample.patch_summary, []),
    (``DualTruncateOpenPatchExample.repaired, [``DualTruncateOpenPatch.extensionEquiv]),
    (``DualTruncateOpenPatchExample.repaired_tait, [``DualTruncateOpenPatchExample.repaired]),
    (``DualTruncateOpenPatchExample.exterior_fixed, [``DualTruncateOpenPatchExample.repaired]),
    (``DualTruncateOpenPatchExample.repaired_corners, [``DualTruncateCornerSemantics.corner_edgeColours]),
    (``DualTruncateOpenPatchExample.difference_nonzero, []),
    (``DualTruncateOpenPatchExample.no_matching_source_witness,
      [``DualTruncateCornerCoherence.source_witness_iff]),
    (``DualTruncateOpenPatchExample.every_complete_sweep,
      [``DualTruncateOpenPatch.every_complete_sweep, ``DualTruncateOpenPatchExample.patch_summary])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    ``DualTruncateStructuralColoring.source_of_connected_pair,
    ``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    ``DualTruncateCoupledExample.source_shared_colouring,
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
      unless (`Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample).isPrefixOf root do
        if (`Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample).isPrefixOf name then
          throwError m!"Diagnostic corner data entered general theorem {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Exact dual-and-truncate patch: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical endpoints and source-colouring suppliers absent; \
    diagnostic corner data absent from the general equivalence."
