import Mettapedia.GraphTheory.FourColor.DualTruncateForestExample
import Lean.Util.CollectAxioms

/-! Audit the finite-forest argument, actual boundary visibility, exact
source-choice equivalence, and the fixed-exterior consumer. Neither the
general family law nor the finite consumer uses a complete colouring supplier. -/

open Lean Elab Command
open Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FiniteForestBranching.eq_bot, []),
    (``DualTruncateForestCollapse.difference_sum_zero, []),
    (``DualTruncateForestCollapse.other_nonzero_difference,
      [``DualTruncateForestCollapse.difference_sum_zero]),
    (``DualTruncateForestCollapse.difference_zero_of_forest,
      [``FiniteForestBranching.eq_bot, ``DualTruncateForestCollapse.other_nonzero_difference,
       ``DualTruncateCornerCoherence.difference_alpha]),
    (``DualTruncateForestCollapse.outside_visible, []),
    (``DualTruncateForestCollapse.rho_fixfree, [``VertexCodeCyclicEncoder.rot_ne]),
    (``DualTruncateForestCollapse.outside_corners,
      [``DualTruncateForestCollapse.outside_visible, ``DualTruncateForestCollapse.rho_fixfree]),
    (``DualTruncateForestCollapse.coherent,
      [``DualTruncateForestCollapse.difference_zero_of_forest,
       ``DualTruncateForestCollapse.outside_corners,
       ``DualTruncateCornerCoherence.coherent_of_difference_zero]),
    (``DualTruncateForestCollapse.source_witness,
      [``DualTruncateForestCollapse.coherent, ``DualTruncateCornerCoherence.sourceColouring]),
    (``DualTruncateForestCollapse.source_summary,
      [``DualTruncateForestCollapse.source_corners,
       ``DualTruncateForestCollapse.visible_outside_source]),
    (``DualTruncateForestCollapse.cornerSourceEquiv,
      [``DualTruncateForestCollapse.source_witness, ``DualTruncateForestCollapse.source_summary]),
    (``DualTruncateForestCollapse.extensionSourceEquiv,
      [``DualTruncateOpenPatch.extensionEquiv, ``DualTruncateForestCollapse.cornerSourceEquiv]),
    (``DualTruncateForestCollapse.extension_source_count,
      [``DualTruncateForestCollapse.extensionSourceEquiv]),
    (``DualTruncateForestExample.simple_source, []),
    (``DualTruncateForestExample.separated, []),
    (``DualTruncateForestExample.forest, []),
    (``DualTruncateForestExample.exterior_stars, []),
    (``DualTruncateForestExample.paired, []),
    (``DualTruncateForestExample.fibreEquiv,
      [``DualTruncateForestCollapse.extensionSourceEquiv,
       ``DualTruncateForestExample.exterior_stars]),
    (``DualTruncateForestExample.reconstruct_same,
      [``DualTruncateForestExample.fibreEquiv]),
    (``DualTruncateForestExample.assignmentEquiv, []),
    (``DualTruncateForestExample.assignment_count, []),
    (``DualTruncateForestExample.extension_count_three,
      [``DualTruncateForestExample.fibreEquiv,
       ``DualTruncateForestExample.assignmentEquiv,
       ``DualTruncateForestExample.assignment_count]),
    (``DualTruncateForestExample.selected_source_variables, []),
    (``DualTruncateForestExample.selected_target_vertices, []),
    (``DualTruncateForestExample.exterior_target_vertices, []),
    (``DualTruncateForestExample.internal_polygon_variables, []),
    (``DualTruncateForestExample.internal_cross_variables, []),
    (``DualTruncateForestExample.every_complete_sweep,
      [``DualTruncateForestCollapse.source_summary, ``DualTruncateOpenPatch.every_complete_sweep])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    ``DualTruncateStructuralColoring.source_of_connected_pair,
    ``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    ``DualTruncateCoupledExample.source_shared_colouring,
    ``DualTruncateGeometryExample.target_coloured_geometry,
    ``DualTruncateOpenPatchExample.baseSource,
    ``DualTruncateOpenPatchExample.exterior_stars,
    ``DualTruncateOpenPatchExample.cornerWord,
    ``DualTruncateOpenPatchExample.patchCorners,
    ``DualTruncateOpenPatchExample.repaired]
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
      unless (`Mettapedia.GraphTheory.FourColor.DualTruncateForestExample).isPrefixOf root do
        if (`Mettapedia.GraphTheory.FourColor.DualTruncateForestExample).isPrefixOf name ||
            (`Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample).isPrefixOf name then
          throwError m!"Finite consumer data entered general theorem {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Exact separated-forest collapse: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical endpoints, source-colouring suppliers and diagnostic corner data absent; \
    finite exterior values absent from the general family law."
