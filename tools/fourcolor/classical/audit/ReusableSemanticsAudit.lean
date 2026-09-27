import Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition
import Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT
import Mettapedia.GraphTheory.Representation.ColoringTransport
import Mettapedia.GraphTheory.Representation.MatrixOperationalTranslation
import Mettapedia.OSLF.MeTTaIL.PremiseRouteSemantics
import Lean.Util.FoldConsts

/-!
# Audit of reusable compositional semantics and its applications

The inspected roots retain actual colouring witnesses, connect their support
to literal graph decoding, count compatible colourings, and transport choices
through representation conversions. A separate MeTTa premise-engine consumer
uses the same replacement operation in every serial context.

This audit checks each root's transitive axiom set and named mathematical
dependencies. It neither asserts universal colourability nor audits unrelated
declarations merely because their modules were imported.
-/

open Mettapedia.GSLT.RelationalRouteSemantics
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.Representation
open Mettapedia.OSLF.MeTTaIL

#check @Semantics.appendEquiv
#check @OpenTangleWitnessComposition.count_serial
#check @SourceConstructionGSLT.encoded_support_iff
#check @ColoringTransport.liftPath
#check @MatrixOperationalTranslation.embedding
#check @PremiseRouteSemantics.deduplicate_freshness_iff

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``Semantics.supports_append_iff,
      [``Semantics.appendEquiv]),
    (``Semantics.replaceInContext,
      [``Semantics.appendEquiv]),
    (``Semantics.viable_append_iff,
      [``Semantics.supports_append_iff]),
    (``OpenTangleWitnessComposition.count_serial,
      [``OpenTangleWitnessComposition.serialEquiv,
        ``Nat.card_prod]),
    (``OpenTangleWitnessComposition.replaceInContext_exteriorWitnesses,
      [``OpenTangleWitnessComposition.replaceInContext,
        ``OpenTangleWitnessComposition.serialEquiv]),
    (``VertexConstructionGSLT.supports_realization_iff,
      [``VertexCodeTrace.Trace.support_exact,
        ``Semantics.supports_append_iff]),
    (``SourceConstructionGSLT.encoded_support_iff,
      [``VertexConstructionGSLT.closed_realization_iff,
        ``SourceVertexCodeTerminalAcceptance.tangle_taitColorable_iff]),
    (``ColoringTransport.path_boundary_card_eq,
      [``ColoringTransport.boundaryEquiv,
        ``RepresentationGSLT.path_commutes]),
    (``ColoringTransport.liftPath_preserves_colour,
      [``ColoringTransport.liftPath,
        ``RepresentationGSLT.step_commutes]),
    (``MatrixOperationalTranslation.embedding,
      [``MatrixBridge.matrix_step_from_encoded_iff]),
    (``MatrixOperationalTranslation.no_scan_to_matrix_step_translation,
      [``MatrixOperationalTranslation.scan_has_two_steps,
        ``MatrixOperationalTranslation.matrix_one_step_terminal]),
    (``PremiseRouteSemantics.deduplicate_freshness_iff,
      [``Semantics.replaceInContext,
        ``PremiseRouteSemantics.supports_engine_iff]),
    (``PremiseRouteSemantics.SharedBinding.conflicting_route,
      [``PremiseRouteSemantics.SharedBinding.conflicting_sequence,
        ``PremiseRouteSemantics.supports_engine_iff])]
  let mut inspected : NameSet := {}
  for (rootName, required) in contracts do
    let mut seen : NameSet := {}
    let mut todo := [rootName]
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
        throwError m!"Required dependency {name} is absent from {rootName}"
    let axioms ← liftCoreM <| collectAxioms rootName
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {rootName}: {name}"
    logInfo m!"Audited {rootName}: {axioms.toList}"
  let rootCount := contracts.length
  let closureCount := inspected.toList.length
  logInfo m!"Reusable semantics: {rootCount} roots; \
    {closureCount} declarations in their combined dependency closure."
