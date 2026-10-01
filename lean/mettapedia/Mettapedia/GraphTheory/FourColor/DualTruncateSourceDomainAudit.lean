import Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample
import Lean.Util.CollectAxioms

/-! Audit the recovered cyclic-cut obstruction and the alternative coupled
colouring supplier, including actual face-cover selection and complete GSLT
consumers. Colour words, cyclic-four suppliers and classical endpoints are
excluded from the load-bearing dependency closures. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CyclicEdgeCutIso.cutMap_card, [``CyclicEdgeCutIso.crossingDartEquiv]),
    (``CyclicEdgeCutIso.cyclic_connectivity,
      [``CyclicEdgeCutIso.cutMap, ``CyclicEdgeCutIso.cycle_map]),
    (``DualTruncateInverseRoundTrip.primalIso,
      [``DualTruncateInverseRoundTrip.vertexEquiv, ``RotationSystemExactTransport.primalIso]),
    (``DualTruncateSourceDomainExample.valid, []),
    (``DualTruncateSourceDomainExample.source_spherical,
      [``DualTruncateSourceDomainExample.source_face_count]),
    (``DualTruncateSourceDomainExample.source_not_cyclic_four,
      [``DualTruncateSourceDomainExample.crossing_count,
       ``DualTruncateSourceDomainExample.top_cycle, ``DualTruncateSourceDomainExample.bottom_cycle]),
    (``DualTruncateSourceDomainExample.target_mapClass,
      [``DualTruncateMapGeometry.mapClass_of]),
    (``DualTruncateSourceDomainExample.nonhex_marked_iff,
      [``DualTruncateSourceDomainExample.source_face_length]),
    (``DualTruncateSourceDomainExample.recovered_primalIso,
      [``DualTruncateInverseRoundTrip.primalIso,
       ``DualTruncateInverseRoundTrip.fromCover_data,
       ``DualTruncateSourceDomainExample.nonhex_marked_iff]),
    (``DualTruncateSourceDomainExample.recovered_not_cyclic_four,
      [``CyclicEdgeCutIso.cyclic_connectivity,
       ``DualTruncateSourceDomainExample.source_not_cyclic_four,
       ``DualTruncateSourceDomainExample.recovered_primalIso]),
    (``DualTruncateSourceDomainExample.source_shared_colouring,
      [``Mettapedia.GraphTheory.CoupledThreeColouring.colouring_of_connected_pair,
       ``DualTruncateSourceDomainExample.retained_connected]),
    (``DualTruncateSourceDomainExample.recovered_colouring,
      [``DualTruncateSourceDomainExample.source_shared_colouring,
       ``DualTruncateInverseRoundTrip.colouring,
       ``DualTruncateSourceDomainExample.nonhex_marked_iff]),
    (``DualTruncateSourceDomainExample.source_domain_obstruction,
      [``DualTruncateSourceDomainExample.recovered_not_cyclic_four,
       ``DualTruncateInverseGeometry.source_spherical,
       ``DualTruncateInverseGeometry.source_connected,
       ``DualTruncateInverseGeometry.tait]),
    (``DualTruncateSourceDomainExample.every_complete_sweep,
      [``DualTruncateInverseGeometry.every_complete_sweep,
       ``DualTruncateSourceDomainExample.recovered_colouring])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample.target_tait,
    `Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample.target_coloured_geometry]
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
  logInfo m!"Dual-and-truncate source-domain obstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    source colour-word certificates, cyclic-four supplier and complete classical theorem absent."
