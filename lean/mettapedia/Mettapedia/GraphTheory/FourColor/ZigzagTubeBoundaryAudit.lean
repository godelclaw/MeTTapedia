import Mettapedia.GraphTheory.FourColor.ZigzagTubeBoundaryGSLT
import Lean.Util.FoldConsts

/-!
# Audit of finite-certificate tube normalization

The checked roots connect the old finite ring certificate to arbitrary tube
lengths, physical closed-map reduction, and literal graphs built along GSLT
routes. The dependency closure must contain the decoder and geometry proofs.
It must not use a complete Four Colour theorem or the classical catalogue.
-/

open Mettapedia.GraphTheory.FourColor
open ZigzagRing ZigzagTubeBoundaryGSLT
open Mettapedia.GSLT.RelationalRouteSemantics

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``five_tube_normalize, [``GoertzelV24FiveTubeExclusion.five_ring_stabilizes,
      ``accepts_iff_testBit, ``mem_iterate_singleton_iff_transfer,
      ``tube_add_of_stabilizes, ``tube_accepts_iff]),
    (``strict_five_tube_reduction, [``five_tube_normalize, ``tube_vertex_card,
      ``tube_replacement_class, ``tube_replacement_euler, ``tube_replacement_structural,
      ``OpenTangleClosedBoundary.compose_colorable_iff]),
    (``reconstructFiveTube_isTait, [``five_tube_normalize,
      ``OpenTangleClosedBoundary.replaceEdgeColoring_isTait]),
    (``reconstructFiveTube_exterior, [``five_tube_normalize,
      ``OpenTangleClosedBoundary.replaceEdgeColoring_exterior]),
    (``presentation, [``theory, ``Event]),
    (``route_context_iff, [``five_tube_normalize,
      ``Semantics.BoundaryReduction.forwardRoute, ``Semantics.BoundaryReduction.backwardRoute,
      ``Semantics.replaceInContext]),
    (``Chain.witnessEquiv, [``OpenTangleWitnessComposition.serialEquiv,
      ``Chain.realize, ``Chain.route, ``Semantics.Witness]),
    (``Chain.normalize_boundary_iff, [``five_tube_normalize, ``Chain.witnessEquiv,
      ``Semantics.BoundaryReduction.supports_iff])]
  let mut inspected : NameSet := {}
  for (root, required) in contracts do
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
      if (`FourColor).isPrefixOf name then
        throwError m!"Classical FourColor dependency in independent tube theorem {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Five-port tube normalization: {contracts.length} roots; \
    {inspected.toList.length} declarations in their combined dependency closure; \
    no classical FourColor dependencies."
