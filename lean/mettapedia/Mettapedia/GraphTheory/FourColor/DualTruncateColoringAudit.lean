import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT
import Lean.Util.CollectAxioms

/-! Audit the literal construction, local reconstruction, exact representation
transport and faithful operational route consumers. The source three-vertex
colouring is an explicit hypothesis; no complete Four Colour endpoint is used. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateColoring.rotation,
      [``DualTruncateColoring.cross_fiber, ``DualTruncateColoring.polygon_fiber]),
    (``DualTruncateColoring.cubic, [``DualTruncateColoring.rotation]),
    (``DualTruncateColoring.source_strictly_smaller,
      [``RotationSystem.card_darts_eq_three_times_card_vertices]),
    (``DualTruncateColoring.colouring,
      [``DualTruncateColoring.star_colour_distinct,
       ``DualTruncateColoring.crossColour_edge]),
    (``DualTruncateColoring.colouring_nonzero,
      [``DualTruncateColoring.crossColour_edge, ``add_ne_zero_of_ne]),
    (``DualTruncateColoring.tait_of_three_vertex_colouring,
      [``DualTruncateColoring.colouring, ``DualTruncateColoring.colouring_nonzero]),
    (``DualTruncateConstructionGSLT.supported_encoded_route,
      [``SourceConstructionGSLT.encoded_support_iff,
       ``DualTruncateConstructionGSLT.tait]),
    (``DualTruncateConstructionGSLT.tait_relabelled,
      [``GoertzelV24VertexSideReassembly.rotationSystemTaitColorable_of_dartEquiv,
       ``DualTruncateConstructionGSLT.tait]),
    (``DualTruncateConstructionGSLT.supported_relabelled_route,
      [``DualTruncateConstructionGSLT.tait_relabelled,
       ``RotationSystemExactTransport.rotationCyclic,
       ``SourceConstructionGSLT.encoded_support_iff])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `Lean.ofReduceBool, `sorryAx]
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
  logInfo m!"Dual-and-truncate colouring transport: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical theorem and trust-expanding shortcuts absent."
