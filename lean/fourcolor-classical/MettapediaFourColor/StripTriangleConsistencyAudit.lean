import MettapediaFourColor.StripTriangleConsistencyRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripTriangleConsistency.compose_iff, [``StripResponseSummary.r2,
      ``StripTriangleConsistency.right2, ``StripResponseSummary.ValidCore]),
    (``StripTriangleConsistency.source_iff, [``StripTriangleConsistency.compose_iff,
      ``StripSourceExtension.colouring, ``StripResponseSummary.valid_of_colouring]),
    (``StripTriangleConsistency.triangle_edges, [``StripResponseSummary.edges]),
    (``StripTriangleConsistency.all_edges_covered, [``StripTriangleConsistency.triangles]),
    (``StripTriangleConsistency.triangles_complete, [``StripResponseSummary.edges]),
    (``StripTriangleConsistency.domains_sound, [``StripTriangleConsistency.domains_exact]),
    (``StripTriangleConsistency.nonempty_domains, [``StripTriangleConsistency.domains]),
    (``StripTriangleConsistency.supported_domains, [``StripTriangleConsistency.Supported]),
    (``StripTriangleConsistency.left_nonempty, [``StripResponseSummary.r2]),
    (``StripTriangleConsistency.right_nonempty, [``StripTriangleConsistency.right2]),
    (``StripTriangleConsistency.no_core, [``StripTriangleConsistency.compose_iff,
      ``StripTriangleConsistency.left_pin, ``StripTriangleConsistency.right_pin]),
    (``StripTriangleConsistency.no_source, [``StripTriangleConsistency.no_core,
      ``StripResponseSummary.valid_of_colouring]),
    (``StripTriangleConsistency.local_support_not_sufficient,
      [``StripTriangleConsistency.supported_domains, ``StripTriangleConsistency.no_source]),
    (``StripTriangleConsistencyRepair.repair, [``KempeBalancedBlock.coclosure,
      ``StripTriangleConsistencyRepair.release, ``StripSymbolicRepair.direct_sound]),
    (``StripTriangleConsistencyRepair.compatible_changed,
      [``StripTriangleConsistencyRepair.repair, ``GraphTraceAlignment.align,
       ``StripTriangleConsistency.no_core])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Triangle support obstruction, composition and repair: {contracts.length} roots; \
    {all.toList.length} declarations."
