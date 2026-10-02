import MettapediaFourColor.D3009ColouringExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``D3009Construction.numbered_eq, [``ExecutableConfiguration.numbered]),
    (``D3009Construction.source_graph, [``D3009Wheel.input]),
    (``D3009Construction.source_rotation, [``D3009Wheel.input]),
    (``D3009Construction.ringTrace_iff, [``ConfigurationTable.Realization.forwardRingTrace]),
    (``D3009Construction.embeddable, [``embeddable_cfquiz]),
    (``WheelColouring.coloringEquiv, [``WheelColouring.extend, ``WheelColouring.observe]),
    (``WheelColouring.extends_iff, [``WheelColouring.extend]),
    (``CyclicColourRoute.supports_iff, [``CyclicColourRoute.supports_succ]),
    (``CyclicColourRoute.closed_iff, [``CyclicColourRoute.supports_iff]),
    (``CyclicColourRoute.split_iff,
      [``Mettapedia.GSLT.RelationalRouteSemantics.Semantics.supports_append_iff]),
    (``WheelColouringGSLT.extends_iff, [``CyclicColourRoute.closed_iff]),
    (``WheelColouringGSLT.split_iff, [``CyclicColourRoute.split_iff]),
    (``D3009Colouring.coloringEquiv, [``WheelColouring.coloringEquiv, ``D3009Colouring.source]),
    (``D3009Colouring.two_sectors_iff, [``WheelColouringGSLT.split_iff]),
    (``D3009Colouring.constructionTrace_iff,
      [``D3009Construction.ringTrace_iff, ``WheelColouringGSLT.witness_iff]),
    (``D3009ColouringExample.stitched, [``D3009Colouring.two_sectors_iff]),
    (``D3009ColouringExample.first_sector, [``CyclicColourRoute.supports_iff]),
    (``D3009ColouringExample.second_sector, [``CyclicColourRoute.supports_iff]),
    (``D3009ColouringExample.incompatible_sectors,
      [``D3009ColouringExample.odd_cycle, ``D3009Colouring.two_sectors_iff])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.KempeProfileCertificate,
    `FourColor.Bulk]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Forbidden complete theorem or repair certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Wheel colouring: {roots.length} roots; {all.toList.length} declarations. \
    Exact source construction, witness equivalence and joint cyclic GSLT closure. \
    No configuration repair certificate or full Four Colour theorem is consumed. \
    Finite repair exploration is not a premise of these results."
