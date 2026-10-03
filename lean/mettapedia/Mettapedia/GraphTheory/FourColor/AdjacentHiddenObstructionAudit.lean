import Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph
open Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeTwoVertexFibre.fibre_path,
      [``KempeIndependentLift.single_vertex, ``Coloring.avoiding_of_pointwise_swap]),
    (``proper, [``graph, ``values]),
    (``same_boundary, [``boundary, ``state]),
    (``frozen, [``Coloring.mem_kempeComponentSet_of_adj]),
    (``retained_switch, [``KempeIndependentLift.single_vertex]),
    (``fibres_connected, [``KempeTwoVertexFibre.fibre_path]),
    (``no_lift, [``Coloring.IsTransparent.eq_of_reflTransGen]),
    (``not_lifts_image, [``retained_switch, ``no_lift]),
    (``not_lifts_joint_image, [``KempeIndependentLift.PairStep, ``no_lift]),
    (``repair_steps, [``Coloring.kempe_component_iff_mem_chain, ``Coloring.swap_apply_of_chain]),
    (``repaired_history, [``repair_steps, ``Mettapedia.GSLT.Ultrainfinite.Route])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.CompositionalComplete, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut seen : NameSet := {}
    let mut todo := [root]
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
    for requiredName in required do
      unless seen.contains requiredName do
        throwError m!"Missing physical or semantic dependency in {root}: {requiredName}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Adjacent hidden vertices: {contracts.length} roots; {all.toList.length} declarations. \
    Connected fibres and extendable targets do not imply lifting with fixed context. \
    Three physical switches repair after one boundary leaf is allowed to change temporarily."
