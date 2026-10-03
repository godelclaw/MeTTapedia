import Mettapedia.GraphTheory.FourColor.BoundaryCooperation
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph
open Mettapedia.GraphTheory.FourColor.BoundaryCooperation

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeStepAvoiding.comp_path, [``Coloring.avoiding_of_pointwise_swap]),
    (``kempe_path_comp, [``KempeStepAvoiding.comp_path]),
    (``card_vertices, [``Vertex]),
    (``core_fixed, [``kempe_path_comp,
      ``Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction.frozen]),
    (``boundary_lower_bound, [``core_fixed]),
    (``repairBudget_card, [``repairBudget]),
    (``repair, [``Coloring.avoiding_of_pointwise_swap]),
    (``boundary_restored, [``Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction.same_boundary]),
    (``retained_switch, [``KempeIndependentLift.single_vertex]),
    (``repair_budget_optimal, [``boundary_lower_bound]),
    (``no_uniform_budget, [``repair_budget_optimal]),
    (``repair_history, [``repair, ``Mettapedia.GSLT.Ultrainfinite.Route])]
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
  logInfo m!"Boundary cooperation: {contracts.length} roots; {all.toList.length} declarations. \
    Exactly r boundary vertices must be available for the width-r repair. \
    One uniform physical history construction handles every width."
