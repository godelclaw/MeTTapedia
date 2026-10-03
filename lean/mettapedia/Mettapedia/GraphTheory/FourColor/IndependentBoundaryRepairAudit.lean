import Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepair
import Lean.Util.CollectAxioms

open Lean Elab Command
open SimpleGraph KempeIndependentLift
open Mettapedia.GraphTheory.FourColor.IndependentBoundaryRepair

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``Coloring.avoiding_of_pointwise_swap,
      [``Coloring.component_changed_of_pointwise_swap, ``KempeStepAvoiding]),
    (``single_vertex, [``Coloring.kempeComponentSet_subset_of_closed]),
    (``fibre_path, [``single_vertex, ``KempeStepAvoiding]),
    (``colour_bridge, [``Equiv.swap]),
    (``partial_swap_avoiding, [``colour_bridge, ``fibre_path, ``Coloring.avoiding_of_pointwise_swap]),
    (``extends_iff, [``Coloring.restrictInduce]),
    (``pair_fibration, [``partial_swap_avoiding]),
    (``projected_history_iff,
      [``Mettapedia.Combinatorics.Reconfiguration.Fibration.reach,
       ``Mettapedia.Combinatorics.Reconfiguration.ProjectsSteps.reach]),
    (``pair_guard_iff, [``extends_iff]),
    (``square_repair, [``partial_swap, ``Mettapedia.GSLT.Ultrainfinite.Route]),
    (``square_prepared_relative, [``partial_swap_avoiding]),
    (``square_paths_lift, [``projected_history_iff]),
    (``CoupledStar.joint_history, [``partial_swap_avoiding, ``Mettapedia.GSLT.Ultrainfinite.Route]),
    (``CoupledStar.no_individual_extension, [``CoupledStar.graph])]
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
  logInfo m!"Independent boundary repair: {contracts.length} roots; {all.toList.length} declarations. \
    Joint extension constraints preserve physical reachability with fixed context. \
    Individual retained components need not have admissible targets."
