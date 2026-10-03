import Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation
import Lean.Util.CollectAxioms

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``word_update_factors, [``SimpleGraph.Coloring.swapOnKempeComponent, ``PairConnected]),
    (``Square.same_view, [``SimpleGraph.Reachable, ``Square.graph]),
    (``Square.left_switch, [``SimpleGraph.Coloring.swapOnKempeComponent]),
    (``Square.right_switch, [``SimpleGraph.Coloring.swapOnKempeComponent]),
    (``Square.different_after, [``SimpleGraph.Reachable]),
    (``Square.no_deterministic_update,
      [``Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors]),
    (``Square.no_two_step_word_update,
      [``rootedSwitch_apply, ``Square.same_view]),
    (``Square.prepared_history,
      [``Mettapedia.GSLT.Ultrainfinite.Route, ``SimpleGraph.Coloring.swapOnKempeComponent])]
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
  logInfo m!"Boundary observation: {contracts.length} roots; {all.toList.length} declarations. \
    The immediate word update factors; the full partition update does not. \
    Silent preparation retains actual component witnesses."
