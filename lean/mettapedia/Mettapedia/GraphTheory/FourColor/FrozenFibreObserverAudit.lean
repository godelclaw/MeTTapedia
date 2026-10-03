import Mettapedia.GraphTheory.FourColor.FrozenFibreObserver
import Lean.Util.CollectAxioms

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let roots := [``FrozenFibreObserver.not_fibres, ``FrozenFibreObserver.not_fibration]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.CompositionalComplete, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData]
  let mut all : NameSet := {}
  for root in roots do
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
    unless seen.contains ``FrozenBoundaryObserver.no_lift_renamed do
      throwError m!"Missing physical observer obstruction in {root}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Frozen fibre observer: {roots.length} roots; {all.toList.length} declarations. \
    A retained colouring alone cannot identify physically disconnected hidden extensions."
