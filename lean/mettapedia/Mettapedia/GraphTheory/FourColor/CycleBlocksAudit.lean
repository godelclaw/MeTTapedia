import Mettapedia.GraphTheory.FourColor.FrozenCycleFamily
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeBlockChoices.combine, ``KempeBlockChoices.combine_exterior,
    ``KempeBlockChoices.anchored_history_iff, ``FrozenCycleFamily.Witnesses.same_exterior,
    ``FrozenCycleFamily.Witnesses.no_path, ``FrozenCycleFamily.Witnesses.summary_card_lower_bound]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor,
    `Mettapedia.GraphTheory.FourColor.WheelRepairData,
    `Mettapedia.GraphTheory.FourColor.ExceptionalRepairData]
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
    if root == ``KempeBlockChoices.anchored_history_iff then
      unless seen.contains ``KempePairBlocks.transition_iff &&
          seen.contains ``KempeForestFibre.list_connected &&
          seen.contains ``Coloring.avoiding_of_pointwise_swap do
        throwError "Missing joint guard factorization or physical forest reconstruction"
    if root == ``FrozenCycleFamily.Witnesses.summary_card_lower_bound then
      unless seen.contains ``KempeBlockChoices.combine &&
          seen.contains ``FrozenBoundaryObserver.no_lift_renamed do
        throwError "Missing actual colouring construction or physical class obstruction"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Cyclic blocks: {roots.length} roots; {all.toList.length} declarations. \
    Boolean colouring choices compose; frozen observers bound summaries; factored guards reconstruct."
