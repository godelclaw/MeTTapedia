import Mettapedia.GraphTheory.Kempe.CycleAnchors
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``KempeCycleAnchors.same_anchor_path,
    ``KempeCycleAnchors.representatives_card_le,
    ``KempeCycleAnchors.one_anchor_card_le_four, ``KempeCycleAnchors.history_iff]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor,
    `Mettapedia.GraphTheory.FourColor]
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
    unless seen.contains ``KempeForestFibre.list_connected &&
        seen.contains ``Coloring.avoiding_of_pointwise_swap do
      throwError m!"Missing forest induction or physical reconstruction in {root}"
    if root == ``KempeCycleAnchors.history_iff then
      unless seen.contains ``KempeGuardedLift.history_iff do
        throwError "Missing exact guarded history transport"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Cycle anchors: {roots.length} roots; {all.toList.length} declarations. \
    Retained cycle-breaking colours bound classes and reconstruct guarded histories."
