import Mettapedia.GraphTheory.Kempe.ForestGuard
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``KempeForestFibre.exists_leaf, ``KempeForestFibre.list_connected,
    ``KempeForestFibre.fibre_path, ``KempeForestFibre.fibres, ``KempeForestFibre.history_iff,
    ``BinaryConstraints.leaf_iff, ``KempeForestGuard.transition_iff,
    ``KempeForestGuard.peel_transition_iff, ``KempeForestGuard.four_colour_alphabet]
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
    if root == ``KempeForestFibre.history_iff then
      unless seen.contains ``KempeForestFibre.list_connected &&
          seen.contains ``Coloring.avoiding_of_pointwise_swap do
        throwError "Missing forest induction or physical reconstruction"
    if root == ``KempeForestGuard.peel_transition_iff then
      unless seen.contains ``BinaryConstraints.leaf_iff &&
          seen.contains ``KempeForestGuard.transition_iff do
        throwError "Missing exact guard bridge or leaf reconstruction"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Forest guards: {roots.length} roots; {all.toList.length} declarations. \
    Arbitrary hidden forests have connected fibres and exact leaf guard elimination."
