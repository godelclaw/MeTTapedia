import Mettapedia.GraphTheory.Kempe.PairBlocks
import Mettapedia.GraphTheory.FourColor.HiddenTriangleObstruction
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempePairBlocks.fibre_path, [``KempeTwoVertexFibre.fibre_path]),
    (``KempePairBlocks.fibres, [``KempePairBlocks.fibre_path]),
    (``KempePairBlocks.transition_iff, [``KempeGuardedLift.Transition, ``KempePairBlocks.LocalTransition]),
    (``KempePairBlocks.step_iff, [``KempePairBlocks.transition_iff]),
    (``KempePairBlocks.history_iff, [``KempePairBlocks.fibres,
      ``KempePairBlocks.step_iff, ``KempeGuardedLift.history_iff]),
    (``HiddenTriangleObstruction.same_retained, [``AdjacentHiddenObstruction.same_boundary]),
    (``HiddenTriangleObstruction.not_fibres, [``AdjacentHiddenObstruction.no_lift]),
    (``HiddenTriangleObstruction.guarded_stutter_does_not_lift,
      [``HiddenTriangleObstruction.same_retained, ``AdjacentHiddenObstruction.no_lift])]
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
  logInfo m!"Hidden pair blocks: {contracts.length} roots; {all.toList.length} declarations. \
    Guards factor over arbitrarily many hidden pairs, including shared retained neighbours. \
    An interacting hidden triangle can already have disconnected fibres."
