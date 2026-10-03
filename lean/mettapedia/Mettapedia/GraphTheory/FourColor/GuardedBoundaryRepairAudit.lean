import Mettapedia.GraphTheory.FourColor.GuardedBoundaryRepair
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeGuardedLift.lift, [``Coloring.avoiding_of_pointwise_swap, ``KempeGuardedLift.glue]),
    (``KempeGuardedLift.fibration, [``KempeGuardedLift.lift]),
    (``KempeGuardedLift.projects, [``KempeGuardedLift.Step, ``KempeGuardedLift.Fits]),
    (``KempeGuardedLift.history_iff, [``KempeGuardedLift.fibration, ``KempeGuardedLift.projects]),
    (``KempeGuardedLift.two_vertex_fibres, [``KempeTwoVertexFibre.fibre_path]),
    (``KempeGuardedLift.two_vertex_history_iff,
      [``KempeGuardedLift.two_vertex_fibres, ``KempeGuardedLift.history_iff]),
    (``GuardedBoundaryRepair.blocked_step, [``KempeGuardedLift.lift, ``AdjacentHiddenObstruction.no_lift]),
    (``GuardedBoundaryRepair.blocked_history,
      [``KempeGuardedLift.two_vertex_history_iff, ``AdjacentHiddenObstruction.no_lift]),
    (``GuardedBoundaryRepair.repaired_guarded_history,
      [``KempeGuardedLift.projects, ``AdjacentHiddenObstruction.repaired])]
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
  logInfo m!"Guarded boundary repair: {contracts.length} roots; {all.toList.length} declarations. \
    Joint before/after assignments give exact history transport across two hidden vertices. \
    Connected fibres are proved, and both obstructed and repaired commands have consumers."
