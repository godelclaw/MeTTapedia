import Mettapedia.GraphTheory.Kempe.BridgeGuard
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``BinaryConstraints.bridge_iff,
    ``KempeForestGuard.transition_bridge_iff, ``KempeForestGuard.repair_of_bridge]
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
    if root == ``KempeForestGuard.repair_of_bridge then
      for required in [``BinaryConstraints.bridge_iff, ``KempeForestGuard.transition_iff,
          ``KempeForestFibre.list_connected, ``KempeGuardedLift.glue,
          ``Coloring.avoiding_of_pointwise_swap] do
        unless seen.contains required do
          throwError m!"Missing port reconstruction or physical lifting: {required}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Bridge guards: {roots.length} roots; {all.toList.length} declarations. \
    Joint port choices construct a target colouring and an actual protected repair."
