import Mettapedia.GraphTheory.Kempe.EarGuard
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``BinaryConstraints.ear_iff, ``BinaryConstraints.separate_ports_not_joint]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor]
  let mut all : NameSet := {}
  for root in roots do
    let mut todo := [root]
    let mut seen : NameSet := {}
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
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Ear constraints: {roots.length} roots; {all.toList.length} declarations. \
    Joint binary elimination preserves witnesses; independent marginals can lose them."
