import MettapediaFourColor.ExceptionalQueryReading
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualGraphQuery.stepR, []),
    (``DualGraphQuery.stepL, []),
    (``DualGraphQuery.arity_eq_degree, []),
    (``ExceptionalQueryReading.source_walk, []),
    (``ExceptionalQueryReading.source_vertices, [``ExceptionalQueryReading.source_walk]),
    (``ExceptionalQueryReading.walk,
      [``ExceptionalCoreOrientation.joint_preserves_turns,
       ``DualGraphQuery.stepR, ``DualGraphQuery.stepL]),
    (``ExceptionalQueryReading.fitted,
      [``ExceptionalQueryReading.walk, ``DualGraphQuery.arity_eq_degree]),
    (``ExceptionalQueryReading.actual_fitted,
      [``ExceptionalQueryReading.fitted, ``MinimalExceptionalEmbedding.triangular,
       ``MinimalExceptionalEmbedding.cyclic]),
    (``ExceptionalQueryReading.not_minimal,
      [``ExceptionalQueryReading.fitted, ``ExceptionalConstructionRepair.not_fitted])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Complete theorem or original catalogue certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exceptional actual query: {roots.length} roots; \
    {all.toList.length} declarations; source walk, actual core corners and degrees, \
    compiled query fit and exclusion under reference minimality."
