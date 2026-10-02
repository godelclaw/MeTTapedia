import MettapediaFourColor.ExceptionalConstructionRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ExceptionalConstruction.reference, [``ExecutableConfiguration.evaluate_eq]),
    (``ExceptionalConstruction.numbered_eq, []),
    (``ExceptionalConstruction.source_graph, []),
    (``ExceptionalConstruction.source_rotation, []),
    (``ExceptionalConstruction.source_boundary, []),
    (``ExceptionalConstruction.compiled_query, []),
    (``ExceptionalConstruction.ringTrace_iff,
      [``ExceptionalConstruction.numbered_eq, ``ExceptionalConstruction.source_graph,
       ``ConfigurationFaceGraph.Presentation.ringTrace_iff]),
    (``ExceptionalConstruction.embeddable, [``embeddable_cfquiz]),
    (``KempeRepairContract.reducible_of_repair,
      [``KempeRepairContract.contract_trace_proper]),
    (``ExceptionalConstructionRepair.repair,
      [``ExceptionalRepairCertificate.repair, ``ExceptionalConstruction.ringTrace_iff]),
    (``ExceptionalConstructionRepair.reducible,
      [``KempeRepairContract.reducible_of_repair, ``ExceptionalConstructionRepair.repair]),
    (``ExceptionalConstructionRepair.contract_endpoints, []),
    (``ExceptionalConstructionRepair.valid_contract,
      [``KempeRepairContract.valid_singleton]),
    (``ExceptionalConstructionRepair.singleton_reducible,
      [``ExceptionalConstructionRepair.valid_contract, ``ExceptionalConstructionRepair.reducible]),
    (``ExceptionalConstructionRepair.colorable_of_contract,
      [``ExceptionalConstructionRepair.reducible, ``Hypermap.embed_closure,
       ``Hypermap.colorable_of_contractColoring]),
    (``ExceptionalConstructionRepair.not_preembedding,
      [``Hypermap.not_embed_reducible, ``ExceptionalConstructionRepair.singleton_reducible]),
    (``ExceptionalConstructionRepair.not_fitted,
      [``Hypermap.quiz_preembedding, ``valid_cfquiz,
       ``ExceptionalConstructionRepair.not_preembedding])]
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
  logInfo m!"Exceptional source construction: {roots.length} roots; \
    {all.toList.length} declarations; exact permutations, source graph, cyclic stars, \
    ordered boundary traces and source embeddability. Actual preembedding remains open."
