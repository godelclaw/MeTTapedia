import MettapediaFourColor.DiamondEarFamily
import Lean.Util.FoldConsts

/-!
# Audit of diamond repair through ear contexts

Check the chord surgery, exact graph semantics, route reconstruction and
strict vertex descent. The diamond consumers must use the actual core
repairs. No extra reference certificate or complete colouring theorem may
enter their dependency closures.
-/

open FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeBoundaryMerge.match_merge, [``matchg_gramFlip, ``matchg_gramNeg]),
    (``KempeBoundaryMerge.closed, [``KempeBoundaryMerge.match_merge]),
    (``KempeBoundaryMerge.coclosure_expand, [``KempeBoundaryMerge.closed]),
    (``BoundaryEarRepair.trace_exact, [``BoundaryEarRepair.extend,
      ``BoundaryEarRepair.restrict, ``BoundaryEarRepair.ear]),
    (``BoundaryEarRepair.repair, [``BoundaryEarRepair.trace_exact,
      ``KempeBoundaryMerge.coclosure_expand]),
    (``BoundaryEarGSLT.repair_with_history, [``BoundaryEarGSLT.recover,
      ``BoundaryEarGSLT.repair, ``BoundaryEarGSLT.semantics,
      ``Mettapedia.GSLT.RelationalRouteSemantics.Semantics.Witness]),
    (``BoundaryEarGSLT.strict, [``BoundaryEarGSLT.size, ``BoundaryEarRepair.size]),
    (``DiamondEarFamily.base, [``DiamondSplitRepair.base_repair,
      ``DiamondSplitRepair.transferred_repair, ``DiamondJointRepair.contract_repair,
      ``DiamondConfigurations.reducibilityTrace001,
      ``DiamondConfigurations.reducibilityTrace002,
      ``DiamondConfigurations.reducibilityTrace004]),
    (``DiamondEarFamily.input_inhabited, [``DiamondEarFamily.seed_inhabited,
      ``BoundaryEarGSLT.input_inhabited]),
    (``DiamondEarFamily.repair, [``DiamondEarFamily.base, ``BoundaryEarGSLT.repair]),
    (``DiamondEarFamily.compatible_history, [``BoundaryEarGSLT.repair_with_history]),
    (``DiamondEarFamily.arbitrary_size, [``BoundaryEarGSLT.size,
      ``BoundaryEarGSLT.iterate_length])]
  let forbidden : List Name := [`FourColor.Bulk.Cfg000, `FourColor.Bulk.Cfg003,
    `FourColor.kempeTree, `FourColor.kempeTreeNum, `FourColor.kempeTreeDepth,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
  let generic : List Name := [`FourColor.KempeBoundaryMerge,
    `FourColor.BoundaryEarRepair, `FourColor.BoundaryEarGSLT]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Superseded certificate or complete theorem in {root}: {name}"
      if (`FourColor.Bulk).isPrefixOf name &&
          name.toString.startsWith "FourColor.Bulk.Cfg" &&
          !(`FourColor.Bulk.Cfg001).isPrefixOf name then
        throwError m!"Additional configuration certificate in {root}: {name}"
      if generic.any (·.isPrefixOf root) &&
          ([`FourColor.Bulk, `FourColor.DiamondConfigurations].any (·.isPrefixOf name) ||
            name == ``cfmap) then
        throwError m!"The general context law uses a catalogue instance: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond ear families: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    one contextual law, three core consumers, no additional certificate replacement."
