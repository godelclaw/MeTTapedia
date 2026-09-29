import MettapediaFourColor.DiamondJointRepair
import Lean.Util.FoldConsts

/-!
# Dependency audit of the coupled diamond repair

The boundary law must consume the matching-cover specification. Its graph
instance must consume actual colouring witnesses and exact contract
elimination. The original configuration certificate and global Kempe closure
computation are excluded from every new proof root.
-/

open FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeAnswerComposition.of_answers, [``coversRec_sound, ``KempeCoclosure]),
    (``DiamondBoundaryRepair.normalize, [``trace_map_add, ``trace_map]),
    (``DiamondBoundaryRepair.repair, [``KempeAnswerComposition.of_answers,
      ``DiamondBoundaryRepair.normalize, ``kempeCoclosure_of_map]),
    (``DiamondJointRepair.terminal_realized, [``DiamondJointRepair.assignment_valid,
      ``DiamondJointRepair.coloring_trace, ``DiamondConfigurations.reducibilityTrace004]),
    (``DiamondJointRepair.contract_repair, [``DiamondBoundaryRepair.repair,
      ``DiamondJointContract.contractTrace_iff, ``DiamondJointRepair.terminal_realized]),
    (``DiamondJointRepair.valid_contract, [``contract_ctreeP]),
    (``DiamondJointRepair.reducible, [``DiamondJointRepair.valid_contract,
      ``DiamondJointRepair.contract_repair]),
    (``DiamondJointRepair.compatible_history, [``DiamondJointRepair.contract_repair,
      ``DiamondInsertionGSLT.every_coloring])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.kempeTree, `FourColor.kempeTreeNum, `FourColor.kempeTreeDepth,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
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
        throwError m!"Superseded checker or complete theorem in {root}: {name}"
    if root == ``DiamondBoundaryRepair.repair then
      for name in [``cf004, ``cfmap, ``contractCtree,
          ``DiamondConfigurations.graph004, ``DiamondJointContract.contractTrace_iff] do
        if seen.contains name then
          throwError m!"The abstract boundary law depends on a catalogue instance: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond joint repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    no configuration certificate or global Kempe checker dependencies."
