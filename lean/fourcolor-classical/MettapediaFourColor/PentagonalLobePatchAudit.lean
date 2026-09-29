import MettapediaFourColor.PentagonalLobePatch
import Lean.Util.FoldConsts

/-!
# Audit of pentagonal lobe boundary repair

The repair must consume actual graph-colouring witnesses and the proved
chromogram-cover specification. It must not consume a configuration certificate,
a complete Four Colour theorem, or the diamond family's reducibility proofs.
-/

open FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PentagonalLobePatch.boundary_repair,
      [``KempeAnswerComposition.of_answers, ``coversRec_sound,
        ``kempeCoclosure_of_map]),
    (``PentagonalLobePatch.terminal_supported,
      [``PentagonalLobePatch.colouring, ``PentagonalLobePatch.graph,
        ``PentagonalLobePatch.assignment, ``PentagonalLobePatch.terminalCodes]),
    (``PentagonalLobePatch.repair,
      [``PentagonalLobePatch.boundary_repair, ``PentagonalLobePatch.terminal_supported]),
    (``PentagonalLobePatch.compatible_colouring,
      [``PentagonalLobePatch.repair, ``PentagonalLobePatch.colouring,
        ``PentagonalLobePatch.graph])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondConfigurations, `FourColor.DiamondFamilyReducibility,
    `FourColor.DiamondProfileReducibility]
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
        throwError m!"Configuration certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Pentagonal lobe patch: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
