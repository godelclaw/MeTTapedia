import MettapediaFourColor.CapRechoice
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``CapRechoice.cap_choice_changes, [``CapRechoice.forced_choice, ``CapRechoice.freed_choices]),
    (``CapRechoice.prefixColouring, [``CapRechoice.prefix_valid, ``TriangleStripAnchors.input0099]),
    (``CapRechoice.no_fixed_prefix_extension, [``TriangleStripAnchors.input0099]),
    (``CapRechoice.no_initial_extension, [``CapRechoice.forced_choice]),
    (``CapRechoice.repaired, [``StripSourceExtension.colouring, ``CapRechoice.repairedCore]),
    (``CapRechoice.same_matching_update, [``KempeIntervalRepair.switch_matches,
      ``KempeMatchingChromogram.reconstruct]),
    (``CapRechoice.visible_boundary_insufficient, [``CapRechoice.no_initial_extension,
      ``CapRechoice.same_visible_boundary, ``CapRechoice.repaired_outer])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.ResidualSeedRepairData, `FourColor.DiamondProfileData]
  let mut all : NameSet := {}
  for (root, required) in contracts do
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
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Cap witness rechoice: {contracts.length} roots; {all.toList.length} declarations."
