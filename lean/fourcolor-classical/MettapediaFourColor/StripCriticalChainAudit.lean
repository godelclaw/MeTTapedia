import MettapediaFourColor.StripCriticalChain
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripCriticalChain.forced_path, []),
    (``StripCriticalChain.no_core, [``StripCriticalChain.forced_path,
      ``StripCriticalChain.path_allowed, ``StripCriticalChain.path_edges]),
    (``StripCriticalChain.punctured_joins, [``StripPuncturedExtension.r5]),
    (``StripCriticalChain.every_proper_core, [``StripPuncturedExtension.terminal_iff]),
    (``StripCriticalChain.every_proper_source, [``StripPartialColouring.partial_valid]),
    (``StripCriticalChain.no_source, [``StripResponseSummary.valid_of_colouring]),
    (``StripCriticalChain.local_extension_not_sufficient,
      [``StripCriticalChain.every_proper_source, ``StripCriticalChain.no_source])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData]
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
  logInfo m!"Critical chain: {contracts.length} roots; {all.toList.length} declarations."
