import MettapediaFourColor.Sector7Coverage
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let closure := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    return seen
  let old := closure ``FourColor.exclude7
  let fresh := closure ``Sector7Coverage.exclude7
  for root in [``Sector7Region.step, ``Sector7Coverage.exclude7] do
    for ax in (← liftCoreM <| collectAxioms root) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError m!"Unexpected axiom {ax} in {root}"
  for i in List.range 7 do
    let name := Name.str `FourColor.Sector7Region s!"m{i}"
    unless fresh.contains name do
      throwError m!"Missing shared spoke bound: {name}"
  for name in [``FourColor.exclude7, ``FourColor.s7_step5880,
      ``FourColor.s7_step5882, ``FourColor.s7_step5919, ``FourColor.s7_step5937,
      ``FourColor.s7_step5941, ``FourColor.s7_step6044, ``FourColor.s7_step6045,
      ``FourColor.s7_step6046] do
    if fresh.contains name then
      throwError m!"Old ancestor remains: {name}"
  for name in fresh.toList do
    if (`FourColor.CompositionalComplete).isPrefixOf name ||
        (`FourColor.fourColorTheorem).isPrefixOf name ||
        name.toString.startsWith "FourColor.Bulk." then
      throwError m!"Unexpected complete endpoint or reducibility certificate: {name}"
  let checks := fun (names : NameSet) => names.toList.filter fun n =>
    n.getPrefix == `FourColor && n.toString.startsWith "FourColor.c7_"
  let fits := fun (names : NameSet) => names.toList.filter fun n =>
    n.getPrefix == `FourColor && n.toString.startsWith "FourColor.f7_"
  let removed := (checks old).filter fun n => !fresh.contains n
  let added := (checks fresh).filter fun n => !old.contains n
  let removedFits := (fits old).filter fun n => !fresh.contains n
  unless added.isEmpty do
    throwError m!"New original check dependencies: {added}"
  unless removed.length == 112 && removedFits.length == 16 do
    throwError m!"Unexpected replacement counts: {removed.length} checks, {removedFits.length} fits"
  logInfo m!"Degree-seven original member checks: {(checks old).length} -> \
    {(checks fresh).length}; seven shared regional checks added."
  logInfo m!"Removed original member checks ({removed.length}): {removed}"
  logInfo m!"Removed original hubcap fits ({removedFits.length}): {removedFits}"
  logInfo m!"Sector coverage audit passed: the rebuilt degree-seven endpoint \
    consumes all seven shared bounds and no superseded ancestor. \
    Catalogue soundness remains an explicit input."
