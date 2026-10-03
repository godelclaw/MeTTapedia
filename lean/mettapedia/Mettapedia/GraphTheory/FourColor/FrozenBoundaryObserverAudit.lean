import Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph
open Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``KempeStepAvoiding.recolor_path, [``Coloring.avoiding_of_pointwise_swap]),
    (``kempe_path_recolor, [``KempeStepAvoiding.recolor_path]),
    (``fixed, [``kempe_path_comp,
      ``Mettapedia.GraphTheory.FourColor.AdjacentHiddenObstruction.frozen]),
    (``no_lift, [``fixed]),
    (``no_lift_renamed, [``no_lift, ``kempe_path_recolor])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.CompositionalComplete, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData]
  let mut all : NameSet := {}
  for (root, required) in contracts do
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
    for requiredName in required do
      unless seen.contains requiredName do
        throwError m!"Missing physical or semantic dependency in {root}: {requiredName}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Frozen boundary observer: {contracts.length} roots; {all.toList.length} declarations. \
    A graph homomorphism with a protected frozen observation obstructs all physical histories. \
    Palette renaming is included in the certified contract."
