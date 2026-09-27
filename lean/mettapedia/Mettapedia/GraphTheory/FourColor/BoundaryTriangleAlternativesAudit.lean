import Mettapedia.GraphTheory.FourColor.BoundaryTriangleAlternatives
import Lean.Util.FoldConsts

/-!
# Audit of the complete boundary-triangle colouring alternatives

The roots cover the equal-endpoint branch, the full witness equivalence,
contextual compatibility and counting. No reducibility theorem is asserted.
-/

open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``equalColoringEquiv, [``contractColoring, ``contracted, ``SimpleGraph.map,
      ``expandEqual, ``selectEqual, ``collapse_eq_iff]),
    (``alternativesEquiv, [``coloringEquiv, ``equalColoringEquiv, ``Equiv.sumCompl]),
    (``compatible_iff, [``alternativesEquiv, ``extend, ``expandEqual]),
    (``alternatives_card, [``alternativesEquiv, ``equalChoiceEquiv, ``freshEquiv,
      ``Nat.card_congr])]
  let mut inspected : NameSet := {}
  for (root, required) in contracts do
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
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Complete boundary-triangle alternatives: {contracts.length} roots; \
    {inspected.toList.length} declarations in their combined dependency closure."
