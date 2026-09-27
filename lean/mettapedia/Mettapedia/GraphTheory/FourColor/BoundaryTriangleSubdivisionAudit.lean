import Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
import Lean.Util.FoldConsts

/-!
# Audit of the boundary-triangle colouring transport

The roots connect the actual graph operation to a colouring equivalence,
its counting consequence, and compatible witnesses along GSLT routes.
This does not audit a configuration-reducibility or planarity theorem.
-/

open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
open Mettapedia.GSLT.RelationalRouteSemantics

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``Operational.presentation, [``Operational.theory, ``Operational.Step]),
    (``coloringEquiv, [``extend, ``restrict, ``fourth_ne, ``fourth_unique]),
    (``coloring_card, [``coloringEquiv, ``Nat.card_congr]),
    (``extend_boundary, [``extend]),
    (``Operational.liftRoute_retained, [``Operational.liftRoute,
      ``Operational.retainedRoute, ``Operational.transport, ``extend,
      ``Operational.transport_retained, ``Semantics.Witness])]
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
  logInfo m!"Boundary-triangle semantics: {contracts.length} roots; \
    {inspected.toList.length} declarations in their combined dependency closure."
