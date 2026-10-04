import Mettapedia.GraphTheory.Kempe.TriangleStripWidth
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``KempeTriangleAnchors.acyclic_of_unique_later,
    ``KempeTriangleAnchors.delete_class_acyclic, ``KempeTriangleAnchors.hidden_forest,
    ``KempeTriangleAnchors.history_iff, ``KempeTriangleAnchors.occurrence_forest,
    ``KempeTriangleAnchors.occurrence_history_iff,
    ``KempeTriangleStripWidth.forest, ``KempeTriangleStripWidth.anchors_required]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : NameSet := {}
  for root in roots do
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
    if root == ``KempeTriangleAnchors.history_iff ||
        root == ``KempeTriangleAnchors.occurrence_history_iff then
      for needed in [``KempeForestFibre.list_connected,
          ``KempeGuardedLift.history_iff, ``Coloring.avoiding_of_pointwise_swap] do
        unless seen.contains needed do
          throwError m!"Missing physical reconstruction in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Triangle anchors: {roots.length} roots; {all.toList.length} declarations."
