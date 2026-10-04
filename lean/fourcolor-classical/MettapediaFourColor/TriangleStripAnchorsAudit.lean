import MettapediaFourColor.TriangleStripAnchors
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let roots := [``TriangleStripAnchors.input0099, ``TriangleStripAnchors.rank_injective,
    ``TriangleStripAnchors.colour_proper, ``TriangleStripAnchors.later_clique,
    ``TriangleStripAnchors.two_anchors, ``TriangleStripAnchors.source_forest,
    ``TriangleStripAnchors.repair_contract, ``TriangleStripAnchors.same_observations]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
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
    if root == ``TriangleStripAnchors.repair_contract ||
        root == ``TriangleStripAnchors.same_observations then
      for needed in [``TriangleStripAnchors.later_clique,
          ``TriangleStripAnchors.colour_proper, ``KempeTriangleAnchors.occurrence_forest,
          ``KempeForestFibre.list_connected, ``Coloring.avoiding_of_pointwise_swap] do
        unless seen.contains needed do
          throwError m!"Missing structural repair dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Decoded strip anchors: {roots.length} roots; {all.toList.length} declarations."
