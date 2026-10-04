import MettapediaFourColor.TriangleStripLists
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let roots := [``ColoringListPropagation.forest_colouring,
    ``ColoringListPropagation.anchored_colouring,
    ``ColoringListPropagation.run_subset,
    ``ColoringListPropagation.extension_iff_nonempty,
    ``TriangleStripLists.anchor_cover, ``TriangleStripLists.pin_pinned,
    ``TriangleStripLists.source_iff, ``TriangleStripLists.sweeps_edges,
    ``TriangleStripLists.guard_colouring, ``TriangleStripLists.occurrence_extension]
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
    if root == ``TriangleStripLists.occurrence_extension then
      for needed in [``TriangleStripAnchors.source_forest,
          ``ColoringListPropagation.forest_colouring,
          ``ColoringListPropagation.run_sound,
          ``KempeGuardedLift.glue_restrict] do
        unless seen.contains needed do
          throwError m!"Missing reconstruction dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Joint anchor reconstruction: {roots.length} roots; {all.toList.length} declarations."
