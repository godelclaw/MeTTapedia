import MettapediaFourColor.StripProtectedEndsGeometry
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripProtectedEnds.safe_exists, [``StripProtectedEnds.Safe]),
    (``StripProtectedEnds.right_iff, [``StripTriangleConsistency.right0]),
    (``StripProtectedEnds.right_release, [``StripProtectedEnds.Family,
      ``StripProtectedEnds.right_iff]),
    (``StripProtectedEnds.left_release, [``StripProtectedEnds.Safe]),
    (``StripProtectedEnds.both_release, [``StripProtectedEnds.left_release,
      ``StripProtectedEnds.right_release]),
    (``StripProtectedEnds.safe_map, [``StripProtectedEnds.Safe]),
    (``StripProtectedEnds.reconstruct, [``StripPartialColouring.partial_valid,
      ``StripProtectedEnds.EndsGraph]),
    (``StripProtectedEnds.word_update, [``StripDiamondPhase.interval_boundary]),
    (``StripProtectedEnds.repair, [``StripProtectedEnds.both_release,
      ``StripProtectedEnds.normalized_update, ``KempeChromogramMatching.recover]),
    (``StripProtectedEnds.compatible, [``StripProtectedEnds.repair, ``GraphTraceAlignment.align]),
    (``StripProtectedEnds.from_reading, [``StripProtectedEnds.compatible,
      ``PatchDisk.Reading.exterior_closed]),
    (``StripProtectedEnds.example_guards, [``StripProtectedEnds.Family,
      ``StripProtectedEnds.Safe]),
    (``StripProtectedEnds.example_repair, [``StripProtectedEnds.repair,
      ``StripProtectedEnds.example_guards])]
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
  logInfo m!"Protected end repair and geometric reconstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
