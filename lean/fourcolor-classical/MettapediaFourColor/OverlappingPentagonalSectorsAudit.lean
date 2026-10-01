import MettapediaFourColor.OverlappingPentagonalSectors
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OverlappingPentagonalSectors.roots_consecutive, []),
    (``OverlappingPentagonalSectors.outer_dart_eq, []),
    (``OverlappingPentagonalSectors.observe_outer_eq,
      [``OverlappingPentagonalSectors.outer_dart_eq]),
    (``OverlappingPentagonalSectors.outer_size_iff,
      [``OverlappingPentagonalSectors.outer_dart_eq]),
    (``OverlappingPentagonalSectors.six_cycle_positions_differ, []),
    (``OverlappingPentagonalSectors.face_pattern,
      [``OverlappingPentagonalSectors.outer_size_iff]),
    (``OverlappingPentagonalSectors.recognized,
      [``OverlappingPentagonalSectors.face_pattern,
       ``PentagonalDiamondPatch.Tangle.FaceReduction.recognized]),
    (``OverlappingPentagonalSectors.strict_reduction,
      [``OverlappingPentagonalSectors.face_pattern,
       ``PentagonalDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern]),
    (``OverlappingPentagonalSectors.not_in_minimal,
      [``OverlappingPentagonalSectors.face_pattern,
       ``PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      ])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Complete theorem or original catalogue certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Pentagonal overlap: {roots.length} roots; {all.toList.length} declarations; \
    no complete theorem or original catalogue rank certificate."
