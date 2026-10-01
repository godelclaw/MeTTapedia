import MettapediaFourColor.FlatNeighborhoodCoverage
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``LocalCoverageAssembly.ball_recenter, [``SimpleGraph.edist_triangle]),
    (``LocalCoverageAssembly.OnBall.recenter, [``LocalCoverageAssembly.ball_recenter]),
    (``LocalCoverageAssembly.Occurs.recenter, [``LocalCoverageAssembly.ball_recenter]),
    (``LocalCoverageAssembly.eight_of_overlap,
      [``LocalCoverageAssembly.EightOverlapSupply.classify,
       ``LocalCoverageAssembly.EightOverlapSupply.next,
       ``LocalCoverageAssembly.EightOverlapSupply.close,
       ``LocalCoverageAssembly.Occurs.recenter]),
    (``LocalCoverageAssembly.localSupply_of_overlap,
      [``LocalCoverageAssembly.eight_of_overlap]),
    (``LocalCoverageAssembly.seven_or_eight,
      [``LocalCoverageAssembly.LocalSupply.seven,
       ``LocalCoverageAssembly.LocalSupply.eight,
       ``LocalCoverageAssembly.Occurs.recenter]),
    (``LocalCoverageAssembly.radius_twelve,
      [``LocalCoverageAssembly.LocalSupply.low, ``LocalCoverageAssembly.seven_or_eight]),
    (``FlatNeighborhoodCoverage.radius_twelve_outcome,
      [``LocalCoverageAssembly.radius_twelve]),
    (``FlatNeighborhoodCoverage.residual_in_minimal,
      [``FlatNeighborhoodCoverage.radius_twelve_outcome,
       ``OverlappingPentagonalSectors.not_in_minimal]),
    (``FlatNeighborhoodCoverage.residual_in_minimal_from_overlap,
      [``LocalCoverageAssembly.eight_of_overlap,
       ``LocalCoverageAssembly.radius_twelve,
       ``OverlappingPentagonalSectors.not_in_minimal]),
    (``FlatNeighborhoodCoverage.not_in_minimal_of_coverage,
      [``FlatNeighborhoodCoverage.residual_in_minimal])]
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
  logInfo m!"Conditional flat coverage: {roots.length} roots; {all.toList.length} declarations; \
    explicit supply hypotheses, no complete theorem or original catalogue rank certificate."
