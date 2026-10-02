import MettapediaFourColor.SecondFanWheelOccurrence
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``WheelBoundaryCompletion.outer_seam, [``FacialStarCompletion.across_edge]),
    (``WheelBoundaryCompletion.row_agrees, [``WheelBoundaryCompletion.outer_seam]),
    (``WheelBoundaryCompletion.boundary_injective,
      [``WheelBoundaryCompletion.owner_not_adj_next,
       ``WheelBoundaryCompletion.center_not_adj_boundary]),
    (``WheelBoundaryCompletion.complete,
      [``WheelBoundaryCompletion.vertex_injective, ``WheelBoundaryCompletion.full_turn]),
    (``D3009BoundaryLayout.layout, []),
    (``WheelBoundaryLayouts.twoFive, []),
    (``ActualWheelOccurrence.occurrence, [``WheelBoundaryCompletion.complete]),
    (``TwoFiveWheelOccurrence.reading, [``D3009Wheel.hom, ``D3009Wheel.face]),
    (``TwoFiveWheelOccurrence.occurrence,
      [``WheelBoundaryCompletion.complete, ``MinimalExceptionalEmbedding.triangle_facial,
       ``ExceptionalCoreInduced.four_cycle_chord]),
    (``TwoFiveWheelOccurrence.supplied,
      [``TwoFiveWheelOccurrence.occurrence, ``WheelNeighborhood.covers]),
    (``SecondFanWheelOccurrence.alternatives,
      [``ActualSecondFanResidual.profile_alternatives,
       ``TwoFiveWheelOccurrence.supplied, ``ActualWheelOccurrence.occurrence])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.Bulk.Cfg, `FourColor.Bulk.Hyb]
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
      if forbidden.any (·.isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Wheel completion: {roots.length} roots; {all.toList.length} declarations. \
    One shared geometric proof completes both the original thirteen-port source \
    and all six twelve-port targets. The actual second-fan classifier retains \
    the centre and both fives and supplies complete injective occurrences. \
    No wheel repair, configuration certificate or complete Four Colour endpoint is used."
