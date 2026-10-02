import MettapediaFourColor.ActualWheelOccurrence
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``WheelNeighborhood.neighbor_injective, []),
    (``WheelNeighborhood.covers, []),
    (``WheelNeighborhood.rim_adj_iff, [``WheelNeighborhood.corner_iff]),
    (``D3009Wheel.input, [``NearLinearDiamondData.WellFormed]),
    (``D3009Wheel.hom, [``WheelNeighborhood.corner]),
    (``D3009Wheel.injective, [``WheelNeighborhood.vertex_injective]),
    (``D3009Wheel.degrees, [``WheelNeighborhood.neighbor_injective]),
    (``D3009Boundary.outer_seam, [``FacialStarCompletion.across_edge]),
    (``D3009Boundary.hom, [``D3009Boundary.outer_seam]),
    (``D3009Boundary.full_turn, [``D3009Boundary.row_agrees]),
    (``D3009Boundary.star_covers, [``FacialStarCompletion.covers]),
    (``D3009Boundary.ring_outside_core, [``D3009Boundary.around_injective]),
    (``D3009Boundary.boundary_injective,
      [``D3009Boundary.owner_not_adj_next, ``D3009Boundary.center_not_adj_boundary]),
    (``D3009Boundary.vertex_injective, [``D3009Boundary.boundary_injective]),
    (``ActualWheelOccurrence.occurrence,
      [``D3009Boundary.hom, ``D3009Boundary.full_turn, ``D3009Boundary.vertex_injective,
       ``D3009Wheel.degrees, ``WheelNeighborhood.rim_adj_iff,
       ``MinimalExceptionalEmbedding.triangle_facial, ``ExceptionalCoreInduced.four_cycle_chord]),
    (``ActualWheelOccurrence.residual_occurrence,
      [``ActualWheelOccurrence.occurrence, ``ExactFanResidual.alternatives,
       ``Bulk.Cfg006.hpairs])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate]
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
      let permitted := root == ``ActualWheelOccurrence.residual_occurrence &&
        (`FourColor.Bulk.Cfg006).isPrefixOf name
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Wheel occurrence: {roots.length} roots; {all.toList.length} declarations. \
    Actual degree observations construct every source vertex, edge and interior turn. \
    Triangle and four-cycle laws prove full injectivity. No wheel repair is assumed. \
    Only the residual supply consumer retains configuration 7 and the shared profile."
