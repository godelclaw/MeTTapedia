import MettapediaFourColor.NearLinearFiveGSLT
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List Name := [
    ``BoundaryTriangleRepair.reconstruct, ``BoundaryTriangleRepair.repair,
    ``NearLinearFiveData.input0370, ``NearLinearFiveData.input0464,
    ``NearLinearFiveData.input0465, ``NearLinearFiveData.input0604,
    ``NearLinearFiveData.input3202,
    ``NearLinearFiveData.stars_exact0370, ``NearLinearFiveData.stars_exact0464,
    ``NearLinearFiveData.stars_exact0465, ``NearLinearFiveData.stars_exact0604,
    ``NearLinearFiveData.stars_exact3202,
    ``NearLinearFiveData.degree_source0370, ``NearLinearFiveData.degree_source0464,
    ``NearLinearFiveData.degree_source0465, ``NearLinearFiveData.degree_source0604,
    ``NearLinearFiveData.degree_source3202,
    ``NearLinearFiveData.boundary_source0370, ``NearLinearFiveData.boundary_source0464,
    ``NearLinearFiveData.boundary_source0465, ``NearLinearFiveData.boundary_source0604,
    ``NearLinearFiveData.boundary_source3202,
    ``NearLinearFiveData.boundary0370_0464, ``NearLinearFiveData.boundary0370_0465,
    ``NearLinearFiveData.boundary0464_0604, ``NearLinearFiveData.boundary0465_0604,
    ``NearLinearFiveData.boundary3202_0604,
    ``NearLinearFiveData.numbered225, ``NearLinearFiveData.faces225,
    ``NearLinearFiveData.rotation225, ``NearLinearFiveData.reducibilityTrace225,
    ``NearLinearFiveData.rotation0370_0464, ``NearLinearFiveData.rotation0370_0465,
    ``NearLinearFiveData.rotation0464_0604, ``NearLinearFiveData.rotation0465_0604,
    ``NearLinearFiveData.rotation3202_0604, ``NearLinearFiveData.retained_square,
    ``NearLinearFiveBase.coverage_mask, ``NearLinearFiveBase.reference_repair,
    ``NearLinearFiveRepair.repair0604, ``NearLinearFiveRepair.repair0464,
    ``NearLinearFiveRepair.repair0465, ``NearLinearFiveRepair.repair3202,
    ``NearLinearFiveRepair.repair0370, ``NearLinearFiveRepair.repair0370_alternative,
    ``NearLinearFiveGSLT.presentation,
    ``NearLinearFiveGSLT.transport_retained, ``NearLinearFiveGSLT.coloring_square,
    ``NearLinearFiveGSLT.left_history, ``NearLinearFiveGSLT.right_history,
    ``NearLinearFiveGSLT.compatible_histories]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducible_block_0]
  let mut all : NameSet := {}
  for root in roots do
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
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Complete theorem in family repair {root}: {name}"
      if (name.toString.startsWith "FourColor.Bulk.Cfg" &&
          !(`FourColor.Bulk.Cfg224).isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Independent configuration certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  for name in [``BoundaryTriangleRepair.reconstruct, ``KempeBoundarySplit.repairs_collapse,
      ``NearLinearFiveBase.coverage_mask, ``Bulk.Cfg224.hpairs,
      ``NearLinearFiveData.numbered225, ``NearLinearFiveGSLT.semantics,
      ``NearLinearFiveGSLT.coloring_square] do
    unless all.contains name do
      throwError m!"Missing family dependency: {name}"
  logInfo m!"Five-entry family: {roots.length} roots; {all.toList.length} declarations; \
    only configuration 225 supplies a rank certificate."
