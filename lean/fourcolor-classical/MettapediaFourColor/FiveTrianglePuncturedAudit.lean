import MettapediaFourColor.FiveTrianglePuncturedRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let generic := [``Mettapedia.GraphTheory.FourColor.OrderedFanKempe.advance,
    ``Mettapedia.GraphTheory.FourColor.OrderedFanKempe.reachable,
    ``Mettapedia.GraphTheory.FourColor.OrderedFanKempe.history]
  let concrete := [``FiveTrianglePuncturedRepair.exterior_exact,
    ``FiveTrianglePuncturedRepair.every_exterior_reconstructs,
    ``FiveTrianglePuncturedRepair.trapped_exterior_repairs,
    ``FiveTrianglePuncturedRepair.no_whole_source_lift,
    ``FiveTrianglePuncturedRepair.not_minimum_degree_five]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`FourColor.Bulk, `FourColor.fourColorTheorem,
    `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.DiamondProfileData, `Lean.ofReduceBool]
  let mut all : NameSet := {}
  for root in generic ++ concrete do
    let mut seen : NameSet := {}
    let mut todo := [root]
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
    if concrete.contains root then
      unless seen.contains ``NearLinearDiamondData.Input.graph do
        throwError m!"Missing actual-graph dependency in {root}"
    if root == ``FiveTrianglePuncturedRepair.every_exterior_reconstructs then
      for required in [``SimpleGraph.Coloring.swapOnKempeComponent,
        ``Mettapedia.GSLT.Ultrainfinite.Route,
        ``Mettapedia.GraphTheory.FourColor.OrderedFanKempe.reachable] do
        unless seen.contains required do
          throwError m!"Missing uniform physical-repair dependency: {required}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Punctured five-triangle repair: {generic.length + concrete.length} roots; \
    {all.toList.length} declarations. One fan law covers all lengths and all \
    proper starting states. The concrete repair retains the entire fan; \
    arbitrary-exterior repair and geometric coverage remain open."
