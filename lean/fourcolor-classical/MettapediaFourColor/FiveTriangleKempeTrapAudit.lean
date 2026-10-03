import MettapediaFourColor.FiveTriangleKempeTrap
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let generic := [``Mettapedia.GraphTheory.FourColor.KempePaletteRigidity.paletteOrbit_switch,
    ``Mettapedia.GraphTheory.FourColor.KempePaletteRigidity.history_paletteOrbit]
  let concrete := [``FiveTriangleKempeTrap.fan_exact,
    ``FiveTriangleKempeTrap.assignment_proper, ``FiveTriangleKempeTrap.chains_connected,
    ``FiveTriangleKempeTrap.no_history_repairs, ``FiveTriangleKempeTrap.no_kempe_closure_repairs,
    ``FiveTriangleKempeTrap.another_choice_works]
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
    if root == ``FiveTriangleKempeTrap.no_history_repairs then
      for required in [``SimpleGraph.Coloring.swapOnKempeComponent,
        ``Mettapedia.GSLT.Ultrainfinite.Route,
        ``Mettapedia.GraphTheory.FourColor.KempePaletteRigidity.history_paletteOrbit] do
        unless seen.contains required do
          throwError m!"Missing physical-history dependency: {required}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Five-triangle Kempe trap: {generic.length + concrete.length} roots; \
    {all.toList.length} declarations. Unbounded finite histories preserve the \
    palette orbit. Both orientations of one seam fail; another initial choice works. \
    The spherical rotation is separately program-checked."
