import MettapediaFourColor.PortPreparationObstructionExample
import Lean.Util.CollectAxioms

/-! # Dependency audit of the failed preparation and its alternative -/

open Lean Elab Command
open FourColor.PortPreparationObstruction
run_cmd do
  let env ← getEnv
  let roots := [``no_extension, ``phase_word, ``no_tail_phase,
    ``Example.proper_edges, ``Example.connected, ``Example.closed_edges,
    ``Example.component_iff, ``Example.physical_step, ``Example.preparing_component_ports,
    ``Example.joiningPath_active, ``Example.failed_preparation,
    ``Example.source_edges, ``Example.failed_whole_preparation, ``Example.alternative_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData]
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
    let required :=
      if root == ``no_tail_phase then
        [``no_extension, ``SimpleGraph.KempePairHistory.pointwise]
      else if root == ``Example.failed_whole_preparation then
        [``no_tail_phase, ``Example.prepared_boundary, ``Example.source_edges,
         ``Example.source_boundary]
      else if root == ``Example.preparing_component_ports then
        [``Example.component_iff, ``Example.preparing_ports]
      else if root == ``Example.alternative_repair then
        [``Example.physical_step, ``Example.closed_edges, ``Example.connected,
         ``Example.completed_edges, ``Example.completed_agrees]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Preparation obstruction and alternative: {roots.length} roots; {all.toList.length} declarations."
