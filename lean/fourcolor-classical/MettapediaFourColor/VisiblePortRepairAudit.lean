import MettapediaFourColor.VisiblePortRepair
import Lean.Util.CollectAxioms

/-!
# Audit of boundary anchoring and its visible repair

The obstruction must consume both the anchored-component coverage and the
symbolic source law. The alternative must consume a real component switch
and a checked source assignment. Whole-map reconstruction is parameterized
by the exact embedded source and exterior readings.
-/

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``Coloring.mem_component_along_chain, ``Coloring.isTransparent_of_chains,
    ``Coloring.IsTransparent.eq_of_boundary_fixed_history,
    ``AnchoredBoundaryExample.proper_edges, ``AnchoredBoundaryExample.connected,
    ``AnchoredBoundaryExample.active, ``AnchoredBoundaryExample.anchors,
    ``AnchoredBoundaryExample.covers, ``AnchoredBoundaryExample.frozen,
    ``AnchoredBoundaryExample.boundary_fixed_history,
    ``AnchoredBoundaryExample.physical_repair, ``AnchoredBoundaryExample.component_iff,
    ``AnchoredBoundaryExample.repair_support_size,
    ``FourColor.VisiblePortRepair.assignment_proper,
    ``FourColor.VisiblePortRepair.isolated_of_two_exclusions,
    ``FourColor.VisiblePortRepair.whole_repair_of_isolated_port,
    ``FourColor.VisiblePortRepair.whole_repair_or_residual,
    ``FourColor.VisiblePortRepair.Example.phase_global,
    ``FourColor.VisiblePortRepair.Example.no_silent_then_tail_phase,
    ``FourColor.VisiblePortRepair.Example.visible_repair]
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
      if root == ``FourColor.VisiblePortRepair.Example.no_silent_then_tail_phase then
        [``AnchoredBoundaryExample.frozen, ``Coloring.isTransparent_of_chains,
         ``KempePairHistory.pointwise, ``FourColor.ThreeBlockCore.necessary]
      else if root == ``FourColor.VisiblePortRepair.Example.visible_repair then
        [``AnchoredBoundaryExample.component_iff, ``FourColor.VisiblePortRepair.assignment_proper]
      else if root == ``FourColor.VisiblePortRepair.whole_repair_of_isolated_port then
        [``FourColor.ThreeBlockGeometry.ExteriorReading.reconstruct,
         ``FourColor.VisiblePortRepair.assignment_proper,
         ``FourColor.VisiblePortRepair.repair_of_isolated_port]
      else if root == ``FourColor.VisiblePortRepair.whole_repair_or_residual then
        [``FourColor.ThreeBlockGeometry.ExteriorReading.whole_repair_of_path,
         ``FourColor.VisiblePortRepair.whole_repair_of_isolated_port]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Anchored boundary and visible repair: {roots.length} roots; {all.toList.length} declarations."
