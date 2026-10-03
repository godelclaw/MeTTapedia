import Mettapedia.GraphTheory.FourColor.CascadingDetach
import Lean.Util.CollectAxioms

/-!
# Audit of the two-stage detachment consumer

The final component must depend on the proved singleton detachment and
the general law. Both newly available components are derived from old
exits, rather than independently checked for saturation after the switch.
-/

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``KempeCascadingDetach.proper_edges, ``KempeCascadingDetach.active,
    ``KempeCascadingDetach.connected, ``KempeCascadingDetach.first_closed_edges,
    ``KempeCascadingDetach.old_exits, ``KempeCascadingDetach.no_entry,
    ``KempeCascadingDetach.singleton_detached, ``KempeCascadingDetach.final_detached,
    ``KempeCascadingDetach.silent_history, ``KempeCascadingDetach.physical_history,
    ``KempeCascadingDetach.preparation_size, ``KempeCascadingDetach.complete_edges,
    ``KempeCascadingDetach.reconstructed, ``KempeCascadingDetach.repair_and_reconstruct,
    ``KempeCascadingDetach.gslt_history]
  let consumers := [``KempeCascadingDetach.final_detached,
    ``KempeCascadingDetach.silent_history, ``KempeCascadingDetach.physical_history,
    ``KempeCascadingDetach.repair_and_reconstruct, ``KempeCascadingDetach.gslt_history]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData]
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
    if consumers.contains root then
      unless seen.contains ``KempeCascadingDetach.singleton_detached &&
          seen.contains ``KempeComponentDetach.closed_after_swap do
        throwError m!"Missing composed detachment argument in {root}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Cascading detachment: {roots.length} roots; {all.toList.length} declarations."
