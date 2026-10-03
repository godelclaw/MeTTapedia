import Mettapedia.GraphTheory.FourColor.ComponentDetachExample
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Lean.Util.CollectAxioms

/-!
# Component detachment: route consumer and dependency audit

Both successful repairs retain actual physical component witnesses in the
existing GSLT route type. Their middle switches consume the general
detachment theorem. The spherical census and bounded failed strategy are
separate program evidence.
-/

namespace SimpleGraph.KempeDetachExample

theorem gslt_history (i : Fin 2) : Nonempty
    (Mettapedia.GraphTheory.FourColor.KempeChainCertificate.History
      (state 0) (state (stage i 3))) :=
  Mettapedia.GraphTheory.FourColor.KempeChainCertificate.nonempty_history_iff.mpr
    (physical_history i)

end SimpleGraph.KempeDetachExample

open Lean Elab Command SimpleGraph
run_cmd do
  let env ← getEnv
  let roots := [``KempeComponentDetach.closed_after_swap,
    ``KempeComponentDetach.active_after_swap, ``KempeDetachExample.proper_edges,
    ``KempeDetachExample.connected, ``KempeDetachExample.old_exits,
    ``KempeDetachExample.no_entry, ``KempeDetachExample.detached_closed,
    ``KempeDetachExample.silent_history, ``KempeDetachExample.physical_history,
    ``KempeDetachExample.completed_edges, ``KempeDetachExample.include_injective,
    ``KempeDetachExample.exterior_adj, ``KempeDetachExample.reconstructed,
    ``KempeDetachExample.repair_and_reconstruct, ``KempeDetachExample.gslt_history]
  let consumers := [``KempeDetachExample.detached_closed,
    ``KempeDetachExample.silent_history, ``KempeDetachExample.physical_history,
    ``KempeDetachExample.repair_and_reconstruct, ``KempeDetachExample.gslt_history]
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
      unless seen.contains ``KempeComponentDetach.closed_after_swap do
        throwError m!"Missing general detachment theorem in {root}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Component detachment: {roots.length} roots; {all.toList.length} declarations."
