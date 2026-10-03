import MettapediaFourColor.ThreeBlockCore
import Mettapedia.GraphTheory.FourColor.CascadingDetachAudit
import Lean.Util.CollectAxioms

/-!
# The three-run core law consumes the actual cascading repair

The exterior history is inherited from `CascadingDetach`. The new core
witness is constructed by the three-choice law, with literal agreement
on all eleven source ports. The planar crosscut interpretation remains
separate from this kernel-checked source and history consumer.
-/

namespace FourColor.ThreeBlockCore

open SimpleGraph SimpleGraph.KempeDetachExample SimpleGraph.KempeCascadingDetach
open FiveTriangleCollapseObstruction

def palette : Fin 4 → Color := ![.c0,.c1,.c2,.c3]

theorem observed_initial : ∀ j : Fin 11,
    palette (KempeDetachExample.state 0 (ports.get j)) = word false false false j := by
  decide +kernel

theorem observed_final : ∀ j : Fin 11,
    palette (KempeCascadingDetach.after 2 (ports.get j)) = word false false true j := by
  decide +kernel

/-- The initial boundary fails by the same general compatibility law. -/
theorem initial_rejects (k : upper.graph.Coloring Color)
    (hk : ∀ j : Fin 11, k (j.castAdd 7) =
      palette (KempeDetachExample.state 0 (ports.get j))) : False := by
  have h := necessary false false false k (fun j => (hk j).trans (observed_initial j))
  exact h.2 rfl

/-- A physical preparation and switch now feed symbolic source reconstruction. -/
theorem physical_source_repair :
    ∃ D : graph.Coloring (Fin 4), D ∈ graph.KempeClosure (KempeDetachExample.state 0) ∧
      ∃ k : upper.graph.Coloring Color,
        ∀ j : Fin 11, k (j.castAdd 7) = palette (D (ports.get j)) := by
  refine ⟨KempeCascadingDetach.after 2, KempeCascadingDetach.physical_history,
    colouring false false true rfl (by decide), ?_⟩
  intro j
  exact (colouring_boundary false false true rfl (by decide) j).trans (observed_final j).symm

end FourColor.ThreeBlockCore

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := [``FourColor.ThreeBlockCore.necessary,
    ``FourColor.ThreeBlockCore.assignment_proper,
    ``FourColor.ThreeBlockCore.extension_iff,
    ``FourColor.ThreeBlockCore.component_choices_iff,
    ``FourColor.ThreeBlockCore.observed_initial,
    ``FourColor.ThreeBlockCore.observed_final,
    ``FourColor.ThreeBlockCore.initial_rejects,
    ``FourColor.ThreeBlockCore.physical_source_repair]
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
    if root == ``FourColor.ThreeBlockCore.physical_source_repair then
      for needed in [``FourColor.ThreeBlockCore.assignment_proper,
          ``SimpleGraph.KempeComponentDetach.closed_after_swap] do
        unless seen.contains needed do
          throwError m!"Missing consumer dependency: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Three-block core: {roots.length} roots; {all.toList.length} declarations."
