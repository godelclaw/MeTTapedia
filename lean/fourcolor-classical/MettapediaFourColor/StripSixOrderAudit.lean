import MettapediaFourColor.StripSixOrderExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixDetachment.repair,
      [``KempeComponentDetach.closed_after_swap, ``KempeComponentDetach.active_after_swap,
       ``StripSixDetachment.core_valid, ``StripSourceExtension.complete_valid]),
    (``StripSixOrderExample.planar, [``GraphTriangulationEuler.planar_iff_balance]),
    (``StripSixOrderExample.minimum_degree, [``StripSixOrderExample.degree_eq]),
    (``StripSixOrderExample.initial_form, []),
    (``StripSixOrderExample.missing_colour, []),
    (``StripSixOrderExample.original_joint,
      [``StripSixOrderExample.first_checked, ``StripSixOrderExample.joint_checked]),
    (``StripSixOrderExample.first_normal_form,
      [``KempePhaseBoundary.phase, ``StripSixOrderExample.first_routes]),
    (``StripSixOrderExample.no_two_phases,
      [``StripSixOrderExample.first_normal_form, ``StripSixOrderExample.no_second_phase,
       ``StripSixOrderExample.routes, ``StripSixOrderExample.terminal_empty,
       ``StripResponseSummary.valid_of_colouring]),
    (``StripSixOrderExample.source,
      [``StripSixDetachment.repair, ``StripSixOrderExample.detachment_checked,
       ``StripSixOrderExample.hidden_checked]),
    (``StripSixOrderExample.reconstructed,
      [``StripSixOrderExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripSixOrderExample.core_stars])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripSixPhaseExample, `FourColor.StripSixReleaseExample,
    `FourColor.StripSixBarrierExample, `FourColor.StripStrongAnchorTrap.finalColouring]
  let mut all : NameSet := {}
  for (root, required) in contracts do
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
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-phase order obstruction and silent detachment: {contracts.length} roots; \
    {all.toList.length} declarations."
