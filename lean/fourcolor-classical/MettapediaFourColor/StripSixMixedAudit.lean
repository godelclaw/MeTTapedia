import MettapediaFourColor.StripSixMixedExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixMixedExample.planar, [``GraphTriangulationEuler.planar_iff_balance]),
    (``StripSixMixedExample.minimum_degree, [``StripSixMixedExample.degree_eq]),
    (``StripSixMixedExample.no_five_run, [``StripSixMixedExample.no_five_run_check]),
    (``StripSixMixedExample.core_stars, []),
    (``StripSixMixedExample.original_joint,
      [``StripSixMixedExample.first_checked, ``StripSixMixedExample.joint_checked]),
    (``StripSixMixedExample.missing_colour, []),
    (``StripSixMixedExample.same_pair_blocked, []),
    (``StripSixMixedExample.no_two_phases,
      [``StripSixMixedExample.first_normal_form, ``StripSixMixedExample.no_second_phase,
       ``KempePhaseBoundary.phase, ``StripSixMixedExample.terminal_empty]),
    (``StripSixMixedExample.no_single_pair_phase,
      [``KempePairHistory.pointwise, ``KempePhaseBoundary.endpoint,
       ``StripSixMixedExample.pair_routes, ``StripSixMixedExample.pair_empty,
       ``StripResponseSummary.valid_of_colouring]),
    (``StripSixMixedExample.source,
      [``KempeNeighborRelease.history, ``KempeNeighborRelease.singleton_closed,
       ``StripSixMixedExample.exits, ``StripSixMixedExample.no_entry,
       ``StripSourceExtension.complete_valid]),
    (``StripSixMixedExample.reconstructed,
      [``StripSixMixedExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripSixMixedExample.core_stars])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripSixPhaseExample, `FourColor.StripSixReleaseExample,
    `FourColor.StripSixBarrierExample, `FourColor.StripStrongAnchorTrap.finalColouring,
    `FourColor.StripSixDetachment.repair, `FourColor.StripSixOrderExample.source,
    `FourColor.StripSixOrderExample.reconstructed,
    `FourColor.StripSixSamePair.repair, `FourColor.StripSixSamePairExample]
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
  logInfo m!"Mixed-pair obstruction and neighbour release: {contracts.length} roots; \
    {all.toList.length} declarations."
