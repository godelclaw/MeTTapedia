import MettapediaFourColor.StripSixSamePairExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripSixSamePair.core_valid, []),
    (``StripSixSamePair.repair,
      [``Coloring.exists_kempeComponentSet_eq_of_bicoloredSet_eq,
       ``StripSixSamePair.core_valid, ``StripSourceExtension.complete_valid]),
    (``StripSixSamePairExample.guard,
      [``StripSixSamePairExample.checked]),
    (``StripSixSamePairExample.repaired,
      [``StripSixSamePair.repair, ``StripSixSamePairExample.guard,
       ``StripSixOrderExample.missing_colour]),
    (``StripSixSamePairExample.reconstructed,
      [``StripSixSamePairExample.repaired, ``PatchBoundaryGluing.reconstruct,
       ``StripSixOrderExample.core_stars]),
    (``StripSixOrderExample.no_two_phases,
      [``StripSixOrderExample.first_normal_form, ``StripSixOrderExample.no_second_phase])]
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
    `FourColor.StripSixOrderExample.reconstructed]
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
  logInfo m!"Single-pair repair and fixed-order obstruction: {contracts.length} roots; \
    {all.toList.length} declarations."
