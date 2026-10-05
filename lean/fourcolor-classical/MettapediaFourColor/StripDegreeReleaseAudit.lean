import MettapediaFourColor.StripDegreeReleaseExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripDegreeRelease.exterior_degree_lt, []),
    (``StripDegreeRelease.unique_one_neighbour, []),
    (``StripDegreeRelease.core_valid, []),
    (``StripDegreeRelease.repair,
      [``StripDegreeRelease.unique_one_neighbour, ``StripDegreeRelease.core_valid,
       ``KempeNeighborRelease.second, ``KempeNeighborRelease.history]),
    (``StripDegreeReleaseExample.exterior_degree,
      [``StripDegreeRelease.exterior_degree_lt]),
    (``StripDegreeReleaseExample.common_corner, []),
    (``StripDegreeReleaseExample.reconstructed,
      [``StripDegreeRelease.repair, ``StripDegreeReleaseExample.exterior_degree,
       ``StripDegreeReleaseExample.common_corner, ``StripSixMixedExample.assemble]),
    (``StripDegreeReleaseExample.saved_reconstruction,
      [``StripDegreeReleaseExample.reconstructed, ``StripSixMixedExample.original_joint])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripSixMixedExample.source, `FourColor.StripSixMixedExample.reconstructed,
    `FourColor.StripSixMixedExample.exits, `FourColor.StripSixMixedExample.no_entry,
    `FourColor.StripSixMixedExample.second, `FourColor.StripSixSamePair.repair]
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
  logInfo m!"Degree-bounded release: {contracts.length} roots; {all.toList.length} declarations."
