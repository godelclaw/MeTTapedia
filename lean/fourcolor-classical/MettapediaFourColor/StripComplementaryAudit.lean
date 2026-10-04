import MettapediaFourColor.StripComplementaryExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripComplementaryGeometry.no_crossing,
      [``Mettapedia.GraphTheory.FourColor.PrimalPathSeparation.labels_eq_of_disjoint_walk]),
    (``StripComplementaryGeometry.complementary_separation,
      [``StripComplementaryGeometry.no_crossing]),
    (``StripComplementaryRepair.core01_valid, []),
    (``StripComplementaryRepair.core23_valid, []),
    (``StripComplementaryRepair.repair01,
      [``StripComplementaryRepair.core01_valid, ``SimpleGraph.Coloring.swapOnKempeComponent,
       ``StripSourceExtension.complete_valid]),
    (``StripComplementaryRepair.repair23,
      [``StripComplementaryRepair.core23_valid, ``SimpleGraph.Coloring.swapOnKempeComponent,
       ``StripSourceExtension.complete_valid]),
    (``StripComplementaryGeometry.repair,
      [``StripComplementaryGeometry.complementary_separation,
       ``StripComplementaryRepair.repair01, ``StripComplementaryRepair.repair23]),
    (``StripComplementaryExample.ear_sides, []),
    (``StripComplementaryExample.both_branches,
      [``StripComplementaryExample.chain_checked]),
    (``StripComplementaryExample.source,
      [``StripComplementaryGeometry.repair, ``StripComplementaryExample.ear_sides,
       ``StripSixMixedExample.planar, ``GraphSphericalEuler.balance]),
    (``StripComplementaryExample.reconstructed,
      [``StripComplementaryExample.source, ``PatchBoundaryGluing.reconstruct,
       ``StripSixMixedExample.core_stars])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripSixMixedExample.source, `FourColor.StripSixMixedExample.reconstructed,
    `FourColor.StripSixSamePair.repair, `FourColor.StripSixOrderExample.source]
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
  logInfo m!"Complementary geometric repair: {contracts.length} roots; \
    {all.toList.length} declarations."
