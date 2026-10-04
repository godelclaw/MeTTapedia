import MettapediaFourColor.StripExteriorFanExample
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripExteriorFan.neighbour_path,
      [``FacialStarCompletion.covers, ``ExceptionalOverlap.consecutive_adjacent]),
    (``StripExteriorFan.bichromatic_path, [``StripExteriorFan.neighbour_path]),
    (``StripExteriorFan.no_independent_change,
      [``StripExteriorFan.bichromatic_path, ``KempeRouteProjection.changed_along_walk]),
    (``StripExteriorFan.no_preparation,
      [``StripExteriorFan.no_independent_change, ``KempePairHistory.pointwise]),
    (``StripExteriorFanExample.interior_block, []),
    (``StripExteriorFanExample.complete, []),
    (``StripExteriorFanExample.forced_path,
      [``StripExteriorFan.bichromatic_path, ``StripExteriorFanExample.interior_block,
       ``StripExteriorFanExample.complete, ``StripSixMixedExample.triangular,
       ``StripSixMixedExample.cyclic, ``StripSixMixedExample.missing_colour]),
    (``StripExteriorFanExample.no_preparation, [``StripExteriorFan.no_preparation])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.StripSixMixedExample.source, `FourColor.StripSixMixedExample.reconstructed,
    `FourColor.StripSixMixedExample.pair_routes, `FourColor.StripSixMixedExample.no_single_pair_phase,
    `FourColor.StripSixMixedExample.no_two_phases, `FourColor.StripComplementaryGeometry.repair]
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
  logInfo m!"Exterior fan: {contracts.length} roots; {all.toList.length} declarations."
