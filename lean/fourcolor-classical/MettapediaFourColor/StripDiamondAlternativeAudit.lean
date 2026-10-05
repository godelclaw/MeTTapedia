import MettapediaFourColor.StripDiamondAlternativeExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripDiamondAlternative.source_observations, []),
    (``StripDiamondAlternative.Reading.next_degree,
      [``StripDiamondAlternative.source_observations]),
    (``StripDiamondAlternative.Reading.previous_degree,
      [``StripDiamondAlternative.source_observations]),
    (``StripDiamondAlternative.Reading.alternatives,
      [``StripDiamondAlternative.Reading.next_degree,
       ``StripDiamondAlternative.Reading.previous_degree]),
    (``StripDiamondAlternative.not_low_port,
      [``StripDiamondAlternative.Reading.alternatives,
       ``ActualRuleFanSupply.degree_five,
       ``ActualRulePairDiamond.pentagonal_face_pattern,
       ``ActualRulePairDiamond.face_pattern,
       ``PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern,
       ``MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern]),
    (``StripDiamondAlternative.surviving_degree,
      [``StripDiamondAlternative.not_low_port]),
    (``StripDiamondAlternativeExample.port_six, []),
    (``StripDiamondAlternativeExample.mixed,
      [``StripDiamondAlternative.Reading.alternatives,
       ``StripDiamondAlternativeExample.port_six])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  -- The established diamond reductions retain their joint profile certificate
  -- and generic trace indexing, but no original configuration rank certificate.
  let forbidden := [`sorryAx, `Lean.ofReduceBool,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.ResidualSeedRepairCertificate]
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
        if forbidden.any (·.isPrefixOf name) ||
            name.toString.startsWith "FourColor.Bulk.Cfg" ||
            name.toString.startsWith "FourColor.Bulk.Hyb" then
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
  logInfo m!"Strip diamond alternative: {contracts.length} roots; {all.toList.length} declarations."
