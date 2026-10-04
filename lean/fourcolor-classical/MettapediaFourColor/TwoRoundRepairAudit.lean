import MettapediaFourColor.StripTwoRoundRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

run_cmd do
  let env ← getEnv
  let roots := [``KempeFiniteDecoder.mem_parses,
    ``StripTwoRoundRepair.mates_valid, ``StripTwoRoundRepair.five_parses,
    ``StripTwoRoundRepair.decode_check, ``StripTwoRoundRepair.decode,
    ``StripTwoRoundRepair.majority_coclosure, ``StripTwoRoundRepair.proper,
    ``StripTwoRoundRepair.answers, ``StripTwoRoundRepair.source_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeAnchorProjection.signatures, `FourColor.KempeIntervalMatching,
    `FourColor.StripIntervalRepair.rejection, `FourColor.StripIntervalRepair.source_repair]
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
    if root == ``StripTwoRoundRepair.source_repair then
      for needed in [``exists_adjacent_majority, ``KempeFiniteDecoder.mem_parses,
          ``StripTwoRoundRepair.decode_check, ``StripTwoRoundRepair.mates_valid,
          ``StripTwoRoundRepair.majority_coclosure, ``StripMajorityRepair.source_repair,
          ``KempeChordExchange.answer_exists, ``StripTwoRoundRepair.answers,
          ``StripTwoRoundRepair.proper, ``TriangleStripAnchors.input0099,
          ``KempeCoclosure] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-round repair: {roots.length} roots; {all.toList.length} declarations."
