import MettapediaFourColor.StripCriticalRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

run_cmd do
  let env ← getEnv
  let roots := [``KempeChromogramMatching.pair_unique,
    ``KempeChromogramMatching.mate_involutive, ``KempeChromogramMatching.mate_noncrossing,
    ``KempeChromogramMatching.pair_switch, ``KempeChromogramMatching.recover,
    ``KempeChromogramMatching.majority_coclosure,
    ``StripCriticalRepair.coordinates, ``StripCriticalRepair.order,
    ``StripCriticalRepair.direct_pairs, ``StripCriticalRepair.source_repair,
    ``StripSymbolicRepair.majority_coclosure, ``StripSymbolicRepair.guarded_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeIntervalMatching, `FourColor.KempeFiniteDecoder,
    `FourColor.StripIntervalRepair.data, `FourColor.StripIntervalRepair.proper,
    `FourColor.StripIntervalRepair.source_repair, `FourColor.StripTwoRoundRepair.data,
    `FourColor.StripTwoRoundRepair.proper, `FourColor.StripTwoRoundRepair.source_repair,
    `FourColor.StripSymbolicRepair.decode_check, `FourColor.StripSymbolicRepair.mate,
    `FourColor.StripSymbolicRepair.mates_valid]
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
    if root == ``StripCriticalRepair.source_repair ||
        root == ``StripSymbolicRepair.guarded_repair then
      for needed in [``KempeChromogramMatching.recover,
          ``KempeChromogramMatching.majority_coclosure, ``exists_adjacent_majority,
          ``chordsAux, ``chords_disjoint, ``chords_nonCrossing, ``matchg_flip,
          ``StripSourceExtension.complete_valid, ``StripResponseSummary.terminal_iff,
          ``TriangleStripAnchors.input0099, ``KempeCoclosure] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Uniform chromogram bridge: {roots.length} roots; {all.toList.length} declarations."
