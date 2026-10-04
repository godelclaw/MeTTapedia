import MettapediaFourColor.StripIntervalRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeIntervalMatching.possible_of_matching,
    ``KempeIntervalMatching.successful_chord, ``KempeIntervalRepair.gram_switch,
    ``KempeIntervalRepair.switch_matches, ``KempeIntervalRepair.answer,
    ``StripIntervalRepair.proper, ``StripIntervalRepair.rejection,
    ``StripIntervalRepair.answers, ``StripIntervalRepair.alternatives_valid,
    ``StripIntervalRepair.no_fixed_anchor, ``StripIntervalRepair.crossing_obstruction,
    ``StripIntervalRepair.source_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeAnchorProjection.signatures]
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
    if root == ``StripIntervalRepair.source_repair then
      for needed in [``KempeIntervalMatching.possible_of_matching,
          ``KempeIntervalRepair.gram_switch, ``KempeMatchingChromogram.reconstruct,
          ``StripIntervalRepair.rejection, ``StripIntervalRepair.answers,
          ``StripIntervalRepair.proper, ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Adaptive interval repair: {roots.length} roots; {all.toList.length} declarations."
