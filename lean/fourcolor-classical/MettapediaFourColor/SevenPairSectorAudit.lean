import MettapediaFourColor.SevenPairSector
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``SevenPairSectorData.witness_sound, []),
    (``SevenPairSectorData.blocked_valid, []),
    (``SevenPairSector.Reading.path, [``SevenPairSector.Reading.step]),
    (``SevenPairSector.outgoing_only,
      [``RuleMatcher.candidate_eq, ``SevenPairSectorData.blocked_valid,
       ``SevenPairSector.Reading.path]),
    (``SevenPairSector.outgoing_le_one, [``SevenPairSector.outgoing_only]),
    (``SevenPairSector.incoming_two, [``SevenPairSector.Reading.occurrence]),
    (``SevenPairSector.positive,
      [``SevenPairSector.outgoing_le_one, ``SevenPairSector.incoming_two,
       ``SevenPairSector.rim_injective]),
    (``SevenPairSector.flat_has_high, [``SevenPairSector.positive]),
    (``ActualSevenPairSector.first_nonadjacent,
      [``MinimalExceptionalEmbedding.triangle_facial]),
    (``ActualSevenPairSector.further_high,
      [``SevenPairSector.flat_has_high, ``ActualSevenPairSector.first_nonadjacent]),
    (``ActualSevenPairSector.pair_continuation,
      [``ActualSevenPairSector.further_high, ``LocalCoverageAssembly.ball_recenter])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.DiamondProfileData,
    `FourColor.Bulk.Cfg, `FourColor.Bulk.Hyb]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) ||
          name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Shared seven-pair sector: {roots.length} roots; {all.toList.length} declarations. \
    The specified facial degree profile and flatness force a further high vertex \
    within radius two of the second centre. No catalogue rank or complete theorem is used. \
    Classification into this profile and broader geometric coverage remain open."
