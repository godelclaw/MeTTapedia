import MettapediaFourColor.SevenPairSectorRecognition
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FacialChainClosure.extend_corner, []),
    (``FacialChainClosure.close, [``FacialStarCompletion.pow_degree]),
    (``SevenPairSectorRecognition.develop,
      [``FacialChainClosure.extend_corner, ``FacialChainClosure.close]),
    (``SevenPairSectorRecognition.complete, [``FacialChainClosure.close]),
    (``SevenPairSectorRecognition.complete_profile, []),
    (``SevenPairSectorRecognition.check_iff, []),
    (``ActualSevenPairRecognition.seed, [``SevenPairSectorRecognition.develop]),
    (``ActualSevenPairRecognition.continuation,
      [``ActualSevenPairRecognition.seed, ``SevenPairSectorRecognition.complete,
       ``ActualSevenPairSector.pair_continuation]),
    (``ActualSevenPairRecognition.checked_continuation,
      [``ActualSevenPairRecognition.continuation, ``SevenPairSectorRecognition.check_iff])]
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
  logInfo m!"Constructive seven-pair recognition: {roots.length} roots; \
    {all.toList.length} declarations. Rooted triangle attachment and degree closure \
    construct every facial observation. The actual pair consumes only a degree test. \
    No catalogue rank or complete theorem is used. Supply of a matching degree profile \
    and universal coverage remain open."
