import MettapediaFourColor.CorePairHistoryObstruction
import Lean.Util.CollectAxioms

/-! # Audit of the source obstruction to fixed-pair repair phases -/

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``CorePairChangeObstruction.no_pair_change,
    ``CorePairHistoryObstruction.no_fixed_pair_extension,
    ``CorePairHistoryObstruction.no_single_step_extension,
    ``CorePairHistoryObstruction.history_needs_two,
    ``CorePairHistoryObstruction.ambient_history_needs_two,
    ``CorePairHistoryObstruction.two_steps_optimal,
    ``CorePairHistoryObstruction.optimal_reconstruction]
  let sourceRoots := roots.take 5
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.ThreeBlockRepairTransfer, `FourColor.ThreeBlockRepairTransferData,
    `FourColor.PairPhaseCore, `FourColor.TwoStepCoreProgress]
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
        if sourceRoots.contains root &&
            ([`FourColor.CoreProfileSwitchGeometry, `FourColor.CoreProfilePreparedRepair].any
              (·.isPrefixOf name)) then
          throwError m!"Concrete exterior dependency in universal source root {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``CorePairHistoryObstruction.no_fixed_pair_extension then
        [``CorePairChangeObstruction.no_pair_change, ``SimpleGraph.KempePairHistory.pointwise]
      else if root == ``CorePairHistoryObstruction.optimal_reconstruction then
        [``CorePairHistoryObstruction.ambient_history_needs_two,
         ``CorePairHistoryObstruction.no_fixed_pair_extension,
         ``CoreProfilePreparedRepair.reconstruction, ``CoreProfilePreparedRepair.history,
         ``CoreProfilePreparedRepair.actual_component,
         ``CoreProfileSwitchObstruction.repaired]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Source fixed-pair history obstruction: {roots.length} roots; {all.toList.length} declarations."
