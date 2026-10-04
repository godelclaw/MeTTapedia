import MettapediaFourColor.CoreProfilePreparedRepair
import Lean.Util.CollectAxioms

/-! # Dependency audit of the physical core-profile counterexample -/

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``CoreProfileSwitchGeometry.reading, ``CoreProfileSwitchGeometry.planar,
    ``CoreProfileSwitchGeometry.exteriorIso, ``CoreProfileSwitchObstruction.profile_source,
    ``CoreProfileSwitchObstruction.same_profile, ``CoreProfileSwitchObstruction.same_joint_relation,
    ``CoreProfileSwitchObstruction.extension_iff_relation,
    ``CoreProfileSwitchObstruction.initial_nonextension,
    ``CoreProfileSwitchObstruction.actual_component, ``CoreProfileSwitchObstruction.physical_step,
    ``CoreProfileSwitchObstruction.switched_word, ``CoreProfileSwitchObstruction.first_extends,
    ``CoreProfileSwitchObstruction.second_nonextension, ``CoreProfileSwitchObstruction.no_profile_update,
    ``CoreProfileSwitchObstruction.no_profile_prediction,
    ``CoreProfileSwitchObstruction.no_deterministic_quotient, ``CoreProfileSwitchObstruction.planar_counterexample,
    ``CoreProfilePreparedRepair.actual_component, ``CoreProfilePreparedRepair.prepared,
    ``CoreProfilePreparedRepair.history, ``CoreProfilePreparedRepair.reconstruction]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.ThreeBlockRepairTransfer, `FourColor.ThreeBlockRepairTransferData]
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
    let required :=
      if root == ``CoreProfileSwitchObstruction.actual_component then
        [``SimpleGraph.Coloring.kempeComponentSet_subset_of_closed,
         ``SimpleGraph.Coloring.mem_kempeComponentSet_of_adj]
      else if root == ``CoreProfileSwitchObstruction.no_profile_prediction then
        [``CoreProfileSwitchObstruction.same_profile, ``CoreProfileSwitchObstruction.actual_component,
         ``CoreProfileSwitchObstruction.switched_word, ``CoreProfileSwitchObstruction.first_extends,
         ``CoreProfileSwitchObstruction.second_nonextension]
      else if root == ``CoreProfileSwitchObstruction.no_deterministic_quotient then
        [``Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors,
         ``Mettapedia.GraphTheory.FourColor.KempeBoundaryObservation.rootedSwitch,
         ``CoreProfileSwitchObstruction.same_profile, ``CoreProfileSwitchObstruction.actual_component]
      else if root == ``CoreProfileSwitchObstruction.planar_counterexample then
        [``CoreProfileSwitchGeometry.planar, ``CoreProfileSwitchGeometry.reading,
         ``CoreProfileSwitchGeometry.exteriorIso, ``CoreProfileSwitchObstruction.same_profile,
         ``CoreProfileSwitchObstruction.physical_step, ``CoreProfileSwitchObstruction.actual_component,
         ``CoreProfileSwitchObstruction.first_extends, ``CoreProfileSwitchObstruction.second_nonextension]
      else if root == ``CoreProfilePreparedRepair.reconstruction then
        [``CoreProfilePreparedRepair.actual_component, ``CoreProfilePreparedRepair.prepared,
         ``CoreProfilePreparedRepair.history, ``CoreProfileSwitchObstruction.repaired,
         ``CoreProfileSwitchObstruction.switched_word,
         ``Mettapedia.GraphTheory.FourColor.KempeChainCertificate.Step]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Physical core-profile obstruction: {roots.length} roots; {all.toList.length} declarations."
