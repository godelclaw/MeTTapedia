import MettapediaFourColor.CoreCliqueRepair
import Mettapedia.GraphTheory.FourColor.CliqueFillAudit
import Lean.Util.CollectAxioms

/-! # Audit of count-preserving physical repair through clique attachments -/

open Lean Elab Command SimpleGraph FourColor

run_cmd do
  let env ← getEnv
  let roots := [``KempeCliquePhysicalLift.component_restriction,
    ``KempeCliquePhysicalLift.step_lifts, ``KempeCliquePhysicalLift.history_lifts,
    ``KempeHistoryIso.step, ``KempeHistoryIso.history,
    ``CoreCliqueRepair.repair, ``CoreCliqueRepair.two_steps_optimal,
    ``CoreCliqueRepair.ambient_reconstruction, ``KempeCliqueFill.physical_repair_lifts]
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
      if root == ``CoreCliqueRepair.ambient_reconstruction then
        [``KempeCliquePhysicalLift.component_restriction,
         ``KempeCliquePhysicalLift.history_lifts, ``KempeHistoryIso.history,
         ``CoreProfilePreparedRepair.history,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct,
         ``ThreeBlockGeometry.ExteriorReading.exact_decrease]
      else if root == ``CoreCliqueRepair.two_steps_optimal then
        [``CorePairHistoryObstruction.history_needs_two,
         ``CoreCliqueRepair.repair]
      else if root == ``KempeCliqueFill.physical_repair_lifts then
        [``KempeCliquePhysicalLift.history_lifts, ``KempeCliqueFill.seam_clique,
         ``KempeCliqueFill.attachment]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Clique physical repair: {roots.length} roots; {all.toList.length} declarations."
