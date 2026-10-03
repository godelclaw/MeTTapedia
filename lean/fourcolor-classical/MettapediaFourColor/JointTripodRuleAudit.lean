import MettapediaFourColor.JointTripodRuleExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let geometric : List (Name × List Name) := [
    (``JointTripodRuleSupply.unit_amounts, []),
    (``JointTripodRuleSupply.corner, []),
    (``JointTripodRuleSupply.reading, [``FourTriangleFaces.reading]),
    (``JointTripodRuleSupply.degrees, [``JointTripodRuleSupply.reading]),
    (``JointTripodRuleExample.observations, [``RuleMatcher.check_iff]),
    (``JointTripodRuleExample.degrees, [``JointTripodRuleSupply.degrees]),
    (``JointTripodRuleExample.core_images, []),
    (``JointTripodRuleExample.occurrence,
      [``JointTripodRuleExample.reading, ``FourTriangleCompletedOccurrence.occurrence,
       ``FacialBoundaryScheme.hom])]
  let repair : List (Name × List Name) := [
    (``ActualJointTripodRuleSupply.not_readings,
      [``JointTripodRuleSupply.reading, ``ActualFourTrianglePatch.not_in_minimal,
       ``ActualDualContract.singleton_colorable, ``FourTriangleRepair.reference_repair,
       ``InjectiveEmbeddedRepair.colorable]),
    (``ActualJointTripodRuleSupply.not_checks,
      [``ActualJointTripodRuleSupply.not_readings, ``RuleMatcher.check_iff]),
    (``ActualJointTripodRuleSupply.joint_units_le_two,
      [``ActualJointTripodRuleSupply.not_checks]),
    (``ActualJointTripodRuleSupply.joint_transfer_le_two,
      [``ActualJointTripodRuleSupply.joint_units_le_two, ``JointTripodRuleSupply.unit_amounts])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.DiamondProfileData,
    ``Bulk.Cfg032.hctr, ``Bulk.Cfg036.hctr]
  let mut all : NameSet := {}
  for (root, required) in geometric ++ repair do
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
      let permitted := repair.any (fun r => r.1 == root) &&
        ((`FourColor.Bulk.Cfg032).isPrefixOf name || (`FourColor.Bulk.Cfg036).isPrefixOf name)
      if forbidden.any (·.isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" && !permitted) ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Joint tripod rule supply: {geometric.length + repair.length} roots; \
    {all.toList.length} declarations. Three compatible source matches reconstruct \
    the tripod; their joint contribution is at most two in a minimal map. \
    The finite example constructs its full boundary from the same readings. \
    Repair retains Cfg032/Cfg036; geometric roots use no rank certificates. \
    Universal joint classification and catalogue compression remain open."
