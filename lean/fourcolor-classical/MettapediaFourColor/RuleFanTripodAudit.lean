import MettapediaFourColor.RuleFanTripodSupply
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let geometric : List (Name × List Name) := [
    (``FourTriangleFaces.edge_in_face, []),
    (``FourTriangleFaces.reading, [``FourTriangleFaces.edge_in_face]),
    (``RuleFanTripodSupply.reading, [``FourTriangleFaces.reading]),
    (``RuleFanTripodSupply.degrees, [``RuleFanTripodSupply.reading]),
    (``RuleFanTripodSupply.tip_adjacent, [``RuleFanCharge.walk_corner]),
    (``ActualRuleFanTripodSupply.tip_support, [``RuleFanTripodSupply.tip_adjacent])]
  let repair : List (Name × List Name) := [
    (``ActualRuleFanTripodSupply.not_five,
      [``ActualFourTrianglePatch.not_in_minimal, ``RuleFanTripodSupply.reading,
       ``RuleFanTripodSupply.degrees, ``ActualDualContract.singleton_colorable,
       ``FourTriangleRepair.reference_repair, ``InjectiveEmbeddedRepair.colorable]),
    (``ActualRuleFanTripodSupply.tip_lower, [``ActualRuleFanTripodSupply.not_five]),
    (``ActualRuleFanTripodSupply.unique_tip, [``ActualRuleFanTripodSupply.tip_lower]),
    (``ActualRuleFanTripodSupply.unique_tip_of_other_six,
      [``ActualRuleFanTripodSupply.unique_tip])]
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
  logInfo m!"Shared fan tripod closing: {geometric.length + repair.length} roots; \
    {all.toList.length} declarations. Both placements retain the same seam tip. \
    A five supplies actual strict reconstruction; in a unique-high-neighbour pair \
    the tip is six or the same second centre. Cfg032/Cfg036 remain in the repair \
    dispatcher; no rank certificates occur in the geometric roots. \
    The full joint flat-pair classification remains open."
