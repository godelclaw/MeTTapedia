import MettapediaFourColor.TwoPortCoreObstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor SimpleGraph

run_cmd do
  let env ← getEnv
  let roots := [``TwoPortCoreElimination.stages_valid,
    ``TwoPortCoreElimination.next_active, ``TwoPortCoreElimination.terminal_edge,
    ``TwoPortCoreElimination.stage_elimination,
    ``TwoPortCoreObstruction.upper_marginal_passes,
    ``TwoPortCoreObstruction.lower_marginal_passes,
    ``TwoPortCoreObstruction.upper_no_extension,
    ``TwoPortCoreObstruction.lower_no_extension]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.DiamondProfileData]
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
    unless root == ``TwoPortCoreElimination.next_active ||
        seen.contains ``NearLinearDiamondData.Input.graph do
      throwError m!"Missing decoded source graph in {root}"
    if root == ``TwoPortCoreElimination.stage_elimination then
      unless seen.contains ``BinaryConstraints.ear_iff do
        throwError "Missing shared two-port reconstruction law"
    if root == ``TwoPortCoreObstruction.upper_no_extension ||
        root == ``TwoPortCoreObstruction.lower_no_extension then
      unless seen.contains ``BinaryConstraints.separate_ports_not_joint do
        throwError "Missing common-witness obstruction"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-port cores: {roots.length} roots; {all.toList.length} declarations. \
    Ten source ear stages use one law; both marginal false positives are certified."
