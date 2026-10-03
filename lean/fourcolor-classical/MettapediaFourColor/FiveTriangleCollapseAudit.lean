import MettapediaFourColor.FiveTriangleJointChoice
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``FiveTriangleCollapseObstruction.upper_witness,
    ``FiveTriangleCollapseObstruction.lower_obstruction,
    ``FiveTriangleCollapseObstruction.no_collapse_reconstruction,
    ``FiveTriangleJointChoice.fan_exact,
    ``FiveTriangleJointChoice.whole_component,
    ``FiveTriangleJointChoice.before_proper,
    ``FiveTriangleJointChoice.compatible_witnesses]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`FourColor.Bulk, `FourColor.fourColorTheorem,
    `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData,
    `FourColor.DiamondProfileData, `Lean.ofReduceBool]
  let mut all : NameSet := {}
  for root in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
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
    for required in [``NearLinearDiamondData.Input.graph] do
      unless seen.contains required do
        throwError m!"Missing actual-graph dependency in {root}: {required}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Five-triangle collapse obstruction: {roots.length} roots; \
    {all.toList.length} declarations. One fixed boundary alignment is excluded \
    by an actual source colouring and a target triangle contradiction. \
    The same fan exterior is retained in a concrete one-component repair; \
    broader joint selection and family coverage remain open."
