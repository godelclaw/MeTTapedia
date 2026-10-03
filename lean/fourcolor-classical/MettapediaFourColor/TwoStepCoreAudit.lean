import MettapediaFourColor.TwoStepCoreProgress
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor SimpleGraph

run_cmd do
  let env ← getEnv
  let sourceRoots := [``TwoStepCoreProgress.upper_no_extension,
    ``TwoStepCoreProgress.lower_no_extension,
    ``TwoStepCoreProgress.upper_repaired_proper,
    ``TwoStepCoreProgress.lower_repaired_proper]
  let roots := [``ColoringListPropagation.trim_sound,
    ``ColoringListPropagation.run_sound, ``ColoringListPropagation.empty_refutes] ++ sourceRoots
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
    if sourceRoots.contains root then
      unless seen.contains ``NearLinearDiamondData.Input.graph do
        throwError m!"Missing decoded source graph in {root}"
    if root == ``TwoStepCoreProgress.upper_no_extension ||
        root == ``TwoStepCoreProgress.lower_no_extension then
      unless seen.contains ``ColoringListPropagation.empty_refutes do
        throwError m!"Missing propagation soundness in {root}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Two-step cores: {roots.length} roots; {all.toList.length} declarations. \
    Twenty-nine source boundary rejections and two reconstructed source colourings."
