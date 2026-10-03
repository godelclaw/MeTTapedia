import MettapediaFourColor.PairPhaseCore
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor SimpleGraph

run_cmd do
  let env ← getEnv
  let sourceRoots := [``PairPhaseCore.extra_no_extension,
    ``PairPhaseCore.upper_phase_rejects, ``PairPhaseCore.lower_phase_rejects,
    ``PairPhaseCore.upper_nearby_proper, ``PairPhaseCore.upper_nearby_one_port]
  let roots := [``KempePairHistory.pointwise, ``KempePairHistory.component_changed,
    ``KempePairHistory.physical] ++ sourceRoots
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
    if sourceRoots.contains root && root != ``PairPhaseCore.upper_nearby_one_port then
      unless seen.contains ``NearLinearDiamondData.Input.graph do
        throwError m!"Missing decoded source graph in {root}"
    if root == ``PairPhaseCore.upper_phase_rejects || root == ``PairPhaseCore.lower_phase_rejects then
      unless seen.contains ``ColoringListPropagation.empty_refutes do
        throwError m!"Missing shared rejection theorem in {root}"
    if root == ``KempePairHistory.component_changed then
      unless seen.contains ``Coloring.component_changed_of_pointwise_swap do
        throwError "Missing original-component propagation"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Fixed-pair phases: {roots.length} roots; {all.toList.length} declarations. \
    Arbitrarily long histories have a component normal form; both source phase tables reject."
