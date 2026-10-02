import MettapediaFourColor.ExceptionalFlatCharge
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``NearLinearRuleData.headers, []),
    (``NearLinearRuleData.source_valid, []),
    (``NearLinearRuleData.adjacency_laws, []),
    (``NearLinearRuleData.endpoint_edge, []),
    (``NearLinearRuleData.local_paths, []),
    (``NearLinearRuleData.five_witness, []),
    (``NearLinearRuleData.sender_bound, []),
    (``NearLinearCharge.Occurrence.vertex_near, [``NearLinearRuleData.local_paths]),
    (``NearLinearCharge.Occurrence.five_near,
      [``NearLinearRuleData.five_witness, ``NearLinearCharge.Occurrence.vertex_near]),
    (``NearLinearCharge.Occurrence.sender_degree_le, [``NearLinearRuleData.sender_bound]),
    (``NearLinearCharge.applies_adj, [``NearLinearRuleData.endpoint_edge]),
    (``NearLinearCharge.applies_five_near, [``NearLinearCharge.Occurrence.five_near]),
    (``NearLinearCharge.sent_nonneg, []),
    (``NearLinearCharge.sent_eq_zero_of_not_adj, [``NearLinearCharge.applies_adj]),
    (``NearLinearCharge.sent_eq_zero_of_degree,
      [``NearLinearCharge.Occurrence.sender_degree_le]),
    (``NearLinearCharge.sent_eq_zero_of_no_five, [``NearLinearCharge.applies_five_near]),
    (``NearLinearCharge.finalCharge_eq_initial_of_no_five,
      [``NearLinearCharge.sent_eq_zero_of_no_five]),
    (``NearLinearCharge.flat_has_five, [``NearLinearCharge.finalCharge_eq_initial_of_no_five]),
    (``NearLinearCharge.pair_balance, [``NearLinearCharge.net_reverse]),
    (``NearLinearCharge.flat_eight_pair_budget, [``NearLinearCharge.pair_balance]),
    (``ExceptionalFlatCharge.overlap_supply,
      [``NearLinearCharge.flat_has_five, ``ExceptionalLocalRepair.overlap_supply]),
    (``ExceptionalFlatCharge.adjacent_eight_budget, [``NearLinearCharge.flat_eight_pair_budget])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring]
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
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Forbidden endpoint or original configuration certificate in {root}: {name}"
      unless root == ``ExceptionalFlatCharge.overlap_supply do
        if (`FourColor.ExceptionalRepairCertificate).isPrefixOf name then
          throwError m!"Exceptional finite repair in charge root {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Near-linear charge: {roots.length} roots; {all.toList.length} declarations; \
    all 84 source rules, actual radius-two observations, five-free pruning and exact \
    pair balance. Surviving cartwheel classification remains an input."
