import MettapediaFourColor.RuleMatcher
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RuleTraversal.step_transport, []),
    (``RuleTraversal.trace_transport, [``RuleTraversal.step_transport]),
    (``RuleTraversalData.valid, []),
    (``RuleTraversalData.length_le_seven, []),
    (``RuleMatcher.candidate_eq, [``RuleTraversal.trace_transport, ``RuleTraversalData.valid]),
    (``RuleMatcher.rooted_unique, [``RuleMatcher.candidate_eq]),
    (``RuleMatcher.goodTurn_sound, []),
    (``RuleMatcher.occurrenceOfFits, [``RuleMatcher.goodTurn_sound]),
    (``RuleMatcher.fits_of_occurrence, [``RuleMatcher.goodTurn_of]),
    (``RuleMatcher.check_iff,
      [``RuleMatcher.candidate_eq, ``RuleMatcher.occurrenceOfFits,
        ``RuleMatcher.fits_of_occurrence]),
    (``RuleMatcher.sentAt_eq, [``RuleMatcher.check_iff]),
    (``RuleMatcher.sentBetween_eq, [``RuleMatcher.sentAt_eq]),
    (``RuleMatcher.chargeAt_eq, [``RuleMatcher.sentBetween_eq]),
    (``RuleMatcher.checked_pair_budget,
      [``RuleMatcher.chargeAt_eq, ``NearLinearCharge.flat_eight_pair_budget])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring,
    `FourColor.ExceptionalRepairCertificate]
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
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exact rule matcher: {roots.length} roots; {all.toList.length} declarations; \
    rooted uniqueness, full rule-check equivalence and actual charge. No reduction \
    certificate, complete Four Colour endpoint or flat-neighbourhood classification."
