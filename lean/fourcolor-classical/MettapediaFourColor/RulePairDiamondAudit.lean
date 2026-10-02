import MettapediaFourColor.ActualRulePairDiamond
import MettapediaFourColor.RulePairExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RulePairDiamond.closing_corner, []),
    (``RulePairDiamond.mixed, [``RulePairDiamond.closing_corner]),
    (``RulePairDiamond.aligned, []),
    (``RulePairDiamond.mixed_of_checks,
      [``RuleMatcher.check_iff, ``RulePairDiamond.aligned, ``RulePairDiamond.mixed]),
    (``ActualRulePairDiamond.degree_dart, [``ActualDualContract.map_eq_source_relabel]),
    (``ActualRulePairDiamond.face_pattern, [``ActualRulePairDiamond.degree_dart]),
    (``ActualRulePairDiamond.not_in_minimal,
      [``RulePairDiamond.mixed_of_checks, ``ActualRulePairDiamond.face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
        ``MixedDiamondPatch.Tangle.FaceReduction.colorable_of_smaller,
        ``DiamondProfileReducibility.repair002]),
    (``ActualRulePairDiamond.right_check_false, [``ActualRulePairDiamond.not_in_minimal]),
    (``RulePairExample.source_valid, []),
    (``RulePairExample.row_source_exact, []),
    (``RulePairExample.cyclic, []),
    (``RulePairExample.triangular, []),
    (``RulePairExample.observations, []),
    (``RulePairExample.has_mixed,
      [``RulePairDiamond.mixed_of_checks, ``RulePairExample.cyclic,
        ``RulePairExample.triangular, ``RulePairExample.observations])]
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
  logInfo m!"Joint charge-rule reduction: {roots.length} roots; {all.toList.length} declarations; \
    actual strict descent and colouring reconstruction, with a nonempty certified instance. \
    Shared diamond profile retained; no original catalogue certificate, D1774 repair, \
    complete Four Colour endpoint or flat-neighbourhood classification."
