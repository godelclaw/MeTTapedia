import MettapediaFourColor.DiamondKempeBoundary
import Lean.Util.FoldConsts

/-!
# Audit of joint boundary elimination and separate-repair obstructions

The negative result consumes the proved specification of the converged Kempe
checker. It does not consume an existing configuration certificate or a
complete Four Colour endpoint. The positive roots reconstruct actual contract
colourings from the six-colour boundary relation.
-/

open FourColor FourColor.DiamondJointContract FourColor.DiamondKempeBoundary

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``reconstruct_valid, [``reconstruct, ``Admissible]),
    (``eliminate, [``ConfigurationFaceGraph.Presentation.ContractAssignment, ``Admissible]),
    (``contractTrace_iff, [``eliminate, ``reconstruct_valid,
      ``DiamondContract.contractTrace004]),
    (``monochrome_not_coclosure, [``not_mem_kempeTree_iff, ``monochrome_retained,
      ``KempeCoclosure]),
    (``leftOnly_trace, [``leftOnly, ``referenceContract,
      ``ConfigurationTable.Realization.ccRingTrace]),
    (``rightOnly_trace, [``rightOnly, ``referenceContract,
      ``ConfigurationTable.Realization.ccRingTrace]),
    (``leftOnly_not_repair, [``leftOnly_trace, ``monochrome_not_coclosure]),
    (``rightOnly_not_repair, [``rightOnly_trace, ``monochrome_not_coclosure]),
    (``monochrome_not_joint_contract, [``contractTrace_iff, ``Admissible])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Classical certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond joint boundary and Kempe obstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    no classical certificate or complete theorem dependencies."
