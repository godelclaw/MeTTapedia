import MettapediaFourColor.ExceptionalRepairReconstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeIndexedCertificate.sound, [``KempeProfileCertificate.answerWord_map]),
    (``KempeMaskCertificate.entries_eq, []),
    (``KempeMaskCertificate.check_sound,
      [``KempeChordMasks.recolor_matches, ``KempeMaskCertificate.entries_complete]),
    (``ExceptionalRepairCertificate.source_edges, []),
    (``ExceptionalRepairCertificate.terminalCheck_sound,
      [``ExceptionalRepairCertificate.source_edges]),
    (``ExceptionalRepairCertificate.check_sound, [``KempeMaskCertificate.check_sound]),
    (``ExceptionalRepairCertificate.checked, []),
    (``ExceptionalRepairCertificate.coverage, []),
    (``ExceptionalRepairCertificate.repair,
      [``ExceptionalRepairCertificate.checked, ``ExceptionalRepairCertificate.coverage,
       ``ExceptionalRepairCertificate.terminalCheck_sound, ``KempeIndexedCertificate.sound,
       ``Bulk.partialOf_indexOf]),
    (``GraphTraceAlignment.align, [``ringColors_eq_shift]),
    (``ExceptionalRepairReconstruction.reconstruct_trace,
      [``GraphTraceAlignment.align, ``ExceptionalBoundaryReconstruction.reconstruct]),
    (``ExceptionalRepairReconstruction.reconstruct,
      [``ExceptionalRepairCertificate.repair,
       ``ExceptionalRepairReconstruction.reconstruct_trace])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec]
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
        throwError m!"Complete theorem or original catalogue certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exceptional joint-chord repair: {roots.length} roots; \
    {all.toList.length} declarations; literal source witnesses, strict descent and complete \
    proper-input coverage; actual exterior closure remains an explicit hypothesis."
