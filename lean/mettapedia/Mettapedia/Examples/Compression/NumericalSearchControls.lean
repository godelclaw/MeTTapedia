import Mettapedia.Algorithms.Compression.ParameterRegion
import Mettapedia.Algorithms.Compression.OrderedScan
import Mettapedia.Algorithms.Compression.ObservedSearch
import Lean.Util.CollectAxioms
import Lean.Data.Json.Printer

/-! Integration audit for finite parameter traversal, ordered partial scans
and original-task artifact checking. Native correspondence is tested through
the ordinary tensor and IC libraries; this audit checks the Lean owners. -/

open Lean Elab Command

run_cmd do
  let modules := #[`Mettapedia.Algorithms.Compression.ParameterRegion,
    `Mettapedia.Algorithms.Compression.OrderedScan,
    `Mettapedia.Algorithms.Compression.ObservedSearch]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut safe := 0
  let mut theorems := 0
  let mut nonlogical := 0
  let mut compilerOnly := 0
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing module {moduleName}"
    let data := env.header.moduleData[index]!
    for declName in (data.constNames ++ data.extraConstNames).toList do
      if seen.contains declName then continue
      seen := seen.insert declName
      let some info := env.checked.get.find? declName | do
        unless data.extraConstNames.contains declName do throwError "missing declaration {declName}"
        compilerOnly := compilerOnly + 1
        continue
      if info.isUnsafe || info.isPartial then
        nonlogical := nonlogical + 1
        continue
      if info matches .axiomInfo _ then throwError "added axiom {declName}"
      let dependencies ← liftCoreM <| collectAxioms declName
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unpermitted dependency {declName}: {dependency}"
      safe := safe + 1
      if info matches .thmInfo _ then theorems := theorems + 1
  liftIO <| IO.println (Json.mkObj [
    ("safeKernelDeclarations", toJson safe), ("theorems", toJson theorems),
    ("separateNonlogicalImplementations", toJson nonlogical),
    ("compilerOnlyNames", toJson compilerOnly)]).compress
