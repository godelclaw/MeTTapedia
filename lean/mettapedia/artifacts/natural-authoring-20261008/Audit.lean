import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if moduleName.toString.startsWith "Mettapedia." then
      logInfo m!"LOCAL-MODULE {moduleName}"
  let mut total := 0
  let mut theorems := 0
  let mut compilerOnly := 0
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing audited module {moduleName}"
    let data := env.header.moduleData[index]!
    for declName in (data.constNames ++ data.extraConstNames).toList.eraseDups do
      let some info := env.checked.get.find? declName | do
        unless data.extraConstNames.contains declName do
          throwError "unavailable kernel declaration {declName}"
        compilerOnly := compilerOnly + 1
        continue
      if info matches .axiomInfo _ then throwError "new axiom {declName}"
      if info.isUnsafe then throwError "unsafe source declaration {declName}"
      if info.isPartial then throwError "partial declaration {declName}"
      let dependencies ← liftCoreM <| collectAxioms declName
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "unpermitted dependency {declName}: {dependency}"
      total := total + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      logInfo m!"AUDIT {declName}: {dependencies.toList}"
  logInfo m!"SUMMARY: {modules.size} modules, {total} kernel declarations, {theorems} theorems, {compilerOnly} compiler-only names"
