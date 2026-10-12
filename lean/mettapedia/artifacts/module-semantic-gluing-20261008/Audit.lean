import Mettapedia.GSLT.LanguageDef.ModuleAlgebra
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Authoring,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Gluing,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Semantics,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluing,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SemanticGluingControls,
    `Mettapedia.GSLT.LanguageDef.ModuleAlgebra]
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
    for name in (data.constNames ++ data.extraConstNames).toList.eraseDups do
      let some info := env.checked.get.find? name | do
        unless data.extraConstNames.contains name do
          throwError "unavailable kernel declaration {name}"
        compilerOnly := compilerOnly + 1
        continue
      if info matches .axiomInfo _ then throwError "new axiom {name}"
      if info.isUnsafe then throwError "unsafe source declaration {name}"
      if info.isPartial then throwError "partial declaration {name}"
      let dependencies ← liftCoreM <| collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "unpermitted dependency {name}: {dependency}"
      total := total + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      logInfo m!"AUDIT {name}: {dependencies.toList}"
  logInfo m!"SUMMARY: {modules.size} modules, {total} kernel declarations, {theorems} theorems, {compilerOnly} compiler-only names"

run_cmd do
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  for name in #[
      `Mettapedia.GSLT.LanguageDef.ScopePolicies.join_not_conservative,
      `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.generative_rig_join,
      `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.compatible_join_not_conservative,
      `Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Controls.join_has_mixed_path] do
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "unpermitted reused-control dependency {name}: {dependency}"
    logInfo m!"REUSED-CONTROL {name}: {dependencies.toList}"
