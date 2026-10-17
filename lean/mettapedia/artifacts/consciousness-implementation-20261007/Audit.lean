import Mettapedia.CogArch.Consciousness.TraceAndImplementation
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.GSLT.Core.PredicateInvariance,
    `Mettapedia.GSLT.Core.ImplementationRecoding,
    `Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
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
      if info.isUnsafe || info.isPartial then throwError "unsafe or partial declaration {name}"
      let dependencies ← liftCoreM <| collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "unpermitted dependency {name}: {dependency}"
      total := total + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      logInfo m!"AUDIT {name}: {dependencies.toList}"
  logInfo m!"SUMMARY: {modules.size} modules, {total} kernel declarations, {theorems} theorems, {compilerOnly} compiler-only names"
