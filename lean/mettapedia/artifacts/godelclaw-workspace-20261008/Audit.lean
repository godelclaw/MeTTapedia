import Mettapedia.CognitiveArchitecture.GodelClaw
import Mettapedia.CognitiveArchitecture.Agent
import Mettapedia.CognitiveArchitecture.Consciousness.TraceAndImplementation
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.CognitiveArchitecture.Agent.ContextEpoch,
    `Mettapedia.CognitiveArchitecture.Agent.ContextAttention,
    `Mettapedia.CognitiveArchitecture.GodelClaw.GlobalWorkspace,
    `Mettapedia.CognitiveArchitecture.Agent,
    `Mettapedia.CognitiveArchitecture.GodelClaw,
    `Mettapedia.GSLT.Core.ObservationIndexedPruning,
    `Mettapedia.GSLT.Logic.HennessyMilnerAdequacy,
    `Mettapedia.CognitiveArchitecture.Consciousness.ArchitecturalIndicators]
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
      if info.isPartial then
        let some parentName := Compiler.isUnsafeRecName? declName
          | throwError "partial source declaration {declName}"
        let some (.defnInfo parent) := env.checked.get.find? parentName
          | throwError "runtime helper has no kernel definition {declName}"
        unless parent.safety == .safe && parent.type == info.type do
          throwError "runtime helper lacks a safe matching kernel definition {declName}"
        compilerOnly := compilerOnly + 1
        logInfo m!"COMPILER-RECURSION {declName}: safe parent {parentName}"
        continue
      let referenced := info.type.getUsedConstants ++
        (match info with
          | .defnInfo value => value.value.getUsedConstants
          | .thmInfo value => value.value.getUsedConstants
          | .opaqueInfo value => value.value.getUsedConstants
          | _ => #[])
      for reference in referenced do
        if let some dependency := env.checked.get.find? reference then
          if dependency.isUnsafe || dependency.isPartial then
            throwError "kernel declaration uses runtime-only code {declName}: {reference}"
      let dependencies ← liftCoreM <| collectAxioms declName
      for dependency in dependencies do
        unless allowed.contains dependency do
          throwError "unpermitted dependency {declName}: {dependency}"
      total := total + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      logInfo m!"AUDIT {declName}: {dependencies.toList}"
  logInfo m!"SUMMARY: {modules.size} modules, {total} kernel declarations, {theorems} theorems, {compilerOnly} compiler-only names"
