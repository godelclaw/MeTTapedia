import Mettapedia.Algorithms.Retrieval
import Mettapedia.Algorithms.Retrieval.NativeTensorRetrieval
import Mettapedia.Algorithms.Retrieval.RetrievalContract
import Mettapedia.Algorithms.Retrieval.SelectorContract
import Mettapedia.Algorithms.Retrieval.TopKSelection
import Mettapedia.CognitiveArchitecture.Attention
import Mettapedia.CognitiveArchitecture.Attention.Equilibrium
import Mettapedia.CognitiveArchitecture.Attention.PremiseActivation
import Mettapedia.CognitiveArchitecture.Attention.Relevance
import Mettapedia.CognitiveArchitecture.Attention.Spreading
import Mettapedia.CognitiveArchitecture.Attention.SpreadingExamples
import Mettapedia.CognitiveArchitecture.Attention.ThreeTimescale
import Mettapedia.CognitiveArchitecture.Memory
import Mettapedia.CognitiveArchitecture.Memory.BitemporalClaims
import Mettapedia.CognitiveArchitecture.Memory.EventSourcedMemory
import Mettapedia.CognitiveArchitecture.Memory.HierarchicalSummary
import Mettapedia.CognitiveArchitecture.Memory.MemoryRefinement
import Mettapedia.CognitiveArchitecture.Memory.WorkingMemory
import Mettapedia.Logic.MarkovLogicLocalQueryApproximation
import Mettapedia.PLN.Bridges.CognitiveArchitecture
import Mettapedia.PLN.Bridges.CognitiveArchitecture.AttentionEvidence
import Mettapedia.PLN.Bridges.CognitiveArchitecture.DerivedBeliefs
import Mettapedia.PLN.Bridges.CognitiveArchitecture.EvidenceRevision
import Mettapedia.ProbabilityTheory.MarkovChain
import Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport
import Mettapedia.ProbabilityTheory.MarkovChain.Restart
import Lean.Util.CollectAxioms
import Lean.Compiler.Old

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.Algorithms.Retrieval,
    `Mettapedia.Algorithms.Retrieval.NativeTensorRetrieval,
    `Mettapedia.Algorithms.Retrieval.RetrievalContract,
    `Mettapedia.Algorithms.Retrieval.SelectorContract,
    `Mettapedia.Algorithms.Retrieval.TopKSelection,
    `Mettapedia.CognitiveArchitecture.Attention,
    `Mettapedia.CognitiveArchitecture.Attention.Equilibrium,
    `Mettapedia.CognitiveArchitecture.Attention.PremiseActivation,
    `Mettapedia.CognitiveArchitecture.Attention.Relevance,
    `Mettapedia.CognitiveArchitecture.Attention.Spreading,
    `Mettapedia.CognitiveArchitecture.Attention.SpreadingExamples,
    `Mettapedia.CognitiveArchitecture.Attention.ThreeTimescale,
    `Mettapedia.CognitiveArchitecture.Memory,
    `Mettapedia.CognitiveArchitecture.Memory.BitemporalClaims,
    `Mettapedia.CognitiveArchitecture.Memory.EventSourcedMemory,
    `Mettapedia.CognitiveArchitecture.Memory.HierarchicalSummary,
    `Mettapedia.CognitiveArchitecture.Memory.MemoryRefinement,
    `Mettapedia.CognitiveArchitecture.Memory.WorkingMemory,
    `Mettapedia.Logic.MarkovLogicLocalQueryApproximation,
    `Mettapedia.PLN.Bridges.CognitiveArchitecture,
    `Mettapedia.PLN.Bridges.CognitiveArchitecture.AttentionEvidence,
    `Mettapedia.PLN.Bridges.CognitiveArchitecture.DerivedBeliefs,
    `Mettapedia.PLN.Bridges.CognitiveArchitecture.EvidenceRevision,
    `Mettapedia.ProbabilityTheory.MarkovChain,
    `Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport,
    `Mettapedia.ProbabilityTheory.MarkovChain.Restart]
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
