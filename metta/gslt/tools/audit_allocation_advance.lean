import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance
import Lean.Util.CollectAxioms
import Lean.Data.Json.Printer

/-! Exhaustive declaration audit of retained allocation advancement. -/

open Lean Elab Command

run_cmd do
  let modules := #[
    `Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let environment ← getEnv
  let mut seen : NameSet := {}
  let mut safe := 0
  let mut theorems := 0
  let mut nonlogical := 0
  let mut compilerOnly := 0
  let mut axioms : Array Name := #[]
  for moduleName in modules do
    let some index := environment.header.moduleNames.toList.idxOf? moduleName
      | throwError "missing module {moduleName}"
    let data := environment.header.moduleData[index]!
    for name in (data.constNames ++ data.extraConstNames).toList do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := environment.checked.get.find? name | do
        unless data.extraConstNames.contains name do throwError "missing declaration {name}"
        compilerOnly := compilerOnly + 1
        continue
      if info.isUnsafe || info.isPartial then
        liftIO <| IO.println (Json.mkObj [("kind", .str "nonlogical-implementation"),
          ("name", .str name.toString), ("certifiedImplementation", .bool false)]).compress
        nonlogical := nonlogical + 1
        continue
      if info matches .axiomInfo _ then throwError "introduced axiom {name}"
      let dependencies ← liftCoreM <| collectAxioms name
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unpermitted dependency {name}: {dependency}"
        unless axioms.contains dependency do axioms := axioms.push dependency
      safe := safe + 1
      if info matches .thmInfo _ then theorems := theorems + 1
  liftIO <| IO.println (Json.mkObj [
    ("safeKernelDeclarations", toJson safe), ("theorems", toJson theorems),
    ("separateNonlogicalImplementations", toJson nonlogical),
    ("compilerOnlyNames", toJson compilerOnly),
    ("axioms", toJson (axioms.map Name.toString))]).compress
