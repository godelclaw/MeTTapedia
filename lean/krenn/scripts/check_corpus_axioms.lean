import Lean
import Lean.Util.CollectAxioms

/-! Inspect all compiled corpus modules together. This program reads module
metadata; it does not replace source builds or the kernel's proof checking. -/

open Lean

private def audit (owned : Std.HashSet Name) : CoreM Unit := do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let negative ← collectAxioms ``sorryAx
  unless (negative.filter fun axiomName => !allowed.contains axiomName).contains ``sorryAx do
    throwError "admission negative control failed"
  let mut modules := 0
  let mut theorems := 0
  let mut declarations := 0
  let mut executionOnly := 0
  for index in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[index]!
    if owned.contains moduleName then
      let data := env.header.moduleData[index]!
      for name in (data.constNames ++ data.extraConstNames).toList.eraseDups do
        let some info := env.checked.get.find? name | do
          unless data.extraConstNames.contains name do
            throwError "unavailable kernel declaration {name}"
          executionOnly := executionOnly + 1
          continue
        if info matches .axiomInfo _ then throwError "owned axiom declaration {name}"
        if (info.isUnsafe || info.isPartial) && !(info matches .thmInfo _) then
          executionOnly := executionOnly + 1
          continue
        let axioms ← collectAxioms name
        let excess := axioms.filter fun axiomName => !allowed.contains axiomName
        unless excess.isEmpty do throwError "{name}: unexpected axioms {excess}"
        declarations := declarations + 1
        if info matches .thmInfo _ then theorems := theorems + 1
      modules := modules + 1
      if modules % 1000 == 0 then
        liftM <| IO.println s!"Audited {modules} modules"
  unless modules == owned.size do throwError "some requested modules were not loaded"
  unless theorems > 0 do throwError "empty theorem audit"
  liftM <| IO.println s!"Qualified: {modules} modules; {theorems} theorems; {declarations} kernel declarations; {executionOnly} execution-only entries; standard axioms only"

/-- With no arguments, audit the complete manifest and every library source.
Explicit module arguments select a partial audit for diagnostic use. -/
def main (args : List String) : IO Unit := do
  let mut modules : List Name := []
  if args.isEmpty then
    let source ← IO.FS.readFile "corpus-modules.txt"
    modules := ((source.splitOn "\n").filter (· != "")).map String.toName
    for entry in ← (System.FilePath.mk "lib").readDir do
      if entry.fileName.endsWith ".lean" then
        modules := (entry.fileName.replace ".lean" "").toName :: modules
    IO.println "Complete corpus inventory audit"
  else
    IO.println "Partial audit of explicitly selected modules"
    modules := args.map String.toName
  let owned : Std.HashSet Name := modules.foldl (fun set name => set.insert name) {}
  initSearchPath (← findSysroot)
  -- Only constant tables are inspected, so imported extension initializers
  -- need not run. Loading all requested modules also checks name clashes.
  let imports : Array Import := modules.toArray.map fun name => { module := name }
  let env ← importModules imports {} (loadExts := false)
  (audit owned).toIO' { fileName := "corpus-axiom-audit", fileMap := FileMap.ofString "" }
    { env := env }
