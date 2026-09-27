import MettapediaFourColor.OrbitAssembly
import Lean.Util.FoldConsts

/-! Dependency and axiom audit for the assembly using the periodic certificate. -/

#print axioms FourColor.Orbit10.exclude10
#print axioms FourColor.OrbitAssembly.fourColorTheorem_of_checks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for rootName in [`FourColor, `FourColor.Orbit10] do
    for i in List.range 10 do
      let name := Name.str rootName s!"c10_128_{i + 1}"
      if env.contains name then
        throwError m!"Removed certificate is present: {name}"
  for name in [`FourColor.f10_128, `FourColor.exclude10] do
    if env.contains name then
      throwError m!"Original presentation theorem is present: {name}"
  let mut seen : NameSet := {}
  let mut todo := [``FourColor.OrbitAssembly.fourColorTheorem_of_checks]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        todo := info.getUsedConstantsAsSet.toList ++ todo
  for name in [``FourColor.PeriodicHubcap.fit,
      ``FourColor.HubcapOrbit.oneEntries_fit_periodic,
      ``FourColor.ClassicalAssembly.no_embedded_reduction] do
    unless seen.contains name do
      throwError m!"Required proof dependency is missing: {name}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`FourColor, `MettapediaFourColor, `Mettapedia, `Foundation]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) && !name.isInternal then
      count := count + 1
      for axiomName in (← liftCoreM <| collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Unexpected axiom in {name}: {axiomName}"
  logInfo m!"Audited {count} imported public declarations; only the three permitted axioms."
  logInfo "The assembly consumes periodic sharing and explicit colouring reconstruction."
  logInfo "The ten original checks and the original arity-ten theorem are absent."
