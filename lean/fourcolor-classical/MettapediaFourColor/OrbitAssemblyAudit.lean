import MettapediaFourColor.OrbitAssembly
import Lean.Util.FoldConsts

/-! Dependency and axiom audit for the assembly using the periodic certificate. -/

#print axioms FourColor.Orbit10.exclude10
#print axioms FourColor.OrbitAssembly.fourColorTheorem_of_checks
#print axioms FourColor.OrbitAssembly.colorable_of_planeDrawing
#print axioms FourColor.OrbitAssembly.supported_source_construction_of_checks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for rootName in [`FourColor, `FourColor.Orbit10] do
    for case in [128, 242] do
      for i in List.range 10 do
        let name := Name.str rootName s!"c10_{case}_{i + 1}"
        if env.contains name then
          throwError m!"Removed certificate is present: {name}"
  for name in [`FourColor.f10_128, `FourColor.f10_242, `FourColor.Orbit10.f10_242,
      `FourColor.HalfTurnHubcap.fit, `FourColor.exclude10] do
    if env.contains name then
      throwError m!"Original presentation theorem is present: {name}"
  let mut seen : NameSet := {}
  let mut todo := [``FourColor.OrbitAssembly.colorable_of_planeDrawing]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        todo := info.getUsedConstantsAsSet.toList ++ todo
  for name in [``FourColor.PeriodicHubcap.fit,
      ``FourColor.ReflectedHubcap.succeeds,
      ``FourColor.ChargeBound.reflect,
      ``FourColor.ChargeBound.successful_of_bounds,
      ``FourColor.PairChargeBound.of_check,
      ``FourColor.PairChargeBound.reflect_swap,
      ``FourColor.Hubcap.successful,
      ``FourColor.Hubcap.charge_le,
      ``FourColor.HubcapOrbit.oneEntries_fit_periodic,
      ``FourColor.ClassicalAssembly.no_embedded_reduction,
      ``FourColor.PlaneDrawing.core_eq_openStar,
      ``FourColor.PlaneDrawing.midpoint_mem_site_iff,
      ``Mettapedia.Topology.NearestRegions.isConnected_region] do
    unless seen.contains name do
      throwError m!"Required proof dependency is missing: {name}"
  let mut sourceSeen : NameSet := {}
  let mut sourceTodo := [``FourColor.OrbitAssembly.supported_source_construction_of_checks]
  while !sourceTodo.isEmpty do
    let name := sourceTodo.head!
    sourceTodo := sourceTodo.tail!
    if !sourceSeen.contains name then
      sourceSeen := sourceSeen.insert name
      if let some info := env.find? name then
        sourceTodo := info.getUsedConstantsAsSet.toList ++ sourceTodo
  for name in [``FourColor.SourceConstruction.supported_construction_of_unavoidability,
      ``FourColor.Hypermap.fourColorable_of_small_unavoidability,
      ``FourColor.SourceConstruction.sourceMap_planar,
      ``FourColor.SourceConstruction.sourceMap_bridgeless,
      ``FourColor.SourceConstruction.taitColoring,
      ``Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring.edgeColoringOfDartColor,
      ``Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT.class_represented,
      ``FourColor.ClassicalAssembly.no_embedded_reduction,
      ``FourColor.PeriodicHubcap.fit, ``FourColor.ReflectedHubcap.succeeds,
      ``FourColor.Hubcap.successful, ``FourColor.PairChargeBound.reflect_swap] do
    unless sourceSeen.contains name do
      throwError m!"Required source-construction dependency is missing: {name}"
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
  logInfo "The assembly consumes rotation, semantic reflection and colouring reconstruction."
  logInfo "The graph endpoint consumes the constructed sites and nearest-region geometry."
  logInfo "The source endpoint consumes exact geometry, Tait descent and GSLT route witnesses."
  logInfo "The twenty original checks and the original arity-ten theorem are absent."
