import MettapediaFourColor.Orbit9Assembly
import Lean.Util.FoldConsts

/-! Audit consumption of all three shared presentations and their trusted dependencies. -/

#check @FourColor.Orbit9Assembly.colorable_of_planeDrawing
#check @FourColor.Orbit9Assembly.supported_source_construction_of_checks
#print axioms FourColor.Orbit9Assembly.colorable_of_planeDrawing
#print axioms FourColor.Orbit9Assembly.supported_source_construction_of_checks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required : List Name := [
    ``FourColor.Orbit9.exclude9,
    ``FourColor.Orbit10.exclude10,
    ``FourColor.Orbit11.exclude11,
    ``FourColor.ChargeBound.reflect,
    ``FourColor.PairChargeBound.reflect_swap,
    ``FourColor.Hubcap.charge_le,
    ``FourColor.PeriodicHubcap.fit,
    ``FourColor.ReflectedHubcap.succeeds,
    ``FourColor.ClassicalAssembly.no_embedded_reduction,
    ``FourColor.Orbit9.f9_22,
    ``FourColor.Orbit9.f9_125,
    ``FourColor.Orbit9.f9_276,
    ``FourColor.Orbit9.f9_295,
    ``FourColor.Orbit9.f9_359,
    ``FourColor.Orbit9.f9_732,
    ``FourColor.Orbit9.f9_754,
    ``FourColor.Orbit9.f9_758,
    ``FourColor.Orbit9.f9_762,
    ``FourColor.Orbit9.f9_858,
    ``FourColor.Orbit9.f9_862,
    ``FourColor.Orbit9.f9_950,
    ``FourColor.Orbit9.f9_1589,
    ``FourColor.Orbit9.f9_1591,
    ``FourColor.Orbit9.f9_1609,
    ``FourColor.Orbit9.f9_1767,
    ``FourColor.Orbit9.f9_1779,
    ``FourColor.Orbit9.f9_1821,
    ``FourColor.Orbit9.f9_2097,
    ``FourColor.Orbit9.f9_2201,
    ``FourColor.Orbit9.f9_2208,
    ``FourColor.Orbit9.f9_2340,
    ``FourColor.Orbit9.f9_2446,
    ``FourColor.Orbit9.f9_2458,
    ``FourColor.Orbit9.f9_2692,
    ``FourColor.Orbit9.f9_2900,
    ``FourColor.Orbit9.f9_3312,
    ``FourColor.Orbit9.f9_3336,
    ``FourColor.Orbit9.f9_3344,
    ``FourColor.Orbit9.f9_3384,
    ``FourColor.Orbit9.f9_3508,
    ``FourColor.Orbit9.f9_3556,
    ``FourColor.Orbit10.f10_28,
    ``FourColor.Orbit10.f10_69,
    ``FourColor.Orbit10.f10_89,
    ``FourColor.Orbit10.f10_144,
    ``FourColor.Orbit10.f10_233,
    ``FourColor.Orbit10.f10_253,
    ``FourColor.Orbit10.f10_620,
    ``FourColor.Orbit10.f10_822,
    ``FourColor.Orbit10.f10_835,
    ``FourColor.Orbit10.f10_917,
    ``FourColor.Orbit10.f10_924,
    ``FourColor.Orbit10.f10_951,
    ``FourColor.Orbit10.f10_998,
    ``FourColor.Orbit10.f10_1013,
    ``FourColor.Orbit10.f10_1042,
    ``FourColor.Orbit10.f10_1056,
    ``FourColor.Orbit10.f10_1082,
    ``FourColor.Orbit10.f10_1100,
    ``FourColor.Orbit10.f10_1101,
    ``FourColor.Orbit10.f10_1106,
    ``FourColor.Orbit10.f10_1110,
    ``FourColor.Orbit11.f11_76,
    ``FourColor.Orbit11.f11_81,
    ``FourColor.Orbit11.f11_89,
    ``FourColor.Orbit11.f11_98,
    ``FourColor.Orbit11.f11_128,
    ``FourColor.Orbit11.f11_170,
    ``FourColor.Orbit11.f11_193,
    ``FourColor.Orbit11.f11_255,
    ``FourColor.Orbit11.f11_291,
    ``FourColor.Orbit11.f11_298,
    ``FourColor.Orbit11.f11_304,
    ``FourColor.Orbit11.f11_308,
    ``FourColor.Orbit11.f11_317]
  for rootName in [``FourColor.Orbit9Assembly.colorable_of_planeDrawing,
      ``FourColor.Orbit9Assembly.supported_source_construction_of_checks] do
    let mut seen : NameSet := {}
    let mut todo := [rootName]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is missing from {rootName}"
  for name in [`FourColor.exclude9, `FourColor.exclude10, `FourColor.exclude11,
      `FourColor.fourColorTheorem, `FourColor.reducibility] do
    if env.contains name then
      throwError m!"Original assembly dependency is present: {name}"
  for stem in [
      "c9_125_5", "c9_1589_2", "c9_1589_6", "c9_1589_7", "c9_1591_3", "c9_1591_4",
      "c9_1591_8", "c9_1591_9", "c9_1609_2", "c9_1609_6", "c9_1609_7", "c9_1767_3",
      "c9_1779_3", "c9_1779_5", "c9_1779_7", "c9_1821_2", "c9_1821_6", "c9_1821_7",
      "c9_2097_3", "c9_2097_4", "c9_2097_8", "c9_2097_9", "c9_2201_5", "c9_2201_6",
      "c9_2201_7", "c9_2208_6", "c9_2208_7", "c9_22_2", "c9_22_6", "c9_2340_3",
      "c9_2340_7", "c9_2340_8", "c9_2340_9", "c9_2446_3", "c9_2446_5", "c9_2458_3",
      "c9_2458_6", "c9_2458_7", "c9_2692_3", "c9_2692_6", "c9_276_5", "c9_2900_2",
      "c9_2900_6", "c9_295_4", "c9_295_5", "c9_295_7", "c9_3312_5", "c9_3336_4",
      "c9_3336_5", "c9_3336_7", "c9_3344_2", "c9_3384_3", "c9_3384_5", "c9_3384_7",
      "c9_3508_4", "c9_3508_5", "c9_3508_8", "c9_3508_9", "c9_3556_4", "c9_3556_5",
      "c9_3556_7", "c9_359_4", "c9_359_5", "c9_359_8", "c9_359_9", "c9_732_5", "c9_754_5",
      "c9_754_6", "c9_754_7", "c9_754_8", "c9_758_4", "c9_758_5", "c9_758_8", "c9_758_9",
      "c9_762_5", "c9_762_6", "c9_762_7", "c9_858_3", "c9_858_5", "c9_858_7", "c9_862_5",
      "c9_862_6", "c9_862_7", "c9_862_9", "c9_950_3", "c9_950_5", "c9_950_7"] do
    for namespaceName in [`FourColor, `FourColor.Orbit9] do
      let name := Name.str namespaceName stem
      if env.contains name then
        throwError m!"Superseded checker declaration is present: {name}"
  for stem in [
      "c10_1013_3", "c10_1013_8", "c10_1042_10", "c10_1042_4", "c10_1042_5", "c10_1042_6",
      "c10_1042_9", "c10_1056_4", "c10_1056_5", "c10_1056_6", "c10_1056_8", "c10_1082_4",
      "c10_1082_5", "c10_1082_6", "c10_1082_8", "c10_1100_4", "c10_1100_5", "c10_1101_4",
      "c10_1101_5", "c10_1106_4", "c10_1106_5", "c10_1106_8", "c10_1110_3", "c10_1110_4",
      "c10_1110_8", "c10_128_1", "c10_128_10", "c10_128_2", "c10_128_3", "c10_128_4",
      "c10_128_5", "c10_128_6", "c10_128_7", "c10_128_8", "c10_128_9", "c10_144_6",
      "c10_144_7", "c10_144_8", "c10_233_3", "c10_233_7", "c10_233_8", "c10_242_1",
      "c10_242_10", "c10_242_2", "c10_242_3", "c10_242_4", "c10_242_5", "c10_242_6",
      "c10_242_7", "c10_242_8", "c10_242_9", "c10_253_10", "c10_253_4", "c10_253_5",
      "c10_253_6", "c10_253_9", "c10_28_10", "c10_28_3", "c10_28_8", "c10_28_9",
      "c10_620_3", "c10_620_8", "c10_69_6", "c10_69_7", "c10_69_8", "c10_69_9",
      "c10_822_3", "c10_822_4", "c10_822_8", "c10_835_3", "c10_835_4", "c10_835_6",
      "c10_835_8", "c10_89_6", "c10_89_7", "c10_89_8", "c10_917_10", "c10_917_5",
      "c10_917_6", "c10_917_7", "c10_924_5", "c10_924_6", "c10_924_7", "c10_951_3",
      "c10_951_6", "c10_998_3", "c10_998_6"] do
    for namespaceName in [`FourColor, `FourColor.Orbit10] do
      let name := Name.str namespaceName stem
      if env.contains name then
        throwError m!"Superseded checker declaration is present: {name}"
  for stem in [
      "c11_128_4", "c11_128_5", "c11_128_8", "c11_128_9", "c11_170_4", "c11_170_5",
      "c11_170_6", "c11_170_9", "c11_193_5", "c11_193_6", "c11_193_7", "c11_193_8",
      "c11_255_10", "c11_255_11", "c11_255_3", "c11_255_8", "c11_255_9", "c11_291_10",
      "c11_291_11", "c11_291_4", "c11_291_5", "c11_291_6", "c11_298_10", "c11_298_11",
      "c11_298_4", "c11_298_5", "c11_298_9", "c11_304_10", "c11_304_11", "c11_304_3",
      "c11_304_4", "c11_304_9", "c11_308_10", "c11_308_11", "c11_308_3", "c11_308_8",
      "c11_308_9", "c11_317_10", "c11_317_11", "c11_317_7", "c11_317_8", "c11_317_9",
      "c11_76_10", "c11_76_11", "c11_76_3", "c11_76_4", "c11_76_9", "c11_81_10",
      "c11_81_11", "c11_81_5", "c11_81_6", "c11_81_7", "c11_89_10", "c11_89_11",
      "c11_89_4", "c11_89_5", "c11_89_9", "c11_98_11", "c11_98_6", "c11_98_7", "c11_98_8",
      "c11_98_9"] do
    for namespaceName in [`FourColor, `FourColor.Orbit11] do
      let name := Name.str namespaceName stem
      if env.contains name then
        throwError m!"Superseded checker declaration is present: {name}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : List Name := [`FourColor, `MettapediaFourColor, `Mettapedia, `Foundation]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (·.isPrefixOf name) && !name.isInternal then
      count := count + 1
      for axiomName in (← liftCoreM <| collectAxioms name) do
        unless allowed.contains axiomName do
          throwError m!"Unexpected axiom in {name}: {axiomName}"
  logInfo m!"Arity-nine integration: audited {count} imported public declarations."
  logInfo "Both endpoints consume 32 new shared hubcaps; 87 arity-nine checks are absent."
