import MettapediaFourColor.Orbit11Assembly
import Lean.Util.FoldConsts

/-! The two endpoint closures consume every shared hubcap; removed checks are absent. -/

#check @FourColor.Orbit11Assembly.fourColorTheorem_of_checks
#check @FourColor.Orbit11Assembly.colorable_of_planeDrawing
#check @FourColor.Orbit11Assembly.supported_source_construction_of_checks
#print axioms FourColor.Orbit11Assembly.colorable_of_planeDrawing
#print axioms FourColor.Orbit11Assembly.supported_source_construction_of_checks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for rootName in [``FourColor.Orbit11Assembly.colorable_of_planeDrawing,
      ``FourColor.Orbit11Assembly.supported_source_construction_of_checks] do
    let mut seen : NameSet := {}
    let mut todo := [rootName]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in [``FourColor.Orbit11.exclude11, ``FourColor.Orbit10.exclude10,
        ``FourColor.ChargeBound.reflect, ``FourColor.PairChargeBound.reflect_swap,
        ``FourColor.Hubcap.charge_le, ``FourColor.PeriodicHubcap.fit,
        ``FourColor.ReflectedHubcap.succeeds,
        ``FourColor.ClassicalAssembly.no_embedded_reduction] do
      unless seen.contains name do
        throwError m!"Required dependency {name} is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_76 do
      throwError m!"Shared hubcap f11_76 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_81 do
      throwError m!"Shared hubcap f11_81 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_89 do
      throwError m!"Shared hubcap f11_89 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_98 do
      throwError m!"Shared hubcap f11_98 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_128 do
      throwError m!"Shared hubcap f11_128 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_170 do
      throwError m!"Shared hubcap f11_170 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_193 do
      throwError m!"Shared hubcap f11_193 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_255 do
      throwError m!"Shared hubcap f11_255 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_291 do
      throwError m!"Shared hubcap f11_291 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_298 do
      throwError m!"Shared hubcap f11_298 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_304 do
      throwError m!"Shared hubcap f11_304 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_308 do
      throwError m!"Shared hubcap f11_308 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit11.f11_317 do
      throwError m!"Shared hubcap f11_317 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_28 do
      throwError m!"Shared hubcap f10_28 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_69 do
      throwError m!"Shared hubcap f10_69 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_89 do
      throwError m!"Shared hubcap f10_89 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_144 do
      throwError m!"Shared hubcap f10_144 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_233 do
      throwError m!"Shared hubcap f10_233 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_253 do
      throwError m!"Shared hubcap f10_253 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_620 do
      throwError m!"Shared hubcap f10_620 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_822 do
      throwError m!"Shared hubcap f10_822 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_835 do
      throwError m!"Shared hubcap f10_835 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_917 do
      throwError m!"Shared hubcap f10_917 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_924 do
      throwError m!"Shared hubcap f10_924 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_951 do
      throwError m!"Shared hubcap f10_951 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_998 do
      throwError m!"Shared hubcap f10_998 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1013 do
      throwError m!"Shared hubcap f10_1013 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1042 do
      throwError m!"Shared hubcap f10_1042 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1056 do
      throwError m!"Shared hubcap f10_1056 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1082 do
      throwError m!"Shared hubcap f10_1082 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1100 do
      throwError m!"Shared hubcap f10_1100 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1101 do
      throwError m!"Shared hubcap f10_1101 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1106 do
      throwError m!"Shared hubcap f10_1106 is missing from {rootName}"
    unless seen.contains ``FourColor.Orbit10.f10_1110 do
      throwError m!"Shared hubcap f10_1110 is missing from {rootName}"
  for name in [`FourColor.exclude11, `FourColor.exclude10,
      `FourColor.fourColorTheorem, `FourColor.reducibility] do
    if env.contains name then
      throwError m!"Original assembly dependency is present: {name}"
  if env.contains `FourColor.c11_76_3 then
    throwError "Removed checker declaration is present: FourColor.c11_76_3"
  if env.contains `FourColor.Orbit11.c11_76_3 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_76_3"
  if env.contains `FourColor.c11_76_4 then
    throwError "Removed checker declaration is present: FourColor.c11_76_4"
  if env.contains `FourColor.Orbit11.c11_76_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_76_4"
  if env.contains `FourColor.c11_76_9 then
    throwError "Removed checker declaration is present: FourColor.c11_76_9"
  if env.contains `FourColor.Orbit11.c11_76_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_76_9"
  if env.contains `FourColor.c11_76_10 then
    throwError "Removed checker declaration is present: FourColor.c11_76_10"
  if env.contains `FourColor.Orbit11.c11_76_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_76_10"
  if env.contains `FourColor.c11_76_11 then
    throwError "Removed checker declaration is present: FourColor.c11_76_11"
  if env.contains `FourColor.Orbit11.c11_76_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_76_11"
  if env.contains `FourColor.c11_81_5 then
    throwError "Removed checker declaration is present: FourColor.c11_81_5"
  if env.contains `FourColor.Orbit11.c11_81_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_81_5"
  if env.contains `FourColor.c11_81_6 then
    throwError "Removed checker declaration is present: FourColor.c11_81_6"
  if env.contains `FourColor.Orbit11.c11_81_6 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_81_6"
  if env.contains `FourColor.c11_81_7 then
    throwError "Removed checker declaration is present: FourColor.c11_81_7"
  if env.contains `FourColor.Orbit11.c11_81_7 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_81_7"
  if env.contains `FourColor.c11_81_10 then
    throwError "Removed checker declaration is present: FourColor.c11_81_10"
  if env.contains `FourColor.Orbit11.c11_81_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_81_10"
  if env.contains `FourColor.c11_81_11 then
    throwError "Removed checker declaration is present: FourColor.c11_81_11"
  if env.contains `FourColor.Orbit11.c11_81_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_81_11"
  if env.contains `FourColor.c11_89_4 then
    throwError "Removed checker declaration is present: FourColor.c11_89_4"
  if env.contains `FourColor.Orbit11.c11_89_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_89_4"
  if env.contains `FourColor.c11_89_5 then
    throwError "Removed checker declaration is present: FourColor.c11_89_5"
  if env.contains `FourColor.Orbit11.c11_89_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_89_5"
  if env.contains `FourColor.c11_89_9 then
    throwError "Removed checker declaration is present: FourColor.c11_89_9"
  if env.contains `FourColor.Orbit11.c11_89_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_89_9"
  if env.contains `FourColor.c11_89_10 then
    throwError "Removed checker declaration is present: FourColor.c11_89_10"
  if env.contains `FourColor.Orbit11.c11_89_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_89_10"
  if env.contains `FourColor.c11_89_11 then
    throwError "Removed checker declaration is present: FourColor.c11_89_11"
  if env.contains `FourColor.Orbit11.c11_89_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_89_11"
  if env.contains `FourColor.c11_98_6 then
    throwError "Removed checker declaration is present: FourColor.c11_98_6"
  if env.contains `FourColor.Orbit11.c11_98_6 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_98_6"
  if env.contains `FourColor.c11_98_7 then
    throwError "Removed checker declaration is present: FourColor.c11_98_7"
  if env.contains `FourColor.Orbit11.c11_98_7 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_98_7"
  if env.contains `FourColor.c11_98_8 then
    throwError "Removed checker declaration is present: FourColor.c11_98_8"
  if env.contains `FourColor.Orbit11.c11_98_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_98_8"
  if env.contains `FourColor.c11_98_9 then
    throwError "Removed checker declaration is present: FourColor.c11_98_9"
  if env.contains `FourColor.Orbit11.c11_98_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_98_9"
  if env.contains `FourColor.c11_98_11 then
    throwError "Removed checker declaration is present: FourColor.c11_98_11"
  if env.contains `FourColor.Orbit11.c11_98_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_98_11"
  if env.contains `FourColor.c11_128_4 then
    throwError "Removed checker declaration is present: FourColor.c11_128_4"
  if env.contains `FourColor.Orbit11.c11_128_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_128_4"
  if env.contains `FourColor.c11_128_5 then
    throwError "Removed checker declaration is present: FourColor.c11_128_5"
  if env.contains `FourColor.Orbit11.c11_128_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_128_5"
  if env.contains `FourColor.c11_128_8 then
    throwError "Removed checker declaration is present: FourColor.c11_128_8"
  if env.contains `FourColor.Orbit11.c11_128_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_128_8"
  if env.contains `FourColor.c11_128_9 then
    throwError "Removed checker declaration is present: FourColor.c11_128_9"
  if env.contains `FourColor.Orbit11.c11_128_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_128_9"
  if env.contains `FourColor.c11_170_4 then
    throwError "Removed checker declaration is present: FourColor.c11_170_4"
  if env.contains `FourColor.Orbit11.c11_170_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_170_4"
  if env.contains `FourColor.c11_170_5 then
    throwError "Removed checker declaration is present: FourColor.c11_170_5"
  if env.contains `FourColor.Orbit11.c11_170_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_170_5"
  if env.contains `FourColor.c11_170_6 then
    throwError "Removed checker declaration is present: FourColor.c11_170_6"
  if env.contains `FourColor.Orbit11.c11_170_6 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_170_6"
  if env.contains `FourColor.c11_170_9 then
    throwError "Removed checker declaration is present: FourColor.c11_170_9"
  if env.contains `FourColor.Orbit11.c11_170_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_170_9"
  if env.contains `FourColor.c11_193_5 then
    throwError "Removed checker declaration is present: FourColor.c11_193_5"
  if env.contains `FourColor.Orbit11.c11_193_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_193_5"
  if env.contains `FourColor.c11_193_6 then
    throwError "Removed checker declaration is present: FourColor.c11_193_6"
  if env.contains `FourColor.Orbit11.c11_193_6 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_193_6"
  if env.contains `FourColor.c11_193_7 then
    throwError "Removed checker declaration is present: FourColor.c11_193_7"
  if env.contains `FourColor.Orbit11.c11_193_7 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_193_7"
  if env.contains `FourColor.c11_193_8 then
    throwError "Removed checker declaration is present: FourColor.c11_193_8"
  if env.contains `FourColor.Orbit11.c11_193_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_193_8"
  if env.contains `FourColor.c11_255_3 then
    throwError "Removed checker declaration is present: FourColor.c11_255_3"
  if env.contains `FourColor.Orbit11.c11_255_3 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_255_3"
  if env.contains `FourColor.c11_255_8 then
    throwError "Removed checker declaration is present: FourColor.c11_255_8"
  if env.contains `FourColor.Orbit11.c11_255_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_255_8"
  if env.contains `FourColor.c11_255_9 then
    throwError "Removed checker declaration is present: FourColor.c11_255_9"
  if env.contains `FourColor.Orbit11.c11_255_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_255_9"
  if env.contains `FourColor.c11_255_10 then
    throwError "Removed checker declaration is present: FourColor.c11_255_10"
  if env.contains `FourColor.Orbit11.c11_255_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_255_10"
  if env.contains `FourColor.c11_255_11 then
    throwError "Removed checker declaration is present: FourColor.c11_255_11"
  if env.contains `FourColor.Orbit11.c11_255_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_255_11"
  if env.contains `FourColor.c11_291_4 then
    throwError "Removed checker declaration is present: FourColor.c11_291_4"
  if env.contains `FourColor.Orbit11.c11_291_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_291_4"
  if env.contains `FourColor.c11_291_5 then
    throwError "Removed checker declaration is present: FourColor.c11_291_5"
  if env.contains `FourColor.Orbit11.c11_291_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_291_5"
  if env.contains `FourColor.c11_291_6 then
    throwError "Removed checker declaration is present: FourColor.c11_291_6"
  if env.contains `FourColor.Orbit11.c11_291_6 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_291_6"
  if env.contains `FourColor.c11_291_10 then
    throwError "Removed checker declaration is present: FourColor.c11_291_10"
  if env.contains `FourColor.Orbit11.c11_291_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_291_10"
  if env.contains `FourColor.c11_291_11 then
    throwError "Removed checker declaration is present: FourColor.c11_291_11"
  if env.contains `FourColor.Orbit11.c11_291_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_291_11"
  if env.contains `FourColor.c11_298_4 then
    throwError "Removed checker declaration is present: FourColor.c11_298_4"
  if env.contains `FourColor.Orbit11.c11_298_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_298_4"
  if env.contains `FourColor.c11_298_5 then
    throwError "Removed checker declaration is present: FourColor.c11_298_5"
  if env.contains `FourColor.Orbit11.c11_298_5 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_298_5"
  if env.contains `FourColor.c11_298_9 then
    throwError "Removed checker declaration is present: FourColor.c11_298_9"
  if env.contains `FourColor.Orbit11.c11_298_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_298_9"
  if env.contains `FourColor.c11_298_10 then
    throwError "Removed checker declaration is present: FourColor.c11_298_10"
  if env.contains `FourColor.Orbit11.c11_298_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_298_10"
  if env.contains `FourColor.c11_298_11 then
    throwError "Removed checker declaration is present: FourColor.c11_298_11"
  if env.contains `FourColor.Orbit11.c11_298_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_298_11"
  if env.contains `FourColor.c11_304_3 then
    throwError "Removed checker declaration is present: FourColor.c11_304_3"
  if env.contains `FourColor.Orbit11.c11_304_3 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_304_3"
  if env.contains `FourColor.c11_304_4 then
    throwError "Removed checker declaration is present: FourColor.c11_304_4"
  if env.contains `FourColor.Orbit11.c11_304_4 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_304_4"
  if env.contains `FourColor.c11_304_9 then
    throwError "Removed checker declaration is present: FourColor.c11_304_9"
  if env.contains `FourColor.Orbit11.c11_304_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_304_9"
  if env.contains `FourColor.c11_304_10 then
    throwError "Removed checker declaration is present: FourColor.c11_304_10"
  if env.contains `FourColor.Orbit11.c11_304_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_304_10"
  if env.contains `FourColor.c11_304_11 then
    throwError "Removed checker declaration is present: FourColor.c11_304_11"
  if env.contains `FourColor.Orbit11.c11_304_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_304_11"
  if env.contains `FourColor.c11_308_3 then
    throwError "Removed checker declaration is present: FourColor.c11_308_3"
  if env.contains `FourColor.Orbit11.c11_308_3 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_308_3"
  if env.contains `FourColor.c11_308_8 then
    throwError "Removed checker declaration is present: FourColor.c11_308_8"
  if env.contains `FourColor.Orbit11.c11_308_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_308_8"
  if env.contains `FourColor.c11_308_9 then
    throwError "Removed checker declaration is present: FourColor.c11_308_9"
  if env.contains `FourColor.Orbit11.c11_308_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_308_9"
  if env.contains `FourColor.c11_308_10 then
    throwError "Removed checker declaration is present: FourColor.c11_308_10"
  if env.contains `FourColor.Orbit11.c11_308_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_308_10"
  if env.contains `FourColor.c11_308_11 then
    throwError "Removed checker declaration is present: FourColor.c11_308_11"
  if env.contains `FourColor.Orbit11.c11_308_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_308_11"
  if env.contains `FourColor.c11_317_7 then
    throwError "Removed checker declaration is present: FourColor.c11_317_7"
  if env.contains `FourColor.Orbit11.c11_317_7 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_317_7"
  if env.contains `FourColor.c11_317_8 then
    throwError "Removed checker declaration is present: FourColor.c11_317_8"
  if env.contains `FourColor.Orbit11.c11_317_8 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_317_8"
  if env.contains `FourColor.c11_317_9 then
    throwError "Removed checker declaration is present: FourColor.c11_317_9"
  if env.contains `FourColor.Orbit11.c11_317_9 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_317_9"
  if env.contains `FourColor.c11_317_10 then
    throwError "Removed checker declaration is present: FourColor.c11_317_10"
  if env.contains `FourColor.Orbit11.c11_317_10 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_317_10"
  if env.contains `FourColor.c11_317_11 then
    throwError "Removed checker declaration is present: FourColor.c11_317_11"
  if env.contains `FourColor.Orbit11.c11_317_11 then
    throwError "Removed checker declaration is present: FourColor.Orbit11.c11_317_11"
  for stem in ["c10_128_1",
      "c10_128_2",
      "c10_128_3",
      "c10_128_4",
      "c10_128_5",
      "c10_128_6",
      "c10_128_7",
      "c10_128_8",
      "c10_128_9",
      "c10_128_10",
      "c10_242_1",
      "c10_242_2",
      "c10_242_3",
      "c10_242_4",
      "c10_242_5",
      "c10_242_6",
      "c10_242_7",
      "c10_242_8",
      "c10_242_9",
      "c10_242_10",
      "c10_28_3",
      "c10_28_8",
      "c10_28_9",
      "c10_28_10",
      "c10_69_6",
      "c10_69_7",
      "c10_69_8",
      "c10_69_9",
      "c10_89_6",
      "c10_89_7",
      "c10_89_8",
      "c10_144_6",
      "c10_144_7",
      "c10_144_8",
      "c10_233_3",
      "c10_233_7",
      "c10_233_8",
      "c10_253_4",
      "c10_253_5",
      "c10_253_6",
      "c10_253_9",
      "c10_253_10",
      "c10_620_3",
      "c10_620_8",
      "c10_822_3",
      "c10_822_4",
      "c10_822_8",
      "c10_835_3",
      "c10_835_4",
      "c10_835_6",
      "c10_835_8",
      "c10_917_5",
      "c10_917_6",
      "c10_917_7",
      "c10_917_10",
      "c10_924_5",
      "c10_924_6",
      "c10_924_7",
      "c10_951_3",
      "c10_951_6",
      "c10_998_3",
      "c10_998_6",
      "c10_1013_3",
      "c10_1013_8",
      "c10_1042_4",
      "c10_1042_5",
      "c10_1042_6",
      "c10_1042_9",
      "c10_1042_10",
      "c10_1056_4",
      "c10_1056_5",
      "c10_1056_6",
      "c10_1056_8",
      "c10_1082_4",
      "c10_1082_5",
      "c10_1082_6",
      "c10_1082_8",
      "c10_1100_4",
      "c10_1100_5",
      "c10_1101_4",
      "c10_1101_5",
      "c10_1106_4",
      "c10_1106_5",
      "c10_1106_8",
      "c10_1110_3",
      "c10_1110_4",
      "c10_1110_8"] do
    for namespaceName in [`FourColor, `FourColor.Orbit10] do
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
  logInfo m!"Arity-eleven integration: audited {count} imported public declarations."
  logInfo "Both endpoints consume 13 new shared hubcaps; 62 arity-eleven checks are absent."
