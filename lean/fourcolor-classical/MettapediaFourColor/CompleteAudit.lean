import MettapediaFourColor.Complete
import Lean.Util.FoldConsts

/-!
# Audit of the complete compositional endpoints

The endpoint closures must consume the catalogue, the joint-profile diamond repair,
the boundary-split repair transfer, all seven arity proofs,
the shared charge certificates and the geometric reconstruction. The
original unconditional theorem and the superseded arity-nine, arity-ten and arity-eleven
checks must be absent. Catalogue membership is checked at every index, including the
hybrid certificates; no conditional checker input is supplied by an axiom.
-/

#check @FourColor.CompositionalComplete.fourColorTheorem
#check @FourColor.CompositionalComplete.colorable_of_planeDrawing
#check @FourColor.CompositionalComplete.supported_source_construction
#check @FourColor.CompositionalComplete.supported_source_sweep
#print axioms FourColor.CompositionalComplete.fourColorTheorem
#print axioms FourColor.CompositionalComplete.colorable_of_planeDrawing
#print axioms FourColor.CompositionalComplete.supported_source_construction
#print axioms FourColor.CompositionalComplete.supported_source_sweep

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [``FourColor.CompositionalComplete.colorable_of_planeDrawing,
    ``FourColor.CompositionalComplete.supported_source_construction,
    ``FourColor.CompositionalComplete.supported_source_sweep]
  let common := [``FourColor.DiamondFamilyReducibility.reducible_all,
    ``FourColor.DiamondProfileReducibility.reducible001,
    ``FourColor.DiamondProfileReducibility.reducible002,
    ``FourColor.DiamondProfileReducibility.reducible004,
    ``FourColor.DiamondProfileReducibility.transferred001,
    ``FourColor.KempeBoundarySplit.repairs_collapse,
    ``FourColor.DiamondSplitRepair.reconstruct,
    ``FourColor.DiamondProfileCertificate.repair,
    ``FourColor.DiamondProfile.good_supports,
    ``FourColor.DiamondProfileReducibility.supports_graph,
    ``FourColor.DiamondBoundarySummary.reference002,
    ``Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination.reconstruct,
    ``FourColor.CompositionalComplete.reducibility,
    ``FourColor.exclude5, ``FourColor.exclude6, ``FourColor.exclude7,
    ``FourColor.exclude8, ``FourColor.Orbit9.exclude9, ``FourColor.Orbit10.exclude10,
    ``FourColor.Orbit11.exclude11, ``FourColor.ClassicalAssembly.no_embedded_reduction,
    ``FourColor.PeriodicHubcap.fit, ``FourColor.ReflectedHubcap.succeeds,
    ``FourColor.ChargeBound.reflect, ``FourColor.PairChargeBound.reflect_swap,
    ``FourColor.Hubcap.charge_le]
  for rootName in roots do
    let mut seen : NameSet := {}
    let mut todo := [rootName]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in common do
      unless seen.contains name do
        throwError m!"Required dependency {name} is missing from {rootName}"
    for i in List.range 633 do
      let digits := toString i
      let suffix := String.ofList (List.replicate (3 - digits.length) '0') ++ digits
      let bulk := Name.str (Name.str `FourColor.Bulk ("Cfg" ++ suffix)) "reducible"
      let hybrid := Name.str (Name.str `FourColor.Bulk ("Hyb" ++ suffix)) "reducible"
      if i == 0 then
        unless seen.contains ``FourColor.DiamondProfileReducibility.reducible001 do
          throwError m!"Configuration 1's transferred repair is not consumed by {rootName}"
      else if i == 1 then
        unless seen.contains ``FourColor.DiamondProfileReducibility.reducible002 do
          throwError m!"Configuration 2's profile repair is not consumed by {rootName}"
      else if i == 3 then
        unless seen.contains ``FourColor.DiamondProfileReducibility.reducible004 do
          throwError m!"Configuration 4's profile repair is not consumed by {rootName}"
      else
        unless seen.contains bulk || seen.contains hybrid do
          throwError m!"Configuration {i} is not consumed by {rootName}"
    for name in seen.toList do
      if (`FourColor.Bulk.Cfg000).isPrefixOf name || (`FourColor.Bulk.Cfg001).isPrefixOf name ||
          (`FourColor.Bulk.Cfg003).isPrefixOf name ||
          name == ``FourColor.DiamondSplitRepair.base_repair ||
          name == ``FourColor.DiamondBoundaryRepair.repair ||
          name == ``FourColor.DiamondJointRepair.contract_repair ||
          name == ``FourColor.reducible_all || name == ``FourColor.reducible_block_0 then
        throwError m!"Superseded diamond certificate dependency in {rootName}: {name}"
    for i in [22, 125, 276, 295, 359, 732, 754, 758, 762, 858, 862, 950, 1589, 1591, 1609, 1767, 1779, 1821, 2097, 2201, 2208, 2340, 2446, 2458, 2692, 2900, 3312, 3336, 3344, 3384, 3508, 3556] do
      let name := Name.str `FourColor.Orbit9 s!"f9_{i}"
      unless seen.contains name do
        throwError m!"Shared semantic hubcap {name} is missing from {rootName}"
    for i in [28, 69, 89, 144, 233, 253, 620, 822, 835, 917, 924, 951, 998, 1013, 1042, 1056, 1082, 1100, 1101, 1106, 1110] do
      let name := Name.str `FourColor.Orbit10 s!"f10_{i}"
      unless seen.contains name do
        throwError m!"Shared semantic hubcap {name} is missing from {rootName}"
    for i in [76, 81, 89, 98, 128, 170, 193, 255, 291, 298, 304, 308, 317] do
      let name := Name.str `FourColor.Orbit11 s!"f11_{i}"
      unless seen.contains name do
        throwError m!"Shared semantic hubcap {name} is missing from {rootName}"
    let geometry := if rootName == ``FourColor.CompositionalComplete.colorable_of_planeDrawing then
        [``FourColor.PlaneDrawing.core_eq_openStar,
          ``FourColor.PlaneDrawing.midpoint_mem_site_iff,
          ``Mettapedia.Topology.NearestRegions.isConnected_region]
      else [``FourColor.Hypermap.fourColorable_of_small_unavoidability,
        ``FourColor.SourceConstruction.sourceMap_planar,
        ``FourColor.SourceConstruction.sourceMap_bridgeless,
        ``FourColor.SourceConstruction.taitColoring,
        ``Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring.edgeColoringOfDartColor]
    for name in geometry do
      unless seen.contains name do
        throwError m!"Required geometric dependency {name} is missing from {rootName}"
    if rootName == ``FourColor.CompositionalComplete.supported_source_construction then
      unless seen.contains ``Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT.class_represented do
        throwError "The exact source construction is not consumed"
    if rootName == ``FourColor.CompositionalComplete.supported_source_sweep then
      unless seen.contains ``Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT.encoded_support_iff do
        throwError "The exact sweep semantics is not consumed"
  for name in [`FourColor.fourColorTheorem, `FourColor.reducibility,
      `FourColor.exclude9, `FourColor.exclude10, `FourColor.exclude11, `FourColor.f10_128, `FourColor.f10_242,
      `FourColor.Orbit10.f10_242, `FourColor.HalfTurnHubcap.fit] do
    if env.contains name then
      throwError m!"Superseded reference theorem is present: {name}"
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
  for stem in ["c11_76_3", "c11_76_4", "c11_76_9", "c11_76_10", "c11_76_11",
      "c11_81_5", "c11_81_6", "c11_81_7", "c11_81_10", "c11_81_11",
      "c11_89_4", "c11_89_5", "c11_89_9", "c11_89_10", "c11_89_11",
      "c11_98_6", "c11_98_7", "c11_98_8", "c11_98_9", "c11_98_11",
      "c11_128_4", "c11_128_5", "c11_128_8", "c11_128_9",
      "c11_170_4", "c11_170_5", "c11_170_6", "c11_170_9",
      "c11_193_5", "c11_193_6", "c11_193_7", "c11_193_8",
      "c11_255_3", "c11_255_8", "c11_255_9", "c11_255_10", "c11_255_11",
      "c11_291_4", "c11_291_5", "c11_291_6", "c11_291_10", "c11_291_11",
      "c11_298_4", "c11_298_5", "c11_298_9", "c11_298_10", "c11_298_11",
      "c11_304_3", "c11_304_4", "c11_304_9", "c11_304_10", "c11_304_11",
      "c11_308_3", "c11_308_8", "c11_308_9", "c11_308_10", "c11_308_11",
      "c11_317_7", "c11_317_8", "c11_317_9", "c11_317_10", "c11_317_11"] do
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
  logInfo m!"Complete assembly: audited {count} imported public declarations."
  logInfo "All three endpoint closures consume 630 reference certificates, joint-profile repair, \
    boundary-split transfer, and seven arity proofs."
  logInfo "Original certificates for configurations 1, 2 and 4 are absent from all endpoint closures."
  logInfo "All three endpoint closures consume the shared charge proofs and geometric reconstruction."
  logInfo "All 236 superseded checker declarations and the original unconditional theorem are absent."
