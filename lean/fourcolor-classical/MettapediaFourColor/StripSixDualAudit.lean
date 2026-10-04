import MettapediaFourColor.StripSixDualExample
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``DualDegreePattern.face_card, []),
    (``DualDegreePattern.hypermap_dual, []),
    (``DualDegreePattern.diamond,
      [``DualDegreePattern.face_card, ``DualDegreePattern.face_power]),
    (``StripSixDualExample.darts,
      [``StripSixDualExample.forward_check, ``StripSixDualExample.backward_check]),
    (``StripSixDualExample.vertex_step, [``StripSixDualExample.step_check]),
    (``StripSixDualExample.face_step, [``StripSixDualExample.vertex_step]),
    (``StripSixDualExample.planar,
      [``DualDegreePattern.hypermap_dual, ``StripSixOrderExample.planar]),
    (``StripSixDualExample.cubic, [``GraphRotationRows.Rows.degree]),
    (``StripSixDualExample.dart_count, [``StripSixOrderExample.dart_count]),
    (``StripSixDualExample.face_pattern,
      [``DualDegreePattern.diamond, ``StripSixDualExample.neighbour_degrees]),
    (``StripSixDualExample.alternative_excludes_minimal,
      [``DualDegreePattern.not_in_minimal, ``DualDegreePattern.diamond,
       ``PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern,
       ``SixPortTreeReplacement.Embedded.size_decrease, ``DiamondProfileReducibility.repair001])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  -- The shared profile uses generic digit decoding from Bulk, but no Cfg certificates.
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk.Cfg,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.ResidualSeedRepairCertificate, `FourColor.StripSixOrderExample.state,
    `FourColor.StripSixOrderExample.source, `FourColor.StripSixOrderExample.reconstructed,
    `FourColor.StripSixOrderExample.no_two_phases]
  let mut all : NameSet := {}
  for (root, required) in contracts do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) ||
            name.toString.startsWith "FourColor.Bulk.Cfg" then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exact dual alternative: {contracts.length} roots; \
    {all.toList.length} declarations. Shared diamond profile retained."
