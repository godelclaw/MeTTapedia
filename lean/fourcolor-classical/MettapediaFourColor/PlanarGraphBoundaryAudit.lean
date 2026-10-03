import MettapediaFourColor.ResidualSeedPlanarReconstruction
import Lean.Util.CollectAxioms

/-! # Audit of geometric exterior closure and the residual reconstruction -/

open Lean Elab Command
open FourColor PlanarGraphBoundaryClosure ResidualSeedRepairCertificate

run_cmd do
  let env ← getEnv
  let roots := [``coloring_iff, ``ringTrace_iff, ``face_ne, ``closed, ``rotation_closed,
    ``whole_repair_of_planar_disk]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : NameSet := {}
  for root in roots do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    let required :=
      if root == ``closed || root == ``rotation_closed then
        [``Hypermap.Kempe_map, ``ringTrace_iff]
      else if root == ``ringTrace_iff then
        [``SimpleGraphBridge.coloringOfDarts_apply_dart,
         ``SimpleGraphBridge.graphColoring_of_vertexColoring]
      else if root == ``whole_repair_of_planar_disk then
        [``rotation_closed, ``seed_repair, ``GraphTraceAlignment.align,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Planar exterior closure: {roots.length} roots; {all.toList.length} declarations."
