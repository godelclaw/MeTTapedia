import MettapediaFourColor.ResidualSeedRepairReconstruction
import Lean.Util.CollectAxioms

/-! # Dependency audit of the compact seed strategy and its witness consumers -/

open Lean Elab Command
open FourColor FourColor.ResidualSeedRepairCertificate

run_cmd do
  let env ← getEnv
  let roots := [``source_edges, ``terminalCheck_sound, ``check_sound, ``coclosure,
    ``checked, ``seed_word, ``seed_repair, ``physical_exterior,
    ``source_boundary, ``seed_not_direct, ``whole_repair]
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
      if root == ``seed_repair then
        [``checked, ``KempeIndexedCertificate.sound,
         ``KempeMaskCertificate.check_sound, ``terminalCheck_sound, ``source_edges]
      else if root == ``physical_exterior then
        [``seed_repair, ``OpenTangleKempeRepair.closed_of_physical_noncrossing,
         ``OpenTangleKempeRepair.trace_iff_coloring]
      else if root == ``seed_not_direct then
        [``ThreeBlockCore.necessary, ``GraphTraceAlignment.align]
      else if root == ``whole_repair then
        [``seed_repair, ``GraphTraceAlignment.align,
         ``ThreeBlockGeometry.ExteriorReading.reconstruct]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Compact residual seed repair: {roots.length} roots; {all.toList.length} declarations."
