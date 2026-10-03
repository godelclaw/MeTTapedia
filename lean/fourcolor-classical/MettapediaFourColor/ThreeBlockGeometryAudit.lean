import MettapediaFourColor.ThreeBlockReconstruction
import Lean.Util.CollectAxioms

/-!
# Dependency audit for complementary-path reconstruction

The whole-map consumer must retain the spherical face-potential argument,
the physical component operation, and the symbolic core witness. Imported
classical reducibility tables and complete Four Colour endpoints are excluded.
The retained concrete sphere has a separate program instantiation; this audit
checks the parameterized Lean theorems and their dependencies.
-/

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots := [
    ``Mettapedia.GraphTheory.FourColor.PrimalPathSeparation.labels_eq_along_walk,
    ``Mettapedia.GraphTheory.FourColor.PrimalPathSeparation.labels_eq_of_disjoint_walk,
    ``FourColor.ThreeBlockGeometry.Patch.closed_parity,
    ``FourColor.ThreeBlockGeometry.Patch.separated_faces,
    ``FourColor.ThreeBlockGeometry.Patch.no_crossing_paths,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.port_adj,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.excludes_first_runs,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.repair_of_path,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.reconstruct,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.strict_decrease,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.exact_decrease,
    ``FourColor.ThreeBlockGeometry.ExteriorReading.whole_repair_of_path]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.WheelRepairData, `FourColor.ExceptionalRepairData]
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
    if root == ``FourColor.ThreeBlockGeometry.ExteriorReading.whole_repair_of_path then
      for needed in [``FourColor.ThreeBlockGeometry.Patch.no_crossing_paths,
          ``Mettapedia.GraphTheory.FourColor.GoertzelV24WalkFaceParityCut.exists_orbitFaceLabeling_eq_walkEdgeParity,
          ``FourColor.ThreeBlockCore.assignment_proper,
          ``SimpleGraph.Coloring.swapOnKempeComponent,
          ``FourColor.ThreeBlockGeometry.ExteriorReading.reconstruct] do
        unless seen.contains needed do
          throwError m!"Missing consumer dependency: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Three-block geometry: {roots.length} roots; {all.toList.length} declarations."
