import MettapediaFourColor.ResidualPortPreparationExample
import Lean.Util.CollectAxioms

/-!
# Audit of the free-port supplier and whole-map reconstruction

The final supplier must use the singleton preparation, spherical path
separation, an actual component switch and exact source/exterior gluing.
The retained finite exterior must consume the same preparation theorem.
-/

open Lean Elab Command
open FourColor.ResidualPortPreparation
run_cmd do
  let env ← getEnv
  let roots := [``assignment_proper, ``boundary_assignment, ``prepare, ``finish,
    ``whole_repair_of_free_port, ``whole_repair_or_neighbor,
    ``Example.initial_boundary, ``Example.free_port, ``Example.path_active,
    ``Example.physical_preparation]
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
    let required :=
      if root == ``prepare then [``SimpleGraph.KempeIndependentLift.single_vertex]
      else if root == ``finish then
        [``FourColor.ThreeBlockGeometry.ExteriorReading.excludes_first_runs,
         ``SimpleGraph.kempeStep_swapOnKempeComponent, ``boundary_assignment]
      else if root == ``whole_repair_of_free_port then
        [``prepare, ``finish, ``assignment_proper,
         ``FourColor.ThreeBlockGeometry.ExteriorReading.reconstruct]
      else if root == ``whole_repair_or_neighbor then
        [``whole_repair_of_free_port, ``FourColor.VisiblePortRepair.whole_repair_or_residual]
      else if root == ``Example.physical_preparation then
        [``prepare, ``Example.free_edges, ``Example.path_active]
      else []
    for needed in required do
      unless seen.contains needed do
        throwError m!"Missing load-bearing dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Residual free-port preparation: {roots.length} roots; {all.toList.length} declarations."
