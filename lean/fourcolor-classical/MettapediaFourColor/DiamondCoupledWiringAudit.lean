import MettapediaFourColor.JointDiamondTangle
import Lean.Util.CollectAxioms

/-! Audit of exact coupled-wiring semantics and actual colouring reconstruction.
The geometric separation and Kempe-closure hypotheses remain explicit.
No ambient-class preservation or coverage conclusion is asserted here. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DiamondCoupledWiring.contractTrace_iff, [``DiamondJointContract.contractTrace_iff, ``DiamondCoupledWiring.ofContract, ``DiamondCoupledWiring.reconstruct_word]),
    (``DiamondCoupledWiring.repair, [``DiamondProfileReducibility.repair004, ``DiamondCoupledWiring.contractTrace_iff]),
    (``DiamondCoupledWiring.forgetting_seam_fails, []),
    (``DiamondCoupledWiring.Rotation.data, []),
    (``DiamondCoupledWiring.Rotation.vertex_count, []),
    (``DiamondCoupledWiring.Rotation.restrict, []),
    (``DiamondCoupledWiring.Rotation.glue, [``GoertzelV24RotationDartColoring.edgeColoringOfDartColor, ``GoertzelV24RotationDartColoring.edgeColoringOfDartColor_edgeOf]),
    (``DiamondCoupledWiring.Rotation.colorable_iff, [``DiamondCoupledWiring.Rotation.restrict, ``DiamondCoupledWiring.Rotation.glue]),
    (``DiamondCoupledWiring.Rotation.compatible_history, [``DiamondCoupledWiring.Rotation.colorable_iff, ``DiamondProfileReducibility.compatible_history]),
    (``JointDiamondPatch.Tangle.cubic, []),
    (``JointDiamondPatch.Tangle.reference_geometry, []),
    (``JointDiamondPatch.Tangle.colouring_valid, []),
    (``JointDiamondPatch.Tangle.boundary_colouring, [``JointDiamondPatch.Tangle.boundary_reference]),
    (``JointDiamondPatch.Tangle.vertex_decrease, []),
    (``JointDiamondPatch.Tangle.colorable_of_wiring, [``DiamondCoupledWiring.Rotation.colorable_iff, ``DiamondProfileReducibility.repair004, ``JointDiamondPatch.Tangle.colouring_valid, ``OpenTangleClosedWitness.glueOpen])]
  let forbidden : List Name := [
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondSplitRepair.base_repair, `FourColor.DiamondBoundaryRepair.repair,
    `FourColor.DiamondJointRepair.contract_repair, `FourColor.coversRec,
    `FourColor.coversRec_sound]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" then
        throwError m!"Superseded repair, catalogue certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Coupled-wiring reconstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    original catalogue certificates, superseded repairs and complete endpoints absent."
