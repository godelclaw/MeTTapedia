import MettapediaFourColor.TwoDiamondCycleFaceTransport
import Lean.Util.CollectAxioms

/-! Audit of conserved-field integration and its actual diamond-replacement
consumer. Neither a complete colouring theorem nor a configuration colour
certificate may occur in these dependency cones. -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``SourceConstruction.reference_mirror_colouring_iff, [``Hypermap.Coloring.of_mirror]),
    (``SourceConstruction.mirror_node_difference, [``SourceConstruction.faceColor_rho]),
    (``RotationConservedFacePotential.exists_facePotential,
      [``GoertzelV24RotationCycleSpace.range_faceBoundaryLinearMap_eq_cycleSpace]),
    (``RotationConservedFacePotential.potentials_differ_by_constant,
      [``GoertzelV24FaceBoundaryLinearAlgebra.mem_ker_orbitFaceBoundaryLinearMap_iff_constant]),
    (``RotationConservedFacePotential.potential_unique_at_root,
      [``RotationConservedFacePotential.potentials_differ_by_constant]),
    (``SourceConstruction.reference_colouring_of_conserved,
      [``RotationConservedFacePotential.exists_facePotential]),
    (``SourceConstruction.reference_colouring_of_tait,
      [``SourceConstruction.reference_colouring_of_conserved,
       ``RotationConservedFacePotential.conserved_of_tait]),
    (``SourceConstruction.tait_round_trip,
      [``SourceConstruction.reference_colouring_of_tait, ``SourceConstruction.taitColoring_dart]),
    (``TwoDiamondCycleReplacement.smaller_joint_face_witness,
      [``SourceConstruction.tait_round_trip, ``OpenTangleClosedWitness.restrictOpen,
       ``TwoDiamondCycleReplacement.replacement_class])]
  let forbidden : List Name := [
    `FourColor.Bulk, `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all, `FourColor.reducible_block_0]
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
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Colour certificate or complete theorem in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Exact face/edge transport audit: {roots.length} roots; \
    {inspected.toList.length} declarations; no configuration colour certificates."
