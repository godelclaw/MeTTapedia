import Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair
import Lean.Util.CollectAxioms

/-! Audit the partial Kempe preservation laws and their genuine physical
consumer. The witness is derived from a switched partial exterior and joint
endpoint choices, not a complete source word or the classical theorem. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``RotationPatchKempe.underlying_injective, []),
    (``RotationPatchKempe.colouring_proper, []),
    (``RotationPatchKempe.region_common_web, []),
    (``RotationPatchKempe.colouring_switched, []),
    (``RotationPatchKempe.switched_proper,
      [``GoertzelV24PortTangleCommonKempeWeb.switchRegion_isProper]),
    (``SourcePatchKempe.switched_exterior, []),
    (``TwoCellBoundaryChoice.repair_one_pin, []),
    (``TwoCellPhysicalKempeRepair.source_exterior_proper, []),
    (``TwoCellPhysicalKempeRepair.source_region, []),
    (``TwoCellPhysicalKempeRepair.repaired_source_exterior_proper,
      [``SourcePatchKempe.switched_exterior]),
    (``TwoCellPhysicalKempeRepair.repaired_pins, []),
    (``TwoCellPhysicalKempeRepair.joint_choices, [``TwoCellBoundaryChoice.repair_one_pin]),
    (``TwoCellPhysicalKempeRepair.sourceColour_nonzero,
      [``SourcePatchKempe.switched_exterior]),
    (``TwoCellPhysicalKempeRepair.endpoint_zero, [``TwoCellPhysicalKempeRepair.joint_choices]),
    (``TwoCellPhysicalKempeRepair.endpoint_one, [``TwoCellPhysicalKempeRepair.joint_choices]),
    (``TwoCellPhysicalKempeRepair.sourceColour_proper,
      [``SourcePatchKempe.switched_exterior, ``TwoCellBoundaryChoice.repair_one_pin]),
    (``TwoCellPhysicalKempeRepair.target_tait,
      [``TwoCellPhysicalKempeRepair.sourceColour_proper,
       ``DualTruncateColoring.colouring_nonzero]),
    (``TwoCellPhysicalKempeRepair.exterior_local,
      [``TwoCellCycleObstruction.exterior_stars]),
    (``TwoCellPhysicalKempeRepair.physical_region, []),
    (``TwoCellPhysicalKempeRepair.switched_exterior_proper,
      [``RotationPatchKempe.switched_proper]),
    (``TwoCellPhysicalKempeRepair.reconstructs_physical_switch, []),
    (``TwoCellPhysicalKempeRepair.switched_boundary_word,
      [``TwoCellPhysicalKempeRepair.reconstructs_physical_switch]),
    (``TwoCellPhysicalKempeRepair.selected_edges_count, []),
    (``TwoCellPhysicalKempeRepair.selected_visible, []),
    (``TwoCellPhysicalKempeRepair.selected_changed,
      [``TwoCellPhysicalKempeRepair.physical_region, ``TwoCellPhysicalKempeRepair.selected_visible]),
    (``TwoCellPhysicalKempeRepair.unselected_unchanged, []),
    (``TwoCellPhysicalKempeRepair.successful_repair,
      [``SourcePatchKempe.switched_exterior, ``RotationPatchKempe.switched_proper,
       ``TwoCellBoundaryChoice.repair_one_pin,
       ``TwoCellPhysicalKempeRepair.reconstructs_physical_switch]),
    (``TwoCellPhysicalKempeRepair.every_complete_sweep,
      [``DualTruncateConstructionGSLT.supported_encoded_route,
       ``SourcePatchKempe.switched_exterior, ``TwoCellBoundaryChoice.repair_one_pin])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `AutoBooks, `Lean.ofReduceBool, `sorryAx,
    `Mettapedia.GraphTheory.Basic,
    ``CubicRotationByteCertificate.ProperWord, ``CubicRotationByteCertificate.threeVertexColoring,
    `Mettapedia.GraphTheory.FourColor.DualTruncateBrooksSource,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCyclicSource,
    ``DualTruncateStructuralColoring.source_of_connected_pair,
    ``DualTruncateStructuralColoring.source_of_pairDeletionConnected,
    `Mettapedia.GraphTheory.FourColor.DualTruncateCoupledExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateGeometryExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatchExample,
    `Mettapedia.GraphTheory.FourColor.DualTruncateForestExample]
  let uniform : List Name := [
    `Mettapedia.GraphTheory.FourColor.RotationPatchKempe,
    `Mettapedia.GraphTheory.FourColor.SourcePatchKempe,
    ``TwoCellBoundaryChoice.repair_one_pin]
  let fixtures : List Name := [
    `Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair]
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
        throwError m!"Forbidden proof dependency in {root}: {name}"
      if uniform.any (·.isPrefixOf root) && fixtures.any (·.isPrefixOf name) then
        throwError m!"Finite graph data entered uniform repair law {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Physical two-cell Kempe repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical endpoints and source-colouring suppliers absent; \
    uniform laws independent of the finite graph consumer."
