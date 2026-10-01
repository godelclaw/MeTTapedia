import Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples
import Lean.Util.CollectAxioms

/-! Audit exact source-to-edge transport, shared reconstruction and the
three actual consumers. Uniform laws exclude finite graph data; whole
source-colouring suppliers and classical theorem endpoints are absent. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``DualTruncateKempeTransport.star_switch, []),
    (``DualTruncateKempeTransport.slotMask_active, []),
    (``DualTruncateKempeTransport.slotMask_closed, []),
    (``DualTruncateKempeTransport.physical_region,
      [``DualTruncateKempeTransport.slotMask_closed]),
    (``DualTruncateKempeTransport.exact_effect,
      [``DualTruncateKempeTransport.star_switch]),
    (``DualTruncateKempeTransport.physical_region_after,
      [``DualTruncateKempeTransport.physical_region]),
    (``DualTruncateKempeTransport.exact_effect_after,
      [``DualTruncateKempeTransport.exact_effect]),
    (``TwoCellSourceRepair.Frame.insert_proper, []),
    (``TwoCellSourceRepair.Frame.complete, []),
    (``TwoCellSourceRepair.Frame.reconstructed_extends, []),
    (``TwoCellSourceRepair.repaired_joint_choices,
      [``TwoCellBoundaryChoice.repair_one_pin]),
    (``TwoCellSourceRepair.repairedSource,
      [``TwoCellSourceRepair.Frame.complete, ``SourcePatchKempe.switched_exterior,
       ``TwoCellBoundaryChoice.repair_one_pin]),
    (``TwoCellSourceRepairExamples.Prism.no_original_joint_choices, []),
    (``TwoCellSourceRepairExamples.Prism.target_tait,
      [``TwoCellSourceRepair.repairedSource, ``DualTruncateColoring.colouring_nonzero]),
    (``TwoCellSourceRepairExamples.Prism.physical_region,
      [``DualTruncateKempeTransport.physical_region]),
    (``TwoCellSourceRepairExamples.Prism.reconstructs,
      [``TwoCellSourceRepair.Frame.reconstructed_extends, ``DualTruncateKempeTransport.exact_effect]),
    (``TwoCellSourceRepairExamples.Dodeca.Single.target_tait,
      [``TwoCellSourceRepair.repairedSource, ``DualTruncateColoring.colouring_nonzero]),
    (``TwoCellSourceRepairExamples.Dodeca.Single.physical_region,
      [``DualTruncateKempeTransport.physical_region]),
    (``TwoCellSourceRepairExamples.Dodeca.Single.reconstructs,
      [``TwoCellSourceRepair.Frame.reconstructed_extends, ``DualTruncateKempeTransport.exact_effect]),
    (``TwoCellSourceRepairExamples.Dodeca.History.no_original_joint_choices, []),
    (``TwoCellSourceRepairExamples.Dodeca.History.exterior₁_proper,
      [``SourcePatchKempe.switched_exterior]),
    (``TwoCellSourceRepairExamples.Dodeca.History.exterior₂_proper,
      [``SourcePatchKempe.switched_exterior]),
    (``TwoCellSourceRepairExamples.Dodeca.History.physical_region₁,
      [``DualTruncateKempeTransport.physical_region]),
    (``TwoCellSourceRepairExamples.Dodeca.History.physical_region₂,
      [``DualTruncateKempeTransport.physical_region_after,
       ``DualTruncateKempeTransport.exact_effect]),
    (``TwoCellSourceRepairExamples.Dodeca.History.effect₂,
      [``DualTruncateKempeTransport.exact_effect_after]),
    (``TwoCellSourceRepairExamples.Dodeca.History.target_tait,
      [``TwoCellSourceRepair.Frame.complete, ``SourcePatchKempe.switched_exterior,
       ``DualTruncateColoring.colouring_nonzero]),
    (``TwoCellSourceRepairExamples.Dodeca.History.reconstructs,
      [``TwoCellSourceRepair.Frame.reconstructed_extends,
       ``DualTruncateKempeTransport.exact_effect_after]),
    (``TwoCellSourceRepairExamples.Dodeca.History.every_complete_sweep,
      [``DualTruncateConstructionGSLT.supported_encoded_route,
       ``TwoCellSourceRepair.Frame.complete, ``SourcePatchKempe.switched_exterior])]
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
    `Mettapedia.GraphTheory.FourColor.DualTruncateForestExample,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair.sourceWitness,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair.sourceColour_proper,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair.target_tait]
  let uniform : List Name := [
    `Mettapedia.GraphTheory.FourColor.RotationPatchKempe,
    `Mettapedia.GraphTheory.FourColor.SourcePatchKempe,
    ``TwoCellBoundaryChoice.repair_one_pin,
    `Mettapedia.GraphTheory.FourColor.DualTruncateKempeTransport,
    `Mettapedia.GraphTheory.FourColor.TwoCellSourceRepair]
  let fixtures : List Name := [
    `Mettapedia.GraphTheory.FourColor.TwoCellCycleObstruction,
    `Mettapedia.GraphTheory.FourColor.TwoCellPhysicalKempeRepair,
    `Mettapedia.GraphTheory.FourColor.DualTruncateSourceDomainExample,
    `Mettapedia.GraphTheory.FourColor.TwoCellSourceRepairExamples]
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
  logInfo m!"Uniform two-cell source repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical endpoints and source-colouring suppliers absent; \
    uniform laws independent of the finite graph consumer."
