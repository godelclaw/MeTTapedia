import MettapediaFourColor.TwoDiamondCycleReplacement
import Lean.Util.CollectAxioms

/-! Audit of actual source incidence, geometry in arbitrary exteriors, joint
GSLT witnesses and conditional colouring reconstruction. The retained base
for configuration 6 is required by repair and excluded from pure geometry.
Neither general exterior closure nor occurrence coverage is asserted. -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``TwoDiamondTangle.original_selected, []),
    (``TwoDiamondTangle.reference_embedding,
      [``TwoDiamondConfigurations.numbered003, ``TwoDiamondTangle.original_incidence]),
    (``TwoDiamondTangle.colouring_valid, []),
    (``TwoDiamondTangle.joint_construction,
      [``TwoDiamondCompositionGSLT.witness, ``TwoDiamondTangle.colouring_valid]),
    (``TwoDiamondTangle.open_repair,
      [``TwoDiamondSplitRepair.transferred_repair, ``TwoDiamondTangle.colouring_valid]),
    (``TwoDiamondTangle.cubic, []),
    (``TwoDiamondTangle.rotation_cyclic, []),
    (``TwoDiamondTangle.piece_connected, []),
    (``TwoDiamondTangle.piece_bridgeless, []),
    (``TwoDiamondTangle.piece_returnCode, [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc]),
    (``TwoDiamondTangle.piece_eulerMass, [``TwoDiamondTangle.piece_face_count]),
    (``TwoDiamondCycleReplacement.cycle_returnCode, [``CycleCap.encode_cap]),
    (``TwoDiamondCycleReplacement.replacement_class,
      [``OpenTangleInternalReplacement.replacement_structural,
       ``OpenTanglePortReplacement.euler_eq_iff_mass,
       ``TwoDiamondTangle.piece_bridgeless, ``TwoDiamondTangle.piece_returnCode,
       ``TwoDiamondTangle.piece_eulerMass, ``CycleCap.cap_connected_bridgeless]),
    (``TwoDiamondCycleReplacement.whole_vertex_loss, []),
    (``TwoDiamondCycleReplacement.replacement_strict, []),
    (``TwoDiamondCycleReplacement.reconstruct,
      [``OpenTangleClosedWitness.restrictOpen, ``OpenTangleClosedWitness.glueOpen,
       ``TwoDiamondTangle.open_repair, ``Bulk.Cfg005.hgood]),
    (``TwoDiamondCycleReplacement.reconstruct_of_noncrossing,
      [``OpenTangleKempeRepair.closed_of_physical_noncrossing,
       ``TwoDiamondCycleReplacement.reconstruct])]
  let geometric : List Name := [
    ``TwoDiamondTangle.original_selected, ``TwoDiamondTangle.reference_embedding,
    ``TwoDiamondTangle.colouring_valid, ``TwoDiamondTangle.joint_construction,
    ``TwoDiamondTangle.cubic, ``TwoDiamondTangle.rotation_cyclic,
    ``TwoDiamondTangle.piece_connected, ``TwoDiamondTangle.piece_bridgeless,
    ``TwoDiamondTangle.piece_returnCode, ``TwoDiamondTangle.piece_eulerMass,
    ``TwoDiamondCycleReplacement.cycle_returnCode,
    ``TwoDiamondCycleReplacement.replacement_class,
    ``TwoDiamondCycleReplacement.whole_vertex_loss,
    ``TwoDiamondCycleReplacement.replacement_strict]
  let forbidden : List Name := [
    `FourColor.Bulk.Cfg000, `FourColor.Bulk.Cfg001, `FourColor.Bulk.Cfg002,
    `FourColor.Bulk.Cfg003, `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
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
        throwError m!"Superseded certificate or complete theorem in {root}: {name}"
      if geometric.contains root && (`FourColor.Bulk).isPrefixOf name then
        throwError m!"Colour certificate in geometric or construction root {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Shared-tip cycle audit: {roots.length} roots; \
    {inspected.toList.length} declarations; geometric replacement independent of colour certificates."
