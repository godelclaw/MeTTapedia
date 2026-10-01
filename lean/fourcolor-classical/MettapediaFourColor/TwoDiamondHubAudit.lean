import MettapediaFourColor.TwoDiamondHubColoring
import Lean.Util.CollectAxioms

/-! Audit of the exact capped-boundary observation and unconditional
shared-tip disk-to-cycle reconstruction. Geometry and transport exclude all
colour certificates. Reconstruction retains only the named configuration-6
base; the complete Four Colour theorem is excluded throughout. -/

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``OpenTangleBoundaryHub.boundary_return, []),
    (``OpenTangleBoundaryHub.euler_mass, [``OpenTangleBoundaryHub.face_count]),
    (``SourceConstruction.sourceMap_planar_of_vertexCovered, []),
    (``SourceConstruction.dartTrace_ne_rho_of_three, []),
    (``OpenTangleKempeRepair.glue_of_closed_observation, [``OpenTangleClosedWitness.glueOpen]),
    (``TwoDiamondBoundaryHub.planar,
      [``SourceConstruction.sourceMap_planar_of_vertexCovered,
       ``OpenTangleInternalReplacement.replacement_structural,
       ``OpenTanglePortReplacement.euler_eq_iff_mass]),
    (``TwoDiamondBoundaryHub.exterior_faces,
      [``OpenTanglePortReplacement.exterior_sameCycle_iff]),
    (``TwoDiamondBoundaryHub.two_sided, [``TwoDiamondBoundaryHub.exterior_faces]),
    (``TwoDiamondBoundaryHub.reference_geometry,
      [``TwoDiamondBoundaryHub.planar, ``TwoDiamondBoundaryHub.outside_three]),
    (``TwoDiamondBoundaryHub.reference_closed,
      [``Hypermap.Kempe_map, ``TwoDiamondBoundaryHub.reference_geometry]),
    (``TwoDiamondHubColoring.lift_colouring,
      [``TwoDiamondHubColoring.project_face, ``TwoDiamondHubColoring.cycle_exterior_faces]),
    (``TwoDiamondHubColoring.read_proper,
      [``SourceConstruction.dartTrace_ne_rho_of_three, ``TwoDiamondBoundaryHub.outside_three]),
    (``TwoDiamondHubColoring.read_word, [``SourceConstruction.faceColor_rho]),
    (``TwoDiamondHubColoring.read_trace,
      [``TwoDiamondHubColoring.read_word, ``TwoDiamondHubColoring.read_proper]),
    (``TwoDiamondHubColoring.reconstruct,
      [``SourceConstruction.reference_colouring_of_tait,
       ``TwoDiamondHubColoring.lift_colouring, ``TwoDiamondHubColoring.read_trace,
       ``TwoDiamondBoundaryHub.reference_closed,
       ``OpenTangleKempeRepair.glue_of_closed_observation,
       ``TwoDiamondTangle.open_repair, ``TwoDiamondTangle.colouring_valid,
       ``Bulk.Cfg005.hgood]),
    (``TwoDiamondHubColoring.strict_reduction,
      [``TwoDiamondCycleReplacement.replacement_class,
       ``TwoDiamondCycleReplacement.whole_vertex_loss,
       ``TwoDiamondHubColoring.reconstruct])]
  let repairRoots : List Name := [``TwoDiamondHubColoring.reconstruct,
    ``TwoDiamondHubColoring.strict_reduction]
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
      if (!repairRoots.contains root && (`FourColor.Bulk).isPrefixOf name) ||
          (name.toString.startsWith "FourColor.Bulk.Cfg" &&
            !(`FourColor.Bulk.Cfg005).isPrefixOf name) then
        throwError m!"Unexpected colour certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Boundary-hub reconstruction audit: {roots.length} roots; \
    {inspected.toList.length} declarations; exact closed-observation reconstruction; only the retained configuration-6 base allowed."
