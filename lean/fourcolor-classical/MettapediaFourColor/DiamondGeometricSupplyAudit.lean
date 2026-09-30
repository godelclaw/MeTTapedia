import MettapediaFourColor.DiamondGeometricSupply
import Lean.Util.CollectAxioms

/-! Dependency and axiom audit of geometric diamond supply. Every branch
must reach its actual class-preserving reduction and smaller-map minimality,
without using the complete Four Colour theorem or original certificates. -/

open Lean Elab Command
open FourColor Mettapedia.GraphTheory Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``PentagonalNeighbourSupply.neighbours_card_index,
      [``GoertzelV24OrbitFaceCyclicOrder.faceOrbitDartEquiv]),
    (``PentagonalNeighbourSupply.exists_flanked_of_three,
      [``PentagonalNeighbourSupply.neighbours_card_index,
       ``PentagonalNeighbourSupply.previous_flank, ``PentagonalNeighbourSupply.next_flank]),
    (``PentagonalNeighbourSupply.sum_neighbours, []),
    (``PentagonalNeighbourSupply.fiftysix_le_of_not_flanked,
      [``PentagonalNeighbourSupply.exists_flanked_of_three,
       ``PentagonalNeighbourSupply.sum_neighbours,
       ``GoertzelV24FaceOrbitIncidence.sum_card_orbitFaceDarts_eq_card_darts]),
    (``DiamondGeometricSupply.classify_flanked,
      [``PentagonalNeighbourSupply.flanked_flip, ``PentagonalNeighbourSupply.last_flank,
       ``PentagonalNeighbourSupply.next_flank]),
    (``DiamondGeometricSupply.of_three_neighbours,
      [``DiamondGeometricSupply.classify_flanked, ``PentagonalNeighbourSupply.exists_flanked_of_three]),
    (``DiamondGeometricSupply.of_card_lt_fiftysix,
      [``DiamondGeometricSupply.classify_flanked,
       ``PentagonalNeighbourSupply.fiftysix_le_of_not_flanked]),
    (``DiamondGeometricSupply.not_in_minimal,
      [``PentagonalDiamondPatch.Tangle.FaceReduction.recognized,
       ``SixPortTreeReplacement.Embedded.strict_reduction,
       ``MixedDiamondPatch.Tangle.FaceReduction.strict_reduction_of_face_pattern,
       ``JointDiamondPatch.Tangle.FaceClearance.boundary_clear,
       ``GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample.smallerColorable]),
    (``DiamondGeometricSupply.neighbours_le_two_of_minimal,
      [``DiamondGeometricSupply.of_three_neighbours, ``DiamondGeometricSupply.not_in_minimal]),
    (``DiamondGeometricSupply.fiftysix_le_vertices_of_minimal,
      [``DiamondGeometricSupply.of_card_lt_fiftysix, ``DiamondGeometricSupply.not_in_minimal]),
    (``DiamondGeometricSupply.fiftysix_le_vertices_of_fullerene_minimal,
      [``DiamondGeometricSupply.fiftysix_le_vertices_of_minimal,
       ``PentagonalNeighbourSupply.shortFaces_of_fullerene,
       ``GoertzelV24OrbitFaceTwoSided.orbitFaceBoundarySimple_of_twoSided])]
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
        throwError m!"Required geometric dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" then
        throwError m!"Superseded repair, catalogue certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond geometric supply: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    original catalogue certificates and complete endpoints absent."
