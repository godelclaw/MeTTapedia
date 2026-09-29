import Mettapedia.GraphTheory.FourColor.CubicCycleIncidence
import Lean.Util.CollectAxioms

/-! Dependency audit of cycle incidence, uniform orientation and exact port return. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CycleBoundaryOrientation.side_face, []),
    (``CycleBoundaryOrientation.constant_of_cofacial_ports,
      [``CycleBoundaryOrientation.side_face]),
    (``CycleBoundaryOrientation.exists_turn, []),
    (``CycleBoundaryOrientation.Incidence.uniform_rotation,
      [``CycleBoundaryOrientation.constant_of_cofacial_ports,
        ``CycleBoundaryOrientation.exists_turn]),
    (``CycleBoundaryOrientation.Incidence.returnCode_of_uniform_rotation,
      [``PermutationFirstReturnRestriction.nextHit_eq_of_returnArc,
        ``CycleBoundaryOrientation.face_port_twice,
        ``CycleBoundaryOrientation.face_port_internal]),
    (``OpenTangleVertexSideReturn.ports_cofacial_of_planarBond,
      [``GoertzelV24CanonicalHubCyclicity.orbitCount_hubRotation_eq_one_of_closedSideSpherical,
        ``GoertzelV24CanonicalHubClosure.closedSideSpherical_canonical_of_planarBond,
        ``OpenTangleVertexSideReturn.returnCode_eq]),
    (``PlanarCycleBoundaryRecognition.uniform_geometry_of_planarBond,
      [``CycleBoundaryOrientation.Incidence.uniform_rotation,
        ``CycleBoundaryOrientation.Incidence.returnCode_of_uniform_rotation,
        ``OpenTangleVertexSideReturn.ports_cofacial_of_planarBond]),
    (``CubicCycleIncidence.Frame.incidence,
      [``CubicCycleIncidence.Frame.adjacent_iff,
        ``CubicCycleIncidence.Frame.star_injective,
        ``CubicCycleIncidence.Frame.star_surjective_at,
        ``CubicCycleIncidence.Frame.retained_flip]),
    (``CubicCycleIncidence.Frame.uniform_geometry,
      [``CubicCycleIncidence.Frame.incidence,
        ``CubicCycleIncidence.Frame.connected,
        ``PlanarCycleBoundaryRecognition.uniform_geometry_of_planarBond])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.checkCert_sound, `FourColor.check_reducible_valid,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondConfigurations, `FourColor.DiamondFamilyReducibility,
    `FourColor.DiamondProfileReducibility]
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
        throwError m!"Configuration certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Cycle boundary recognition: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
