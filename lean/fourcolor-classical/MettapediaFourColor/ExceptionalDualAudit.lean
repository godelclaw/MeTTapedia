import MettapediaFourColor.MinimalExceptionalEmbedding
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor
open GoertzelV24MinimalDualTriangleClassification GoertzelV24FourEdgeCutGluing

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ActualDualRotation.dual_endpoints_injective,
      [``ActualDualRotation.shared_of_boundaries]),
    (``ActualDualRotation.dual_adj_iff,
      [``GoertzelV24FaceOrbitIncidence.orbitFaceBoundary]),
    (``ActualDualRotation.data_face_step,
      [``GoertzelV24DualRotationSystem.rotationSystem_phi]),
    (``ActualDualRotation.cyclic,
      [``GoertzelV24OrderedCutFaceReturnProfile.permCongr_sameCycle_iff]),
    (``ActualDualRotation.triangular,
      [``ActualDualRotation.data_face_step, ``PhysicalForkCodeFaces.cubic3_of]),
    (``ActualDualRotation.corner_at_vertex,
      [``ActualDualRotation.data_step, ``PhysicalForkCodeFaces.cubic3_of]),
    (``ActualDualRotation.face_mem_vertex_triangle,
      [``PhysicalForkCodeFaces.Cubic3.fiber]),
    (``ActualDualRotation.corner_of_three_members,
      [``ExceptionalCoreOrientation.Corner.rotate]),
    (``MinimalExceptionalEmbedding.graph_eq_coverage_dual,
      [``ActualDualRotation.dual_adj_iff]),
    (``MinimalExceptionalEmbedding.triangle_facial,
      [``exists_singleton_primalCut_of_dual_triangle,
       ``cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample,
       ``ActualDualRotation.corner_at_vertex, ``ActualDualRotation.face_mem_vertex_triangle,
       ``ActualDualRotation.corner_of_three_members]),
    (``MinimalExceptionalEmbedding.joint_injective,
      [``MinimalExceptionalEmbedding.triangle_facial,
       ``ExceptionalCoreCollision.collision_nonfacial]),
    (``MinimalExceptionalEmbedding.source_core_injective,
      [``ExceptionalCore.jointReading, ``ExceptionalCore.coreHom,
       ``ExceptionalCoreOrientation.joint_preserves_turns,
       ``ExceptionalCoreLocalInjectivity.joint_neighbor_injective,
       ``MinimalExceptionalEmbedding.triangle_facial,
       ``ExceptionalCoreCollision.collision_nonfacial])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec]
  let mut all : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Missing dependency {name} in {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) || name.toString.startsWith "FourColor.Bulk.Cfg" ||
          name.toString.startsWith "FourColor.Bulk.Hyb" then
        throwError m!"Complete theorem or original catalogue certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Minimal exceptional embedding: {roots.length} roots; \
    {all.toList.length} declarations; actual dual rotation, singleton separation and \
    source core injectivity; no complete theorem or original rank certificate."
