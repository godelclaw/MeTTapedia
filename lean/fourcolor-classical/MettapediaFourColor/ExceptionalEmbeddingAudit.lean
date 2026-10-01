import MettapediaFourColor.ExceptionalCoreCollision
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ExceptionalCoreOrientation.Corner.rotate, [``ExceptionalOverlap.Triangular]),
    (``ExceptionalCoreOrientation.joint_preserves_turns,
      [``ExceptionalCoreOrientation.turn_partition, ``ExceptionalCoreOrientation.old_turns,
       ``ExceptionalCoreOrientation.closing_corner, ``ExceptionalCoreOrientation.Corner.rotate,
       ``ExceptionalCore.JointReading.realizes]),
    (``ExceptionalCoreLocalInjectivity.corner_chain_injective,
      [``Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation.Data.IsVertexwiseCyclic]),
    (``ExceptionalCoreLocalInjectivity.star_specs, [``ExceptionalCore.input]),
    (``ExceptionalCoreLocalInjectivity.star_steps, [``ExceptionalCore.input]),
    (``ExceptionalCoreLocalInjectivity.joint_neighbor_injective,
      [``ExceptionalCoreLocalInjectivity.corner_chain_injective,
       ``ExceptionalCoreOrientation.joint_preserves_turns, ``ExceptionalCore.Reading.degree]),
    (``ExceptionalCoreCollision.NonfacialTriangle.walk_isCycle,
      [``ExceptionalCoreCollision.NonfacialTriangle.walk]),
    (``ExceptionalCoreCollision.nonfacial_of_flanks,
      [``ExceptionalCoreCollision.corner_left_unique, ``ExceptionalCoreCollision.corner_right_unique]),
    (``ExceptionalCoreCollision.collision_partition, [``ExceptionalCore.input]),
    (``ExceptionalCoreCollision.central_collision,
      [``ExceptionalCoreCollision.nonfacial_of_flanks, ``ExceptionalPattern.Occurrence.turn,
       ``ExceptionalPattern.Occurrence.degree, ``ExceptionalCore.Reading.degree]),
    (``ExceptionalCoreCollision.closing_collision,
      [``ExceptionalCoreCollision.nonfacial_of_flanks, ``ExceptionalPattern.Occurrence.edge,
       ``ExceptionalPattern.Occurrence.turn, ``ExceptionalPattern.Occurrence.degree]),
    (``ExceptionalCoreCollision.collision_nonfacial,
      [``ExceptionalCoreCollision.collision_partition,
       ``ExceptionalCoreLocalInjectivity.joint_neighbor_injective,
       ``ExceptionalCoreCollision.central_collision, ``ExceptionalCoreCollision.closing_collision]),
    (``ExceptionalCoreCollision.injective_or_nonfacial,
      [``ExceptionalCoreCollision.collision_nonfacial]),
    (``ExceptionalCoreCollision.injective_of_local_triangles_facial,
      [``ExceptionalCoreCollision.injective_or_nonfacial]),
    (``ExceptionalCoreCollision.source_core_alternative,
      [``ExceptionalCore.jointReading, ``ExceptionalCore.coreHom, ``ExceptionalCore.core_degrees,
       ``ExceptionalOverlap.closing_degree, ``ExceptionalPattern.Occurrence.vertex_near,
       ``ExceptionalCoreCollision.injective_or_nonfacial])]
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
  logInfo m!"Exceptional embedding alternative: {roots.length} roots; {all.toList.length} declarations; \
    facial transport, local injectivity and collision alternative; no complete theorem or original rank certificate."
