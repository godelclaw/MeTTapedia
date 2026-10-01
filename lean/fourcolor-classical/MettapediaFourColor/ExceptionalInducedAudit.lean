import MettapediaFourColor.ExceptionalCoreInduced
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor
open GoertzelV24MinimalDualFourCycleClassification

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FacialPatchInduced.corner_chain_successor,
      [``SimpleGraphDartRotation.Data.IsVertexwiseCyclic]),
    (``FacialPatchInduced.reflects_of_short_paths, []),
    (``ExceptionalCoreInduced.star_strict, [``ExceptionalCore.input]),
    (``ExceptionalCoreInduced.star_consecutive_adjacent, [``ExceptionalCore.input]),
    (``ExceptionalCoreInduced.short_paths, [``ExceptionalCore.input]),
    (``ExceptionalCoreInduced.joint_reflects_common_neighbor,
      [``FacialPatchInduced.corner_chain_successor,
       ``ExceptionalCoreOrientation.joint_preserves_turns,
       ``ExceptionalCoreInduced.star_strict]),
    (``ExceptionalCoreInduced.four_cycle_chord,
      [``middle_adj_other_of_two_common_neighbors, ``ActualDualRotation.dual_adj_iff]),
    (``ExceptionalCoreInduced.joint_induced,
      [``FacialPatchInduced.reflects_of_short_paths,
       ``ExceptionalCoreInduced.joint_reflects_common_neighbor,
       ``ExceptionalCoreInduced.four_cycle_chord,
       ``MinimalExceptionalEmbedding.joint_injective]),
    (``ExceptionalCoreInduced.source_core_induced,
      [``ExceptionalCore.jointReading, ``ExceptionalCoreInduced.joint_induced,
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
  logInfo m!"Exceptional induced core: {roots.length} roots; \
    {all.toList.length} declarations; facial intervals, short paths and actual source inducedness; \
    no complete theorem or original rank certificate."
