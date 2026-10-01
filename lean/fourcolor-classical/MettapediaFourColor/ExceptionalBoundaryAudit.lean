import MettapediaFourColor.ExceptionalBoundaryReconstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FacialStarCompletion.across_edge, []),
    (``FacialStarCompletion.pow_degree, []),
    (``FacialStarCompletion.covers, []),
    (``ExceptionalBoundaryCompletion.around_core,
      [``ExceptionalCoreOrientation.joint_preserves_turns]),
    (``ExceptionalBoundaryCompletion.row_agrees,
      [``ExceptionalBoundaryCompletion.outer_seam,
       ``ExceptionalBoundaryCompletion.ring_position_cases]),
    (``ExceptionalBoundaryCompletion.hom,
      [``ExceptionalBoundaryCompletion.edge_reading,
       ``ExceptionalBoundaryCompletion.row_agrees]),
    (``ExceptionalBoundaryOccurrence.full_turn,
      [``ExceptionalBoundaryCompletion.around_next,
       ``ExceptionalBoundaryCompletion.row_agrees]),
    (``ExceptionalBoundaryOccurrence.star_covers,
      [``FacialStarCompletion.covers, ``ExceptionalBoundaryCompletion.row_agrees]),
    (``ExceptionalBoundaryOccurrence.ring_outside_core,
      [``ExceptionalBoundaryOccurrence.around_injective]),
    (``ExceptionalBoundaryOccurrence.sourceHom,
      [``ExceptionalCore.jointReading, ``ExceptionalBoundaryCompletion.hom]),
    (``ExceptionalBoundaryOccurrence.source_ring_outside,
      [``ExceptionalCoreInduced.joint_induced]),
    (``PatchBoundaryGluing.reconstruct, []),
    (``ExceptionalBoundaryReconstruction.reconstruct,
      [``PatchBoundaryGluing.reconstruct,
       ``MinimalExceptionalEmbedding.source_core_injective,
       ``ExceptionalBoundaryOccurrence.source_ring_outside,
       ``ExceptionalBoundaryOccurrence.star_covers,
       ``ExceptionalBoundaryReconstruction.source_spoke_adj]),
    (``ExceptionalBoundaryReconstruction.extension_iff,
      [``ExceptionalBoundaryReconstruction.reconstruct,
       ``ExceptionalBoundaryOccurrence.sourceHom])]
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
  logInfo m!"Exceptional boundary completion: {roots.length} roots; \
    {all.toList.length} declarations; actual shared ports, full star coverage and joint \
    colouring reconstruction; no complete theorem or original rank certificate."
