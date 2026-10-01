import MettapediaFourColor.ExceptionalCore
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ExceptionalPattern.source_valid, [``ExceptionalPattern.source]),
    (``ExceptionalPattern.central_word_gap, [``ExceptionalPattern.prescribed]),
    (``ExceptionalPattern.Occurrence.central_covers,
      [``ExceptionalPattern.Occurrence.central_pow, ``ExceptionalPattern.Occurrence.degree]),
    (``ExceptionalPattern.Occurrence.seven_previous_two,
      [``ExceptionalPattern.Occurrence.central_covers, ``ExceptionalPattern.central_word_gap]),
    (``ExceptionalPattern.Occurrence.next_centre,
      [``ExceptionalPattern.Occurrence.edge, ``ExceptionalPattern.Occurrence.degree]),
    (``ExceptionalPattern.Occurrence.vertex_near,
      [``ExceptionalPattern.source_routes, ``ExceptionalPattern.Occurrence.edge]),
    (``ExceptionalOverlap.consecutive_adjacent, [``ExceptionalOverlap.Triangular]),
    (``ExceptionalOverlap.closing_edges, [``ExceptionalOverlap.consecutive_adjacent]),
    (``ExceptionalOverlap.closing_degree,
      [``ExceptionalPattern.Occurrence.seven_previous_two, ``ExceptionalPattern.Occurrence.turn]),
    (``ExceptionalOverlap.next_centered, [``ExceptionalPattern.Occurrence.next_centre]),
    (``ExceptionalCore.old_edges, [``ExceptionalCore.input, ``ExceptionalPattern.source]),
    (``ExceptionalCore.new_edges, [``ExceptionalCore.input]),
    (``ExceptionalCore.old_degrees, [``ExceptionalCore.input, ``ExceptionalPattern.source]),
    (``ExceptionalCore.coreHom,
      [``ExceptionalCore.old_edges, ``ExceptionalCore.new_edges, ``ExceptionalOverlap.closing_edges]),
    (``ExceptionalCore.core_degrees,
      [``ExceptionalCore.old_degrees, ``ExceptionalOverlap.closing_degree]),
    (``ExceptionalCore.core_near,
      [``ExceptionalPattern.Occurrence.vertex_near, ``ExceptionalPattern.Occurrence.next_centre]),
    (``ExceptionalCore.jointReading,
      [``ExceptionalCore.coreHom, ``ExceptionalCore.core_degrees]),
    (``ExceptionalCore.joint_support_near,
      [``ExceptionalPattern.Occurrence.vertex_near, ``ExceptionalCore.core_near,
       ``ExceptionalCore.JointReading.first, ``ExceptionalCore.JointReading.second]),
    (``ExceptionalCore.overlap_supply,
      [``ExceptionalOverlap.next_centered, ``ExceptionalCore.jointReading,
       ``ExceptionalCore.coreHom,
       ``ExceptionalCore.core_degrees, ``ExceptionalCore.joint_support_near])]
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
  logInfo m!"Exceptional overlap: {roots.length} roots; {all.toList.length} declarations; \
    source-grounded core geometry, no complete theorem or original rank certificate."
