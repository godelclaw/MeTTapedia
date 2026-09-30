import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowWiring
import Lean.Util.CollectAxioms

/-! Audit the two-row colouring component and its actual closed witness
consumer. Free-wire replacement geometry and occurrence coverage remain
separate; neither finite ring stabilization nor a complete Four Colour
endpoint may supply the colouring argument. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ZigzagRing.ShiftedWiring.exists_first_ring,
      [``ZigzagRing.Full.exists_step, ``ZigzagRing.step_iff_of_missing]),
    (``ZigzagRing.ShiftedWiring.two_rows,
      [``ZigzagRing.ShiftedWiring.exists_first_ring,
       ``ZigzagRing.Step.two_ring_shift, ``ZigzagRing.tube_accepts_iff]),
    (``ZigzagRing.ShiftedWiring.closed_reconstruction,
      [``ZigzagRing.ShiftedWiring.two_rows, ``OpenTangleClosedWitness.glue])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor,
    `Mettapedia.GraphTheory.FourColor.GoertzelV24FiveTubeExclusion,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.five_tube_normalize,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.tube_support_eq,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.transfer_adjacent_of_stabilizes,
    `Mettapedia.GraphTheory.FourColor.ZigzagRing.full_transfer_after_word_bound]
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
        throwError m!"Finite stabilization or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Shifted two-row colouring reconstruction: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    finite stabilization certificates and complete classical theorem absent."
