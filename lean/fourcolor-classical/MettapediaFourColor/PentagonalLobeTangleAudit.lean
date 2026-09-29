import MettapediaFourColor.PentagonalLobeTangle
import Lean.Util.FoldConsts

/-!
# Audit of literal pentagonal lobe reconstruction

The physical consumer must use the joint repair, the exact ordered boundary
map, valid tangle colourings, and actual closed sewing. No configuration
certificate or complete Four Colour theorem may enter its proof.
-/

open FourColor.PentagonalLobePatch
open Mettapedia.GraphTheory.FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``Tangle.cubic, [``Tangle.vertex, ``Tangle.rho]),
    (``Tangle.colouring_valid,
      [``Tangle.referenceColour_proper, ``Tangle.piece]),
    (``Tangle.boundary_colouring,
      [``Tangle.boundary_reference, ``Tangle.colouring]),
    (``Tangle.compatible_darts,
      [``compatible_colouring, ``Tangle.boundary_colouring]),
    (``Tangle.sewn_colorable,
      [``Tangle.compatible_darts, ``Tangle.colouring_valid,
        ``OpenTangleClosedWitness.glue])]
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
  logInfo m!"Pentagonal lobe tangle: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
