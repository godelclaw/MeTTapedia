import MettapediaFourColor.DiamondInsertionGSLT
import Lean.Util.FoldConsts

/-!
# Audit of the diamond configuration geometry and colouring alternatives

The dependency contracts cover the reference decoder, exact embedded maps,
ordered traces, cyclic neighbour lists, both colouring branches and the GSLT
history. No classical reducibility certificate or complete Four Colour theorem
may occur in these dependency closures. This is a geometry and semantics
audit; it does not claim a new reducibility result.
-/

open FourColor FourColor.ExecutableConfiguration FourColor.DiamondConfigurations
open FourColor.DiamondInsertion
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let contracts : List (Name × List Name) := [
    (``evaluate_eq, [``cpmap, ``ofCancel3_eq]),
    (``realization001, [``cf001, ``reference001, ``numbered001, ``index]),
    (``realization002, [``cf002, ``reference002, ``numbered002, ``index]),
    (``realization004, [``cf004, ``reference004, ``numbered004, ``index]),
    (``reducibilityTrace001, [``cf001, ``cpring001, ``faces001,
      ``ConfigurationTable.Realization.forwardRingTrace]),
    (``reducibilityTrace002, [``cf002, ``cpring002, ``faces002,
      ``ConfigurationTable.Realization.forwardRingTrace]),
    (``reducibilityTrace004, [``cf004, ``cpring004, ``faces004,
      ``ConfigurationTable.Realization.forwardRingTrace]),
    (``faceOrbit001, [``ConfigurationFaceGraph.faceCycle_eq_orbit, ``table001]),
    (``faceOrbit002, [``ConfigurationFaceGraph.faceCycle_eq_orbit, ``table002]),
    (``faceOrbit004, [``ConfigurationFaceGraph.faceCycle_eq_orbit, ``table004]),
    (``core001, [``diamondCore, ``graph001]),
    (``core002, [``diamondCore, ``graph002]),
    (``core004, [``diamondCore, ``graph004]),
    (``insert12, [``subdivide, ``graph001, ``graph002]),
    (``insert24, [``subdivide, ``graph002, ``graph004]),
    (``triangle12, [``table001, ``ring001, ``vertex001]),
    (``triangle24, [``table002, ``ring002, ``vertex002]),
    (``rotation12, [``ConfigurationFaceGraph.triangleStar, ``stars001, ``stars002]),
    (``rotation24, [``ConfigurationFaceGraph.triangleStar, ``stars002, ``stars004]),
    (``boundary12, [``ConfigurationFaceGraph.triangleBoundary, ``boundary001, ``boundary002]),
    (``boundary24, [``ConfigurationFaceGraph.triangleBoundary, ``boundary002, ``boundary004]),
    (``referenceAlternatives14, [``alternativesEquiv, ``equalColoringEquiv,
      ``insert12, ``insert24, ``coloring004, ``ConfigurationFaceGraph.Presentation.coloringEquiv,
      ``realization004]),
    (``context12, [``referenceAlternatives12]),
    (``context24, [``referenceAlternatives24]),
    (``DiamondInsertionGSLT.presentation, [``DiamondInsertionGSLT.theory]),
    (``DiamondInsertionGSLT.supported_iff, [``DiamondInsertionGSLT.witness,
      ``Mettapedia.GSLT.RelationalRouteSemantics.Semantics.Witness,
      ``referenceAlternatives14]),
    (``DiamondInsertionGSLT.viable_iff, [``DiamondInsertionGSLT.every_coloring,
      ``Mettapedia.GSLT.RelationalRouteSemantics.Semantics.Viable]),
    (``DiamondInsertionGSLT.constructed, [``DiamondInsertionGSLT.seed,
      ``DiamondInsertionGSLT.witness, ``referenceAlternatives14])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
  let mut inspected : NameSet := {}
  for (root, required) in contracts do
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
        throwError m!"Classical certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond geometry and colouring alternatives: {contracts.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    no classical certificate or complete theorem dependencies."
