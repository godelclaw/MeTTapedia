import MettapediaFourColor.DiamondContract
import Lean.Util.FoldConsts

/-!
# Audit of contract edges and their boundary semantics

The roots retain the reference contract selector, its dart coordinates and
both directions of contract-colouring transport. Reducibility certificates
and complete Four Colour endpoints are excluded from these dependencies.
-/

open FourColor FourColor.ExecutableConfiguration FourColor.DiamondContract
open FourColor.ConfigurationFaceGraph

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``marked_eq, [``ctrenum, ``kernelEdges, ``cpmap]),
    (``Hypermap.ccColoring_relabel, [``Hypermap.CcColoring, ``Hypermap.insertE_relabel]),
    (``Presentation.contractColoringEquiv, [``Presentation.ContractAssignment,
      ``Hypermap.CcColoring, ``Hypermap.CcColoring.cface]),
    (``contract001, [``cfcontract, ``enumeration001, ``marked_eq]),
    (``contract002, [``cfcontract, ``enumeration002, ``marked_eq]),
    (``contract004, [``cfcontract, ``enumeration004, ``marked_eq]),
    (``referenceEndpoints001, [``contract001, ``endpoints001]),
    (``referenceEndpoints002, [``contract002, ``endpoints002]),
    (``referenceEndpoints004, [``contract004, ``endpoints004]),
    (``referenceContract_insertions, [``referenceEndpoints004,
      ``DiamondInsertion.insert12, ``DiamondInsertion.insert24]),
    (``contractTrace001, [``contract001, ``ConfigurationTable.Realization.ccRingTrace,
      ``Presentation.ccRingTrace_iff]),
    (``contractTrace002, [``contract002, ``ConfigurationTable.Realization.ccRingTrace,
      ``Presentation.ccRingTrace_iff]),
    (``contractTrace004, [``contract004, ``ConfigurationTable.Realization.ccRingTrace,
      ``Presentation.ccRingTrace_iff])]
  let forbidden : List Name := [`FourColor.Bulk, `FourColor.Reduce,
    `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all]
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
        throwError m!"Classical certificate or complete theorem in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond contract transport: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    no classical certificate or complete theorem dependencies."
