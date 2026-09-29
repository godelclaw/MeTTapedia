import MettapediaFourColor.PentagonalLobePhysicalRepair
import Lean.Util.CollectAxioms

/-! Dependency audit of physical boundary transport and its reconstruction consumer. -/

open Lean Elab Command
open FourColor
open Mettapedia.GraphTheory.FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeMatchingChromogram.reconstruct,
      [``KempeMatchingChromogram.translation, ``KempeMatchingChromogram.difference_paired,
        ``KempeMatchingChromogram.matches_related]),
    (``PhysicalKempeBoundary.closed,
      [``KempeMatchingChromogram.reconstruct, ``PhysicalKempeBoundary.encode_swap,
        ``PhysicalKempeBoundary.encode_permWord]),
    (``PhysicalKempeBoundary.ordered_closed,
      [``PhysicalKempeBoundary.closed,
        ``GoertzelV24PhysicalKempeNoncrossingClosure.boundaryKempeClosed_orderedTaitSupport_of_physical_noncrossing]),
    (``PhysicalKempeBoundary.vertexSide_closed,
      [``PhysicalKempeBoundary.closed,
        ``GoertzelV24PhysicalKempeNoncrossingClosure.boundaryKempeClosed_orderedVertexSideTaitSupport]),
    (``PhysicalKempeBoundary.trace_valid,
      [``GoertzelV24PortTangleCutParity.sum_boundaryWord_eq_zero,
        ``PhysicalKempeBoundary.paletteAdd]),
    (``PentagonalLobePatch.Tangle.physicalTrace_iff,
      [``PentagonalLobePatch.Tangle.ExteriorTrace,
        ``PhysicalKempeBoundary.Trace]),
    (``PentagonalLobePatch.Tangle.sewn_colorable_of_physical_noncrossing,
      [``PentagonalLobePatch.Tangle.exterior_closed,
        ``PhysicalKempeBoundary.trace_valid,
        ``PentagonalLobePatch.Tangle.physicalTrace_iff,
        ``PentagonalLobePatch.Tangle.sewn_colorable,
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
  logInfo m!"Physical lobe repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure."
