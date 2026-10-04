import MettapediaFourColor.BoundaryReplacementObstruction
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let roots := [``BoundaryReplacementObstruction.diagonal_cover,
    ``BoundaryReplacementObstruction.source_edges,
    ``BoundaryReplacementObstruction.nonextension_checked,
    ``BoundaryReplacementObstruction.no_extension,
    ``BoundaryReplacementObstruction.normalize,
    ``BoundaryReplacementObstruction.signatures_checked,
    ``BoundaryReplacementObstruction.same_signature,
    ``BoundaryReplacementObstruction.obstruction]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut all : NameSet := {}
  for root in roots do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        all := all.insert name
        if forbidden.any (·.isPrefixOf name) then
          throwError m!"Forbidden dependency in {root}: {name}"
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    if root == ``BoundaryReplacementObstruction.obstruction then
      for needed in [``BoundaryReplacementObstruction.diagonal_cover,
          ``BoundaryReplacementObstruction.no_extension,
          ``BoundaryReplacementObstruction.normalize,
          ``NearLinearDiamondData.input0000] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Fixed-boundary obstruction: {roots.length} roots; {all.toList.length} declarations."
