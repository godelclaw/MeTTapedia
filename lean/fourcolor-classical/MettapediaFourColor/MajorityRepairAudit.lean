import MettapediaFourColor.StripMajorityRepair
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

run_cmd do
  let env ← getEnv
  let roots := [``exists_adjacent_within, ``exists_adjacent_majority,
    ``exists_adjacent, ``KempeMajorityRepair.active_mate, ``KempeMajorityRepair.answer,
    ``StripMajorityRepair.rank_embed, ``StripMajorityRepair.embed_rank,
    ``StripMajorityRepair.order, ``StripMajorityRepair.successful,
    ``StripMajorityRepair.source_repair]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate,
    `FourColor.KempeAnchorProjection.signatures, `FourColor.KempeIntervalMatching,
    `FourColor.StripIntervalRepair.rejection, `FourColor.StripIntervalRepair.source_repair]
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
    if root == ``StripMajorityRepair.source_repair then
      for needed in [``exists_adjacent_within, ``exists_adjacent_majority,
          ``KempeMajorityRepair.active_mate, ``KempeIntervalRepair.gram_switch,
          ``KempeMatchingChromogram.reconstruct, ``StripMajorityRepair.order,
          ``StripIntervalRepair.answers, ``StripIntervalRepair.proper,
          ``TriangleStripAnchors.input0099] do
        unless seen.contains needed do
          throwError m!"Missing semantic dependency in {root}: {needed}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Majority repair: {roots.length} roots; {all.toList.length} declarations."
