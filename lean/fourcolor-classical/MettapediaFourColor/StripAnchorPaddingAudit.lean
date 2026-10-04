import MettapediaFourColor.StripAnchorPadding
import Lean.Util.CollectAxioms

open Lean Elab Command SimpleGraph FourColor
open SimpleGraph

run_cmd do
  let env ← getEnv
  let contracts : List (Name × List Name) := [
    (``StripAnchorTrapTransport.phase_stays, [``KempePairHistory.pointwise,
      ``StripAnchorTrap.pointwise_stays]),
    (``StripAnchorTrapTransport.history_nonextension, [``StripAnchorTrapTransport.history_stays,
      ``StripAnchorTrap.orbit_profile]),
    (``StripAnchorTrapTransport.history_no_source, [``StripAnchorTrapTransport.history_nonextension,
      ``StripResponseSummary.valid_of_colouring]),
    (``StripAnchorPadding.planar, [``GraphTriangulationEuler.planar_iff_balance,
      ``StripAnchorPadding.triangular, ``StripAnchorPadding.connected]),
    (``StripAnchorPadding.minimum_degree, [``GraphRotationRows.Rows.degree]),
    (``StripAnchorPadding.exterior_adj, []),
    (``StripAnchorPadding.old_edges, []),
    (``StripAnchorPadding.source_edges, []),
    (``StripAnchorPadding.source_injective, []),
    (``StripAnchorPadding.core_stars, []),
    (``StripAnchorPadding.no_guarded_reconstruction, [``StripAnchorTrapTransport.history_no_source,
      ``StripAnchorPadding.source_edges, ``StripAnchorPadding.initial_orbit]),
    (``StripAnchorPadding.repairStep, [``KempeSeparatedChains.Certificate.step,
      ``StripAnchorPadding.repair_eq]),
    (``StripAnchorPadding.repair_length, []),
    (``StripAnchorPadding.reconstructed, [``StripAnchorPadding.repairStep,
      ``StripAnchorPadding.whole_valid]),
    (``StripAnchorPadding.separating_seam, [])]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := [`sorryAx, `Lean.ofReduceBool, `FourColor.Bulk,
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly,
    `FourColor.CompositionalComplete, `FourColor.reducible_all,
    `FourColor.reducibility, `FourColor.coversRec, `FourColor.WheelRepairData,
    `FourColor.ExceptionalRepairData, `FourColor.WheelSeedRepairData,
    `FourColor.DiamondProfileData, `FourColor.ResidualSeedRepairCertificate]
  let mut all : NameSet := {}
  for (root, required) in contracts do
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
    for name in required do
      unless seen.contains name do
        throwError m!"Missing semantic dependency in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Minimum-degree-five anchor trap: {contracts.length} roots; \
    {all.toList.length} declarations."
