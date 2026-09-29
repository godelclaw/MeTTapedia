import MettapediaFourColor.DiamondProfileReducibility
import Lean.Util.FoldConsts

/-!
# Audit of the shared profile certificate and its actual graph consumers

The complete graph reductions must consume profile descent, actual interior
witnesses and the proved reference contraction decoder. The three original
configuration certificates and the earlier diamond repair bodies are excluded.
The single-chord law is independent of the catalogue and finite-cover checker;
the coupled active-mask law retains the same exterior. Their consumer counts
and 216 local ear-pair classifications are kernel checked. Five residual finite
covers remain explicit. The six-active-port skeleton fact is a shared finite
combinatorial lemma, separate from its unrestricted mask-transport theorem.
-/

open FourColor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``KempeProfileCertificate.sound_of_cover, [``kempeCoclosure_of_rank,
      ``KempeProfileCertificate.answerWord_map]),
    (``KempeChordExchange.answer_exists, [``KempeChordExchange.exchange_first,
      ``matchg_gramRot]),
    (``KempeChordMasks.recolor_matches, [``KempeChordMasks.paired,
      ``KempeChordMasks.recolor, ``matchStep]),
    (``KempeChordMasks.six_checked, [``KempeChordMasks.balanced,
      ``KempeChordMasks.earPairs, ``KempeChordMasks.jointMasks]),
    (``KempeChordMasks.coverCheck_sound, [``KempeChordMasks.recolor_matches,
      ``KempeChordMasks.matched_skeleton, ``KempeChordMasks.six_checked]),
    (``DiamondProfileCertificate.structural_counts, [``DiamondProfileCertificate.strategy]),
    (``DiamondProfileCertificate.coupled_counts, [``DiamondProfileCertificate.strategy,
      ``KempeChordMasks.earPairs]),
    (``DiamondProfileCertificate.coupled_example, [``DiamondProfileCertificate.example_checked,
      ``KempeChordMasks.recolor_matches, ``DiamondProfile.good_supports]),
    (``DiamondProfileCertificate.structural_checked, [``DiamondProfileCertificate.checked0,
      ``DiamondProfileCertificate.checked1, ``DiamondProfileCertificate.checked2]),
    (``DiamondProfile.good_supports, [``DiamondProfile.solve,
      ``Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination.Summary]),
    (``DiamondProfileCertificate.repair, [``KempeProfileCertificate.sound_of_cover,
      ``KempeChordExchange.answer_exists, ``KempeChordMasks.coverCheck_sound,
      ``DiamondProfileCertificate.coverCheck_sound,
      ``DiamondProfileCertificate.checked0, ``DiamondProfileCertificate.checked1,
      ``DiamondProfileCertificate.checked2, ``DiamondProfile.good_supports,
      ``DiamondProfile.key]),
    (``DiamondProfileFamilyRepair.repair0, [``DiamondProfileFamilyRepair.coverage0,
      ``DiamondProfileCertificate.repair, ``Bulk.partialOf_indexOf]),
    (``DiamondProfileFamilyRepair.repair1, [``DiamondProfileFamilyRepair.coverage1,
      ``DiamondProfileCertificate.repair, ``Bulk.partialOf_indexOf]),
    (``DiamondProfileFamilyRepair.repair2, [``DiamondProfileFamilyRepair.coverage2,
      ``DiamondBoundaryRepair.normalize, ``DiamondProfileCertificate.repair]),
    (``DiamondProfileReducibility.repair001, [``DiamondProfileFamilyRepair.repair0,
      ``DiamondProfileReducibility.supports_graph]),
    (``DiamondProfileReducibility.reducible001, [``DiamondProfileFamilyRepair.repair1,
      ``DiamondProfileReducibility.transferred001, ``KempeBoundarySplit.repairs_collapse,
      ``DiamondSplitRepair.reconstruct, ``DiamondSplitRepair.contract_proper,
      ``DiamondSplitRepair.valid_contract, ``contract_ctreeP]),
    (``DiamondProfileReducibility.reducible002, [``DiamondProfileFamilyRepair.repair1,
      ``DiamondBoundarySummary.reference002, ``DiamondProfileReducibility.contract_proper002,
      ``DiamondProfileReducibility.valid_contract002, ``contract_ctreeP]),
    (``DiamondProfileReducibility.reducible004, [``DiamondProfileFamilyRepair.repair2,
      ``DiamondProfileReducibility.supports_graph, ``DiamondJointContract.contractTrace_iff,
      ``DiamondJointRepair.valid_contract, ``contract_ctreeP]),
    (``DiamondProfileReducibility.compatible_history, [``DiamondProfileReducibility.repair004,
      ``DiamondInsertionGSLT.every_coloring])]
  let forbidden : List Name := [`FourColor.Bulk.Cfg000, `FourColor.Bulk.Cfg001,
    `FourColor.Bulk.Cfg003, `FourColor.kempeTree, `FourColor.kempeTreeNum,
    `FourColor.kempeTreeDepth, `FourColor.CompositionalComplete, `FourColor.ClassicalAssembly,
    `FourColor.fourColorTheorem, `FourColor.reducibility, `FourColor.reducible_all,
    `FourColor.DiamondSplitRepair.base_repair, `FourColor.DiamondBoundaryRepair.repair,
    `FourColor.DiamondJointRepair.contract_repair]
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
        throwError m!"Superseded certificate or complete theorem in {root}: {name}"
      if (root == ``KempeProfileCertificate.sound_of_cover ||
          root == ``KempeChordExchange.answer_exists ||
          root == ``KempeChordMasks.recolor_matches ||
          root == ``KempeChordMasks.six_checked ||
          root == ``KempeChordMasks.coverCheck_sound) &&
          ([`FourColor.Bulk, `FourColor.DiamondConfigurations,
            `FourColor.DiamondContract].any (·.isPrefixOf name) || name == ``cfmap ||
              name == ``coversRec || name == ``coversRec_sound) then
        throwError m!"A structural answer law depends on a catalogue or finite cover: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Diamond profile repair: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    original configuration 1, 2 and 4 certificates absent."
