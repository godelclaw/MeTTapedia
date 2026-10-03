import MettapediaFourColor.FourTriangleRecognition
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``FourTriangleCore.source_stars, []),
    (``FourTriangleCore.turns, [``FourTriangleCore.step_partition]),
    (``FourTriangleCore.injective,
      [``FourTriangleCore.short_pairs, ``ExceptionalCoreLocalInjectivity.corner_chain_injective]),
    (``FourTriangleCore.reflects, [``FacialPatchInduced.corner_chain_successor]),
    (``FourTriangleCore.source_profile_embedding,
      [``FourTriangleCore.injective, ``FourTriangleCore.reflects]),
    (``FourTriangleRecognition.embedded,
      [``FourTriangleCore.source_profile_embedding, ``MinimalExceptionalEmbedding.triangle_facial])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.ExceptionalRepairCertificate, `FourColor.WheelRepairData,
    `FourColor.WheelSeedRepairData, `FourColor.DiamondProfileData]
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
        throwError m!"Forbidden endpoint or reduction certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Four-triangle recognition: {roots.length} roots; \
    {all.toList.length} declarations. Both exact source cores use the same \
    facial-interval proof. No colouring certificate or full Four Colour theorem. \
    Boundary completion, repair and flat-pair classification remain separate."
