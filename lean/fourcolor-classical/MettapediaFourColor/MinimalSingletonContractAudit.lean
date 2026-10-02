import MettapediaFourColor.ActualDualContract
import Lean.Util.CollectAxioms

open Lean Elab Command FourColor
open Mettapedia.GraphTheory.FourColor
open GoertzelV24MinimalTriangleFree GoertzelV24AdjacentPairInsertion.AdjacentPairData

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``ConservedContract.of_conserved,
      [``RotationConservedFacePotential.exists_facePotential]),
    (``ConservedContract.singleton_support, []),
    (``ConservedContract.singleton,
      [``ConservedContract.of_conserved, ``ConservedContract.singleton_support]),
    (``MinimalSingletonContract.conserved_of_graph_flow, []),
    (``MinimalSingletonContract.one_zero,
      [``exists_cyclicallyOrdered_deletedColoring_of_vertexMinimalTaitCounterexample,
       ``oneZeroAmbientChain_isCDLGoodFlow_of_not_taitColorable,
       ``oneZeroAmbientChain_eq_zero_iff]),
    (``MinimalSingletonContract.colorable,
      [``MinimalSingletonContract.one_zero, ``ConservedContract.singleton]),
    (``Hypermap.insertE_relabel, []),
    (``Hypermap.ccColoring_relabel, [``Hypermap.insertE_relabel]),
    (``Hypermap.ccColoring_push, [``Hypermap.ccColoring_relabel]),
    (``ActualDualContract.map_eq_source_relabel,
      [``ActualDualRotation.data_step]),
    (``ActualDualContract.singleton_colorable,
      [``ActualDualContract.map_eq_source_relabel,
       ``MinimalSingletonContract.colorable, ``Hypermap.ccColoring_push]),
    (``ActualDualContract.not_colorable,
      [``ActualDualContract.map_eq_source_relabel,
       ``SourceConstruction.taitColoring_nonzero])]
  let forbidden : List Name := [
    `FourColor.fourColorTheorem, `FourColor.ClassicalAssembly, `FourColor.CompositionalComplete,
    `FourColor.reducible_all, `FourColor.reducibility, `FourColor.coversRec,
    `FourColor.ExceptionalRepairCertificate, `FourColor.ExceptionalRepairChecked,
    `FourColor.Hypermap.MinimalCounterExample.contract_coloring]
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
        throwError m!"Forbidden theorem or finite repair certificate in {root}: {name}"
    for name in (← liftCoreM <| collectAxioms root) do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}"
  logInfo m!"Actual singleton contracts: {roots.length} roots; \
    {all.toList.length} declarations; vertex-minimal smaller-map colouring, \
    exact singleton-zero field, face potential and faithful dual relabelling."
