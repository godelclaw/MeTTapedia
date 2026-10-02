import Lake

open Lake DSL

package MettapediaFourColor where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "85e3a25e006c35636f0e53b0e9296caca2685bc0"

require Mettapedia from "../mettapedia"

-- Pinned by lean/bootstrap_local_repos.sh; the upstream licence is retained.
require FourColor from "../externals/fourcolor"

lean_lib MettapediaFourColor

/-- Reconstruct the chain from a genuine local occurrence and minimality. -/
target kernelChainReduction pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/chain-reduction-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "NearLinearChainConstruction", "NearLinearChainContract", "NearLinearChainOccurrence", "ActualChainReduction", "ChainReductionExample", "ChainReductionAudit"]
      cwd := pkg.dir
      env := env }

/-- Transport a three-triangle chain repair from classical configuration 7. -/
target kernelNearLinearChain pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/near-linear-chain-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "NearLinearChainData", "NearLinearChainRepair", "NearLinearChainExample", "NearLinearChainAudit"]
      cwd := pkg.dir
      env := env }

/-- Eliminate the degree-five second sender using a different reduction edge. -/
target kernelRulePairResidual pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-pair-residual-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RulePairResidual", "ActualRulePairResidual", "RulePairResidualExample", "RulePairResidualAudit"]
      cwd := pkg.dir
      env := env }

/-- Combine distinct incoming rule occurrences in a signed star budget. -/
target kernelRulePairBudget pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-pair-budget-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RulePairBudget", "ActualRulePairBudget", "RulePairBudgetExample", "RulePairBudgetAudit"]
      cwd := pkg.dir
      env := env }

/-- Reconstruct a third charge rule from two compatible actual readings. -/
target kernelRulePairCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-pair-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RulePairCharge", "ActualRulePairCharge", "RulePairChargeExample", "RulePairChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Prepare the finite rotation and reachability facts for the rule-pair example. -/
target kernelRulePairExampleData pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-pair-example-data",
        "--library-output", ".lake/build/lib/lean", "--modules", "RulePairExampleData"]
      cwd := pkg.dir
      env := env }

/-- Check joint charge-rule geometry through shared actual darts. -/
target kernelRulePairDiamond pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-pair-diamond-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RulePairDiamond", "ActualRulePairDiamond", "RulePairExample",
        "RulePairCollisionExample", "RulePairDiamondAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the exact matcher using the prepared traversal certificates. -/
target kernelRuleMatcher pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-matcher-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "RuleMatcher", "RuleMatcherAudit"]
      cwd := pkg.dir
      env := env }

/-- Interpret checked rule traversals in actual graph darts. -/
target kernelRuleTraversal pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-traversal-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RuleTraversal", "RuleTraversalData"]
      cwd := pkg.dir
      env := env }

/-- Certify all pinned oriented-rule data and their local geometric paths. -/
target kernelNearLinearRuleData pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/near-linear-rule-data-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "NearLinearRuleData"]
      cwd := pkg.dir
      env := env }

/-- Connect prepared rule data to actual charge and exceptional coverage. -/
target kernelNearLinearCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/near-linear-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "NearLinearCharge", "ExceptionalFlatCharge", "NearLinearChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Reconstruct from local kernel faithfulness and actual disk injection. -/
target kernelInjectiveEmbeddedRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/injective-embedded-repair-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "InjectiveEmbeddedRepair", "FaithfulKernelEmbedding", "ExceptionalDartReading"]
      cwd := pkg.dir
      env := env }

/-- Close the exceptional geometric branch through the actual local embedding. -/
target kernelExceptionalExterior pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-exterior-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "LocalPreembedding", "ExceptionalPreembedding", "ActualDualLocalGeometry",
        "ExceptionalLocalRepair", "ExceptionalExteriorAudit"]
      cwd := pkg.dir
      env := env }

/-- Integrate actual singleton-zero fields into source contract colourings. -/
target kernelMinimalSingletonContract pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/minimal-singleton-contract-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ConservedContract", "MinimalSingletonContract", "ContractTransport", "ActualDualContract",
        "MinimalSingletonContractAudit"]
      cwd := pkg.dir
      env := env }

/-- Transport the constructed exceptional query through actual core corners. -/
target kernelExceptionalQuery pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-query-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "DualGraphQuery", "ExceptionalQueryReading", "ExceptionalQueryAudit"]
      cwd := pkg.dir
      env := env }

/-- Check exact Y/H construction and source geometry for D1774. -/
target kernelExceptionalConstruction pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-construction-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExceptionalConstruction", "KempeRepairContract", "ExceptionalConstructionRepair",
        "ExceptionalConstructionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay reconstruction and the dependency audit after the finite checks. -/
target kernelExceptionalRepairConsumer pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-repair-consumer",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "GraphTraceAlignment", "ExceptionalRepairReconstruction", "ExceptionalRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the repair proof against prepared finite-data artifacts. -/
target kernelExceptionalRepairChecks pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-repair-checks",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExceptionalRepairCertificate", "ExceptionalRepairChecked"]
      cwd := pkg.dir
      env := env }

/-- Check the joint-chord certificate and literal D1774 terminal witnesses. -/
target kernelExceptionalRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-repair-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "KempeIndexedCertificate", "KempeMaskCertificate",
        "ExceptionalRepairData", "ExceptionalRepairCertificate", "ExceptionalRepairChecked",
        "GraphTraceAlignment", "ExceptionalRepairReconstruction", "ExceptionalRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the eleven-port completion and actual compatible-colouring reconstruction. -/
target kernelExceptionalBoundary pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-boundary-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "FacialStarCompletion",
        "ExceptionalBoundaryCompletion", "ExceptionalBoundaryOccurrence", "PatchBoundaryGluing",
        "ExceptionalBoundaryReconstruction", "ExceptionalBoundaryAudit"]
      cwd := pkg.dir
      env := env }

/-- Check induced core recognition using actual triangular and four-cycle geometry. -/
target kernelExceptionalInduced pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-induced-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "FacialPatchInduced",
        "ExceptionalCoreInduced", "ExceptionalInducedAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the actual dual rotation used by exceptional core geometry. -/
target kernelExceptionalDual pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-dual-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "ActualDualRotation",
        "MinimalExceptionalEmbedding", "ExceptionalDualAudit"]
      cwd := pkg.dir
      env := env }

/-- Check facial orientation, local injectivity and the collision alternative. -/
target kernelExceptionalEmbedding pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-embedding-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExceptionalCoreOrientation", "ExceptionalCoreLocalInjectivity", "ExceptionalCoreCollision", "ExceptionalEmbeddingAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the pinned exceptional pattern and its actual graph interpretation. -/
target kernelExceptionalOverlap pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exceptional-overlap-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExceptionalPattern", "ExceptionalOverlap", "ExceptionalCore", "ExceptionalOverlapAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the conditional flat-neighbourhood coverage assembly. -/
target kernelFlatCoverage pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/flat-coverage-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "LocalCoverageAssembly", "FlatNeighborhoodCoverage", "FlatNeighborhoodCoverageAudit"]
      cwd := pkg.dir
      env := env }

/-- Check overlap recognition and its strict-reduction consumer. -/
target kernelOverlapSupply pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/overlap-supply-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "OverlappingPentagonalSectors", "OverlappingPentagonalSectorsAudit"]
      cwd := pkg.dir
      env := env }

/-- Check the near-linear family through prepared, audited reference artifacts. -/
target kernelNearLinearFamily pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/near-linear-family-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "BoundaryTriangleRepair", "NearLinearFiveData", "NearLinearFiveBase",
        "NearLinearFiveRepair", "NearLinearFiveGSLT", "NearLinearFiveAudit"]
      cwd := pkg.dir
      env := env }

/-- Check exact graph semantics for families of reference configurations. -/
target kernelConfigurationFamilies pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/family-audit",
        "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }

/-- Check the adapters and their axiom audit without emitting native C code. -/
@[default_target] target kernelAdapters pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_adapters.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--output", ".lake/adapter-audit", "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }

/-- Reconstruct the arity-ten presentation with the periodic certificate shared. -/
target kernelOrbitPresentation pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/orbit_presentation.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--output", ".lake/orbit-audit", "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }

/-- Check arity-eleven semantic sharing and its two compositional consumers. -/
target kernelOrbit11Presentation pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/orbit11_presentation.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--output", ".lake/orbit11-audit", "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }

/-- Check arity-nine sharing, reusing presentation modules outside its dependency cone. -/
target kernelOrbit9Presentation pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/shared_presentation.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".",
        "--pin", "../../tools/fourcolor/classical/orbit9-presentation-sources.json",
        "--output", ".lake/orbit9-audit", "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }

/-- Check the full reference baseline and the complete compositional endpoints. -/
target kernelComplete pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_complete.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/complete-audit",
        "--library-output", ".lake/build/lib/lean"]
      cwd := pkg.dir
      env := env }
