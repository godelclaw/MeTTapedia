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

/-- Replay uniform exterior repair and its consumer at a previously trapped seam. -/
target kernelFiveTrianglePuncturedRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/five-triangle-punctured-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "FiveTrianglePuncturedRepair", "FiveTrianglePuncturedAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay an invariant excluding every Kempe history through a fixed seam. -/
target kernelFiveTriangleKempeTrap pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/five-triangle-kempe-trap",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "FiveTriangleKempeTrap", "FiveTriangleKempeTrapAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a short explicit obstruction to fixed boundary-collapse transport. -/
target kernelFiveTriangleCollapse pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/five-triangle-collapse",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "FiveTriangleCollapseObstruction", "FiveTriangleJointChoice",
        "FiveTriangleCollapseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay constructive recognition of the shared facial sector. -/
target kernelSevenPairRecognition pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/seven-pair-recognition",
        "--library-output", ".lake/build/lib/lean", "--modules", "FacialChainClosure",
        "SevenPairSectorRecognition", "SevenPairRecognitionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the finite facial paths and source maps of the shared seven-pair sector. -/
target kernelSevenPairSectorData pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/seven-pair-sector",
        "--library-output", ".lake/build/lib/lean", "--modules", "SevenPairSectorData"]
      cwd := pkg.dir
      env := env }

/-- Replay the signed closing constraint and actual flat-pair continuation. -/
target kernelSevenPairSector pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/seven-pair-sector-proof",
        "--library-output", ".lake/build/lib/lean", "--modules", "SevenPairSector",
        "SevenPairSectorAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact charge with high-neighbour boundary transfers retained. -/
target kernelPuncturedCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/punctured-charge",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "PuncturedCyclicCharge", "PuncturedPairCharge",
        "PuncturedChargeExample", "PuncturedChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a tripod reduction supplied by joint source-rule matches. -/
target kernelJointTripodRules pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/joint-tripod-rules",
        "--library-output", ".lake/build/lib/lean", "--modules", "JointTripodRuleSupply",
        "JointTripodRuleExample", "JointTripodRuleAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the joint tripod closing law on both free sides of the charge fan. -/
target kernelRuleFanTripod pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-fan-tripod",
        "--library-output", ".lake/build/lib/lean", "--modules", "RuleFanTripodSupply",
        "RuleFanTripodAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay generic facial-interval boundary completion. -/
target kernelFacialBoundary pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/facial-boundary",
        "--library-output", ".lake/build/lib/lean", "--modules", "FacialBoundaryScheme",
        "FanBoundaryScheme", "FourTriangleCompletion", "FourTriangleCompletedOccurrence",
        "FacialBoundaryAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact source bridges and full joint repair for two four-triangle patches. -/
target kernelFourTriangleRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/four-triangle-repair",
        "--library-output", ".lake/build/lib/lean", "--modules", "FullRankRepair",
        "FourTriangleConstruction", "FourTriangleRepair"]
      cwd := pkg.dir
      env := env }

/-- Replay actual occurrence geometry and strict four-triangle reconstruction. -/
target kernelFourTriangleGeometry pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/four-triangle-geometry",
        "--library-output", ".lake/build/lib/lean", "--modules", "FourTriangleOccurrence",
        "FourTriangleRepairGeometry", "FourTriangleRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the common facial geometry of two four-triangle source cores. -/
target kernelFourTriangleCore pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/four-triangle-core",
        "--library-output", ".lake/build/lib/lean", "--modules", "FourTriangleCore",
        "FourTriangleRecognition", "FourTriangleAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the shared fan's adjacent seven-centre and joint-view supply. -/
target kernelRuleFanSevenCluster pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-fan-seven-cluster",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RuleFanSevenCluster", "RuleFanSevenClusterAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay common disk embedding and strict reconstruction for two-five wheels. -/
target kernelTwoFiveEmbedding pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/two-five-embedding",
        "--library-output", ".lake/build/lib/lean", "--modules", "TwoFiveWheelPreembedding", "TwoFiveWheelRepairGeometry", "TwoFiveWheelEmbeddingAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact source construction for the six two-five wheels. -/
target kernelTwoFiveConstruction pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/two-five-construction",
        "--library-output", ".lake/build/lib/lean", "--modules", "TwoFiveWheelConstruction"]
      cwd := pkg.dir
      env := env }

/-- Replay joint geometric completion across wheel layouts. -/
target kernelWheelBoundaryCompletion pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-boundary-completion",
        "--library-output", ".lake/build/lib/lean", "--modules", "WheelBoundaryCompletion", "D3009BoundaryLayout", "WheelBoundaryLayouts",
        "TwoFiveWheelOccurrence",
        "ActualWheelOccurrence", "WheelOccurrenceAudit", "SecondFanWheelOccurrence", "WheelBoundaryCompletionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay one boundary-collapse operation at every second-five position. -/
target kernelTwoFiveWheel pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/two-five-wheel-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "TwoFiveWheelData", "TwoFiveWheelRepair",
        "TwoFiveWheelColouring", "TwoFiveWheelAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the exact second-free-centre residual. -/
target kernelSecondFan pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/second-fan-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "SecondFanResidual", "SecondFanAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the actual wheel occurrence as the same injective repair disk. -/
target kernelWheelEmbedding pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-embedding-audit",
        "--library-output", ".lake/build/lib/lean", "--modules", "D3009Preembedding", "D3009RepairGeometry", "WheelEmbeddingAudit"]
      cwd := pkg.dir
      env := env }

/-- Assemble complete wheel repair and its actual compositional consumers. -/
target kernelWheelFamilyChecked pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-family-checked",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "WheelRepairChecked", "WheelFamilyChecked", "WheelFamilyAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay all wheel record checks after the full-table pilot. -/
target kernelWheelRepairRecords pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-repair-records",
        "--library-output", ".lake/build/lib/lean", "--modules", "WheelRepairRecord0", "WheelRepairRecord1", "WheelRepairRecord2", "WheelRepairRecord3", "WheelRepairRecord4", "WheelRepairRecord5", "WheelRepairRecord6", "WheelRepairRecord7", "WheelRepairRecord8", "WheelRepairRecord9", "WheelRepairRecord10", "WheelRepairRecord11", "WheelRepairRecord12", "WheelRepairRecord13", "WheelRepairRecord14", "WheelRepairRecord15", "WheelRepairRecord16"]
      cwd := pkg.dir
      env := env }

/-- Replay all wheel input checks after the full-table pilot. -/
target kernelWheelRepairInputs pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-repair-inputs",
        "--library-output", ".lake/build/lib/lean", "--modules", "WheelRepairInput0", "WheelRepairInput1", "WheelRepairInput2", "WheelRepairInput3", "WheelRepairInput4", "WheelRepairInput5", "WheelRepairInput6", "WheelRepairInput7", "WheelRepairInput8", "WheelRepairInput9", "WheelRepairInput10", "WheelRepairInput11", "WheelRepairInput12", "WheelRepairInput13", "WheelRepairInput14", "WheelRepairInput15", "WheelRepairInput16"]
      cwd := pkg.dir
      env := env }

/-- Prepare shared finite block definitions. -/
target kernelWheelRepairCheckCommon pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-repair-common",
        "--library-output", ".lake/build/lib/lean", "--modules", "WheelRepairCheckCommon"]
      cwd := pkg.dir
      env := env }

/-- Check action sharing without weakening exterior compatibility. -/
target kernelSharedMask pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/shared-mask-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeSharedMaskCertificate"]
      cwd := pkg.dir
      env := env }

/-- Benchmark the complete wheel certificate format before full finite replay. -/
target kernelWheelRepairPilot pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-repair-pilot",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeSharedMaskCertificate", "WheelRepairData", "WheelRepairCertificate", "WheelRepairPilot4", "WheelRepairPilot6", "WheelRepairPilot8", "WheelRepairPilot10", "WheelRepairPilot12", "WheelRepairPilotInput"]
      cwd := pkg.dir
      env := env }

/-- Replay a compatible repair of the wheel's nonextending seed trace. -/
target kernelWheelSeedRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-seed-repair-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeMaskCertificate", "WheelSeedRepairData", "WheelSeedRepairCertificate",
        "WheelSeedRepairChecked", "WheelSeedRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the exact wheel construction and its colouring interface. -/
target kernelWheelConstruction pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-construction-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "D3009Construction"]
      cwd := pkg.dir
      env := env }

/-- Replay the uniform wheel-colouring law and its cyclic GSLT interpretation. -/
target kernelWheelColouring pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-colouring-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "D3009Construction", "WheelColouring", "CyclicColourRoute", "WheelColouringGSLT",
        "D3009Colouring", "D3009ColouringExample", "WheelColouringAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay ordered wheel recognition and its pinned source consumer. -/
target kernelWheelNeighborhood pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/wheel-neighborhood-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "WheelNeighborhood", "D3009Wheel", "D3009Boundary",
        "WheelBoundaryCompletion", "D3009BoundaryLayout", "ActualWheelOccurrence",
        "WheelOccurrenceAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact cyclic accounting and its residual coverage consumer. -/
target kernelExactCyclicCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/exact-cyclic-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "LocalCyclicRules", "ExactCyclicCharge", "ExactFanResidual",
        "ExactChargeExample", "ExactChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a source-rule closing law and its actual colouring reductions. -/
target kernelExtraCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/extra-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExtraChargeReduction", "ExtraChargeExample", "ExtraChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a uniform cyclic charge budget from shared facial triangles. -/
target kernelCyclicCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/cyclic-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "CyclicCharge", "CyclicFanContinuation", "CyclicChargeExample", "CyclicChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the signed charge budget of a two-sided facial fan. -/
target kernelRuleFanCharge pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-fan-charge-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RuleFanCharge", "ActualRuleFanCharge", "RuleFanChargeExample", "RuleFanChargeAudit"]
      cwd := pkg.dir
      env := env }

/-- Combine two exact charge-rule views with three geometric reduction consumers. -/
target kernelRuleFanSupply pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/rule-fan-supply-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RuleFanSupply", "ActualRuleFanSupply", "RuleFanSupplyExample", "RuleFanSupplyAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the shared degree-seven region and its rebuilt coverage endpoint. -/
target kernelSector7 pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/sector7-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "Sector7Region", "Sector7Coverage", "Sector7Audit"]
      cwd := pkg.dir
      env := env }

/-- Check a chain that crosses a flat pair's original observation boundary. -/
target kernelChainBoundary pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/chain-boundary-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "RuleChainRecognition", "ChainBoundaryGeometry", "ChainBoundaryExample",
        "RuleChainRecognitionAudit"]
      cwd := pkg.dir
      env := env }

/-- Recognize the chain from its embedded three-triangle core. -/
target kernelChainRecognition pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/chain-recognition-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ThreeTriangleFan", "FanBoundaryScheme", "ChainCoreReading", "ChainCoreCompletion",
        "ChainCoreOccurrence",
        "ActualChainRecognition", "ChainFanRecognition", "ChainRecognitionExample",
        "ChainRecognitionAudit"]
      cwd := pkg.dir
      env := env }

/-- Extend the same facial-fan completion to the nine-port profile. -/
target kernelExtendedChain pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/extended-chain-audit",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "ExtendedChainCore", "ExtendedChainCompletion", "ExtendedChainOccurrence",
        "ExtendedChainRecognition", "ExtendedChainContract", "ActualExtendedChainReduction",
        "ExtendedChainExample", "ExtendedChainAudit"]
      cwd := pkg.dir
      env := env }

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

/-- Replay the structural anchor contract for three exact source strips. -/
target kernelTriangleStripAnchors pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/triangle-strip-anchors",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "TriangleStripAnchors", "TriangleStripAnchorsAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the obstruction to noncrossing boundary-only replacement. -/
target kernelBoundaryReplacement pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/boundary-replacement",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "BoundaryReplacementObstruction", "BoundaryReplacementObstructionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the composed two-triangle fan repair law. -/
target kernelBoundaryFan pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/boundary-fan",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeBoundaryFan", "BoundaryFanRepair", "StripParentFan", "StripParentFanExample",
        "BoundaryFanAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay adaptive repair through noncrossing interval exclusion. -/
target kernelIntervalRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/interval-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeIntervalMatching", "KempeIntervalRepair", "StripIntervalRepair",
        "IntervalRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the majority-block replacement for adaptive source repair. -/
target kernelMajorityRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/majority-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeMajorityRepair", "StripMajorityRepair", "MajorityRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the bounded inverse bridge and composed source repair. -/
target kernelTwoRoundRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/two-round-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeFiniteDecoder", "StripTwoRoundRepair", "TwoRoundRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact strip relations and their boundary-update obstruction. -/
target kernelStripResponse pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-response",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripResponseSummary", "StripResponseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay source reconstruction from symbolic boundary relations. -/
target kernelSymbolicStrip pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/symbolic-strip",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeChromogramMatching", "KempeChordComposition", "StripSourceExtension",
        "StripSymbolicRepair", "SymbolicStripAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the uniform chromogram-to-matching bridge. -/
target kernelChromogramMatching pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/chromogram-matching",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeChromogramMatching", "StripSymbolicRepair", "SymbolicStripAudit",
        "StripCriticalRepair", "ChromogramMatchingAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the fixed-boundary partial-colouring bound and reconstruction. -/
target kernelStripPartial pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-partial",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripPartialColouring", "StripSpineFibre", "StripPartialAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay coordinated component switches in a retained exterior. -/
target kernelRetainedMatching pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/retained-matching",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeChromogramMatching", "KempeRetainedMatching", "StripCoupledRepair",
        "RetainedMatchingAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay physical phase obstruction and mixed-pair reconstruction. -/
target kernelStripPhase pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-phase",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripPhaseObstruction", "StripPhaseDisk", "StripPhaseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the phase obstruction and repair on the spherical coverage example. -/
target kernelStripSphere pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-sphere",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripSpherePhase", "StripSphereGeometry", "StripSphereAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay adaptive partial-source progress through retained matchings. -/
target kernelStripTwoPhase pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-two-phase",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripPuncturedExtension", "StripTwoPhaseProgress",
        "StripTwoPhaseReconstruction", "StripTwoPhaseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the hole-choice obstruction and a compatible complete source repair. -/
target kernelStripChoiceBarrier pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-choice-barrier",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeAnchorSelection", "StripChoiceBarrier", "StripChoiceEscape", "StripChoiceAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the shared forced-chain obstruction and exact proper restrictions. -/
target kernelStripCriticalChain pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-critical-chain",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripCriticalChain", "StripCriticalChainAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the joint repair of both critical-chain boundaries. -/
target kernelStripChainRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-chain-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeBalancedBlock", "KempeShortBlock", "StripChainRepair", "StripChainRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay joint anchor propagation and exterior reconstruction for three cores. -/
target kernelTriangleStripLists pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/triangle-strip-lists",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "TriangleStripLists", "TriangleStripListsAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay conditional-colour loops and their majority/forest repair consumer. -/
target kernelStripChoiceLoops pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-choice-loops",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripChoiceLoops", "StripChoiceLoopRepair", "StripChoiceLoopAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the composed matching selector for the remaining choice loop. -/
target kernelStripLoopContinuation pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-loop-continuation",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "KempeShortBlock", "StripLoopMatching", "StripLoopContinuation",
        "StripLoopContinuationAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact cut transport and two actual-source list-summary obstructions. -/
target kernelStripListTransport pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-list-transport",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripListTransport", "StripListTransportAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay planar physical realizations of the evaluated-list obstruction. -/
target kernelStripPhysicalListTransport pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-physical-list-transport",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripEndpointTransport", "StripPhysicalListTransport",
        "StripPhysicalListTransportAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a physical trap for monotone joint choices and its two-switch escape. -/
target kernelStripAnchorTrap pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-anchor-trap",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripAnchoredExtension", "StripAnchorTrap", "StripGuardedOrbit", "StripAnchorTrapHistory",
        "StripAnchorTrapAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay obstruction transport and a minimum-degree-five spherical consumer. -/
target kernelStripAnchorPadding pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-anchor-padding",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripAnchorTrapTransport", "StripAnchorPadding", "StripAnchorPaddingAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the shared guarded-orbit invariant and its spherical counterexample. -/
target kernelStripStrongAnchorTrap pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-strong-anchor-trap",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripGuardedOrbit", "StripAnchorTrapHistory", "StripAnchorTrapAudit",
        "StripStrongAnchorTrap", "StripStrongAnchorTrapAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a two-stage source repair from old-state component conditions. -/
target kernelStripSingletonRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-singleton-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripSingletonRepair", "StripSingletonRim", "StripSingletonExample",
        "StripSingletonRepairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay geometric alternatives for the D0099 connection branch. -/
target kernelStripConnectionRepair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-connection-repair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripConnectionGeometry", "StripConnectionRepair", "GraphSphericalEuler",
        "StripConnectionExample", "StripConnectionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the joint-connection alternative for the port-six branch. -/
target kernelStripSixConnection pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-connection",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripSixConnection",
        "StripSixRim", "StripSixConnectionAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay neighbour-controlled continuation of the port-six branch. -/
target kernelStripSixRelease pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-release",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripSixRelease",
        "StripSixReleaseExample", "StripSixReleaseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the preserved-path repair of the port-six branch. -/
target kernelStripSixBarrier pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-barrier",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripSixBarrierGeometry", "StripSixBarrierRepair", "StripSixBarrierExample", "StripSixBarrierAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the exact fixed-pair phase repair criterion. -/
target kernelStripSixPhaseChoice pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-phase-choice",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripSixPhaseChoice", "StripSixPhaseExample", "StripSixPhaseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the two-phase order obstruction and silent detachment repair. -/
target kernelStripSixOrder pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-order",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripSixDetachment", "StripSixOrderExample", "StripSixOrderAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay exact degree-to-face transport and its alternative-piece consumer. -/
target kernelStripSixDual pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-dual",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "DualDegreePattern", "StripSixDualExample", "StripSixDualAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the two-switch repair using a single colour pair. -/
target kernelStripSixSamePair pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-same-pair",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripSixSamePair", "StripSixSamePairExample", "StripSixSamePairAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the single-pair obstruction and neighbouring release. -/
target kernelStripSixMixed pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-six-mixed",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripSixMixedExample", "StripSixMixedAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay a geometric choice between complementary repair pairs. -/
target kernelStripComplementary pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-complementary",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripComplementaryGeometry", "StripComplementaryRepair",
        "StripComplementaryExample", "StripComplementaryAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the exterior fan forced by a missing colour. -/
target kernelStripExteriorFan pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-exterior-fan",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripExteriorFan", "StripExteriorFanExample", "StripExteriorFanAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay degree-bounded supply of the neighbouring release. -/
target kernelStripDegreeRelease pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-degree-release",
        "--library-output", ".lake/build/lib/lean", "--modules", "StripDegreeRelease",
        "StripDegreeReleaseExample", "StripDegreeReleaseAudit"]
      cwd := pkg.dir
      env := env }

/-- Replay the source-sector alternative and its minimal-map consumer. -/
target kernelStripDiamondAlternative pkg : Unit := do
  let env ← getAugmentedEnv
  Job.async do
    proc {
      cmd := "python3"
      args := #["../../tools/fourcolor/classical/replay_family.py",
        "--reference", "../externals/fourcolor", "--mettapedia", "../mettapedia",
        "--package", ".", "--output", ".lake/strip-diamond-alternative",
        "--library-output", ".lake/build/lib/lean", "--modules",
        "StripDiamondAlternative", "StripDiamondAlternativeExample",
        "StripDiamondAlternativeAudit"]
      cwd := pkg.dir
      env := env }
