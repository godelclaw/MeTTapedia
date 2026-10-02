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
