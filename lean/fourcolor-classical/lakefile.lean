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
