import Lake

open Lake DSL

package MettapediaNavierStokes where
  version := v!"0.1.0"

require NavierStokesAndEuler from git
  "https://github.com/openai/NavierStokesAndEuler.git" @
  "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"

require EulerBlowup from git
  "https://github.com/tristanbuckmaster/fluid_lean.git" @
  "d0124689230b58b4f86e7b90ac59de06404b3b6b" / "euler-blowup"

/-- Resolve shared transitive dependencies from the selected mathlib revision. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "85e3a25e006c35636f0e53b0e9296caca2685bc0"

/-- The existing source is shared, not copied into a second development. -/
lean_lib MettapediaFluid where
  srcDir := "../mettapedia"
  roots := #[`Mettapedia.Analysis, `Mettapedia.FluidDynamics.NavierStokes]

@[default_target] lean_lib MettapediaNS
