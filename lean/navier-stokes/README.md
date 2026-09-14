# Navier–Stokes upstream integration

This package uses Lean 4.34.0-rc2 to import the existing OpenAI fluid-analysis
library directly. It is a migration and integration surface, not another copy
of the mathematical development and not a completed regularity proof.

The existing MeTTapedia sources are available through `MettapediaFluid` with
`srcDir = ../mettapedia`. The repository's other Lean packages keep their own
toolchains. Compatibility of an existing module with this package must be
checked explicitly; adding the source root does not certify its migration.

## Pinned dependencies

- OpenAI/NavierStokesAndEuler:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, the upstream
  Lean 4.34.0-rc2 revision.

Upstream sources remain in their original package with their original
attribution and licenses. `MettapediaNS.UpstreamAudit` imports the actual
pressure-commutator, viscous-propagator, and arbitrary-positive-viscosity
periodic uniqueness theorems and prints their axioms. It also imports the
existing coherent-pair estimate from the canonical MeTTapedia source tree.
It does not replace their analytic hypotheses with assumptions about the
desired global regularity conclusion.

## Reuse policy

Before a new general-analysis proof, check mathlib, the existing MeTTapedia
development, and the relevant OpenAI and Alpöge–Buckmaster developments.
Prefer direct application, then a representation adapter or a generalization
of an existing proof. Record the exact missing hypothesis before undertaking
new mathematics. Toolchain differences are migration tasks, not a reason to
reprove an available theorem.

Ben's coherence/pancake mechanism remains the research target. Auxiliary
norms, functionals, and interfaces may be improved to use established theory.

## Build

```sh
lake update
lake exe cache get
lake build MettapediaNS
```

This target checks only the imported theorem surface listed above. The
arbitrary-data dynamical budget and unconditional continuation theorem remain
separate mathematical obligations.

The selected target has been checked on Lean 4.34.0-rc2. It compiles the
unchanged coherent-pair source together with the direct upstream imports.
The existing coherent-pair source produces deprecation/unused-variable
warnings on the newer toolchain; these are not proof failures.

The Alpöge–Buckmaster repository is a separate source inventory:
`tristanbuckmaster/fluid_lean` at `d0124689230b58b4f86e7b90ac59de06404b3b6b`.
Its `euler-blowup` package declares Lean 4.32.2 and mathlib 4.32.0. It has
not yet been added as a dependency or certified on this newer toolchain.
This distinction prevents a source review from being reported as an import.
