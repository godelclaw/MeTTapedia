# Navier–Stokes upstream integration

This package uses Lean 4.34.0-rc2 to import the existing OpenAI and
Alpöge–Buckmaster fluid-analysis libraries directly. It is a migration and
integration surface, not another copy of their mathematical developments
and not a completed regularity proof.

The existing MeTTapedia sources are available through `MettapediaFluid` with
`srcDir = ../mettapedia`. The repository's other Lean packages keep their own
toolchains. Compatibility of an existing module with this package must be
checked explicitly; adding the source root does not certify its migration.

## Pinned dependencies

- OpenAI/NavierStokesAndEuler:
  `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
- tristanbuckmaster/fluid_lean, package `euler-blowup`:
  `d0124689230b58b4f86e7b90ac59de06404b3b6b`.
- mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, the upstream
  Lean 4.34.0-rc2 revision.

The explicit mathlib requirement comes last so that its shared transitive
dependency versions take precedence over the older EulerBlowup manifest.

Upstream sources remain in their original package with their original
attribution and licenses. `MettapediaNS.UpstreamAudit` imports the actual
pressure-commutator, viscous-propagator, and arbitrary-positive-viscosity
periodic uniqueness theorems and prints their axioms. It also imports the
existing coherent-pair estimate from the canonical MeTTapedia source tree.
It does not replace their analytic hypotheses with assumptions about the
desired global regularity conclusion.

## Checked applications and semantic interfaces

| Module | Reused mathematics | Exact remaining boundary |
| --- | --- | --- |
| `MettapediaNS.WholeSpaceBKM` | OpenAI's actual vorticity norm, norm-path continuity, and logarithmic gradient estimate. The adapter proves equality with the existing spatial essential supremum, including its extended value, and applies the estimate to the existing transported-velocity interface. | Euclidean smooth fields with actual L² jets; the physical-time vorticity budget and the required realization of the velocity remain obligations. A nonzero periodic lift is not a whole-space L² field. |
| `MettapediaNS.WholeSpaceViscousEnergy` | OpenAI's derivative-word fields, whole-space integration by parts, and nonlinear H³ energy estimate. The constructed Laplacian is identified with mathlib's actual Laplacian; its production is exactly minus twice the derivative-word dissipation. The full unforced NS right-hand side therefore retains the same nonlinear bound with dissipation on the left. | These are spatial right-hand-side identities and estimates. A time-dependent solution must still supply its actual evolution and regularity, and the gradient/vorticity coefficient must be controlled. |
| `MettapediaNS.AlmostOrthogonality` | Direct semantic aliases of Alpöge–Buckmaster's C*-ring and Hilbert-space Cotlar–Stein theorems. Neither proof is copied or reimplemented. | Both adjoint cross-product bounds and the row/column majorant bounds must be established for the actual localized operators. |
| `MettapediaNS.QuadraticSingularIntegral` | Alpöge–Buckmaster's sharp-truncation, smooth-truncation, and principal-value `L^p` bounds. The adapter constructs the angular hypotheses for the explicit kernels `x_i*x_j / ‖x‖^5` (`i ≠ j`) and `(x_i² - x_j²) / ‖x‖^5`, using mathlib's orthogonal changes of variables and compactness. | Whole-space inputs: bounded compactly supported fields for the truncations, smooth compactly supported fields for the principal value, finite `p > 1`. The constants are independent of the truncation radii; the smooth version also permits every cutoff satisfying the stated support/range conditions. The modules below identify and assemble the actual whole-space strain on smooth compactly supported sources. Periodic transfer, weighted costs, and physical-time control remain separate obligations. |
| `MettapediaNS.WholeSpaceBiotSavart` | Alpöge–Buckmaster's proved `potential_theory_R3` and actual Newtonian Biot–Savart construction. Its velocity is smooth and in `L²`; for divergence-free vorticity, its divergence vanishes and its curl recovers that vorticity in both OpenAI's and the pancake route's APIs. The actual velocity-gradient entries are represented using the imported Newtonian gradient kernel on source derivatives. | Smooth compactly supported vorticity on `ℝ³`. The modules below supply the trace-free Hessian identification, derivative-free component bounds, full strain assembly, and all `L²` velocity jets for divergence-free inputs. General admissible data, physical-time evolution, and the signed budget remain separate obligations. |
| `MettapediaNS.NewtonianHessianPrincipalValue` | The upstream regularized Newtonian potential, integration by parts, convergence against test functions, and principal-value integrability. These identify the actual off-diagonal Newtonian Hessians and differences of diagonal Hessians with the upstream principal-value operators, including the factor `-3/(4π)`. The previously imported `L^p` estimates now bound those actual derivatives by the undifferentiated source norm. | Smooth compactly supported scalar sources on `ℝ³`, finite `p > 1`. Radial cancellation removes the local term for these trace-free components; no such cancellation is asserted for an individual diagonal entry. Full-strain assembly is supplied below. General-data/periodic transfer, weighted projector costs, and signed physical-time control remain open. |
| `MettapediaNS.WholeSpaceStrain` | The existing pancake `strainRateApply` is identified with mathlib's self-adjoint part of the actual Biot–Savart gradient. Its entries are explicit combinations of the imported principal-value operators: local isotropic terms cancel before estimation. All nine entries and the complete operator satisfy `L^p` bounds by the undifferentiated vorticity norm. Assembly uses OpenAI's multilinear coordinate estimate, mathlib's isometric currying, and its finite-sum `L^p` inequality. | Smooth compactly supported vorticity on `ℝ³`, finite `p > 1`; the constant is independent of the source. Actual `MemLp` is also proved. This supplies no `L^∞` endpoint, derivative-weighted projector estimate, general-data/periodic extension, or signed physical-time budget. |
| `MettapediaNS.WholeSpacePressure` | OpenAI's smooth Helmholtz pressure field, normalized radial scalar potential, and preservation of solenoidality by actual derivative words. The constructed pressure is an actual smooth scalar gradient, and the full viscous right-hand side is divergence-free for solenoidal input. The H³ production estimate no longer takes an independently supplied pressure or gradient-space hypothesis. | An actual `SmoothL2Field` input is required. The module constructs a spatial NS right-hand side, not a solution trajectory. No physical-time equation or budget is assumed to follow from the construction. |
| `MettapediaNS.WholeSpaceBiotSavartRegularity` | OpenAI's `smoothL2Field_of_curl_compact` applies directly to the smooth finite-energy Biot–Savart velocity constructed using Alpöge–Buckmaster. Every actual Fréchet derivative is in `L²`, and the closed solenoidal-space condition is proved. The existing spatial BKM estimate and viscous H³ production bound now apply with velocity jets and pressure both constructed from the source. | Smooth compactly supported divergence-free vorticity on `ℝ³`. Compact vorticity is not asserted to persist under viscous evolution. General-data extension, actual time evolution, weighted projector costs, and the signed physical-time bound remain open. The constant time path in the BKM notation represents one spatial slice only. |

`WholeSpaceBKM.h3_energyProduction_add_dissipation_le_spatialBKMIntegrand`
combines the first two applications: the actual viscous energy production
is controlled by the existing spatial BKM integrand and the actual higher
velocity norm. This does not establish integrability up to a singular time.

`NS.Lit.CZ.truncated_Lp_uniform`, `pvOp_Lp`, and
`smoothTruncate_Lp_uniform` in `Lit/CZ/CZCore/Homogeneous.lean` are now
checked imports and used by the quadratic-kernel applications above.
Their proofs cover general positive dimension; the current concrete
applications use dimension three. None of these estimates provides an
`L^∞` endpoint or the global signed time-integrated misalignment budget.

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
bash scripts/prepare-upstreams.sh
lake build MettapediaNS
lake env lean MettapediaNS/UpstreamAudit.lean
```

This target checks the imported theorem surface and adapters listed above. The
arbitrary-data dynamical budget and unconditional continuation theorem remain
separate mathematical obligations.

The selected target has been checked on Lean 4.34.0-rc2. OpenAI's source
tree is unchanged. EulerBlowup declares Lean 4.32.2 and mathlib 4.32.0;
the Cotlar–Stein dependency chain compiles unchanged on the newer toolchain.
The larger homogeneous-kernel dependency chain needs exactly five order-
lemma name updates in `Marcinkiewicz.lean` and `Homogeneous.lean`, recorded
in `patches/euler-blowup-lean-4.34.patch`. The potential-theory dependency
chain additionally needs one scoped elaboration setting around the existing
`Cm24.L2_6_III_Fc` proof in `Cm24/S2/Master.lean`, recorded in
`patches/euler-blowup-potential-lean-4.34.patch`. No statement or mathematical
argument is changed. `scripts/prepare-upstreams.sh` checks the pinned
revision and applies these patches idempotently, refusing a conflicting patch.
Run it after dependency setup; it never resets upstream files. The upstream
files and their Apache-2.0 license remain in their original package.
This does not certify the entire EulerBlowup development.
Upstream and existing local sources emit deprecation/unused-variable
warnings; these are not proof failures.

The shared `SpatialBKMIntegrand` source needs only a compatibility adjustment
to six continuity/measurability applications. Its mathematical statements
are unchanged; no new supremum construction is introduced.
The adjusted source also passes its original Lean 4.31.0 target. The
88-declaration integration audit reports only `propext`, `Classical.choice`,
and `Quot.sound`; there are no additional analytic axioms in those proofs.
