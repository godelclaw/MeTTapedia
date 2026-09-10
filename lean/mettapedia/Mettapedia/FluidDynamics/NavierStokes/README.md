# NavierStokes

This directory contains the Lean side of the godelclaw Navier-Stokes /
Fefferman-target route audit. It is not a proof of the Millennium
Navier-Stokes problem.

Useful entry points:

- `NavierStokesEquationTarget.lean` - concrete target surface for the
  Navier-Stokes equation on time `R` and space `R^3`.
- `FeffermanGrassrootsInterface.lean` - bridge from current approximation
  packages toward the Fefferman-style target.
- `NavierStokesWitnessConstruction.lean` - honest witness-construction surface;
  includes the zero-data witness and classifies what extra balance is needed
  for boxed steady seed routes.
- `NavierStokesBKMContinuationTarget.lean` and
  `NavierStokesUniformVorticityContinuationTarget.lean` - continuation target
  surfaces.
- `NavierStokesFiniteMode*.lean` - finite-mode classifications and obstruction
  checks.
- `WindowedColeHopfHeat*.lean` and `Fefferman*.lean` - Cole-Hopf/Fefferman
  package interfaces and obstruction/frontier surfaces.

Related papers:

- `papers/benxiv/goertzel_ns.tex`
- `papers/benxiv/goertzel_ns.pdf`
- `lean/mettapedia/papers/ns_crux.tex`
- `lean/mettapedia/papers/ns_grassroots.tex`

Cross-problem proof-state scan:

- `lean/mettapedia/Mettapedia/Problems/PROOF_STATE.md`

Area-local proof-state and live build target:

- `lean/mettapedia/Mettapedia/FluidDynamics/NavierStokes/PROOF_STATE.md`
- `lake -f lakefile.toml build Mettapedia.FluidDynamics.NavierStokes.Live`

## Cluster Map

Source-count scan from 2026-06-21:

- Cole-Hopf/Fefferman window package: 86 files. This is the largest cluster and
  includes `WindowedColeHopfHeat*`, `ColeHopf*`, and `Fefferman*` route
  surfaces.
- Finite-mode classifications and obstructions: 40 files.
- Schwartz, shear, pressure, and transported obstruction family: 28 files.
- Witness construction and shared-witness route: 16 files.
- Target/core analytic infrastructure: 9 files, including the equation target,
  vector-calculus support, Schwartz data, and energy inequality surfaces.
- BKM/continuation targets and bridges: 8 files.
- Topology countermodels: 2 files.
- Other support/frontier/regression files: the remaining files.

This map is an organizational index only. It is not evidence of global
regularity, blowup, or any other Millennium-problem conclusion.

## Current Status

### September 2026 material-flow development

The stochastic-Lagrangian lane now constructs a local infinite Fourier
velocity and a common-interval material flow for arbitrary admissible smooth
periodic data, with no small-data restriction. Along that flow it derives
the actual velocity-gradient and strain equations, retaining the pressure
Hessian, spin, and viscous terms.

`StochasticLagrangian/LocalMaterialVorticity.lean` derives the actual curl
equation `Dₜω = Sω + νΔω`, including its real Euclidean formulation.
`LocalVorticityDiffusion.lean` proves continuity of the viscous source from
the common third Fourier-moment envelope and applies the reusable
`Mettapedia.Analysis.ODE.QuadraticFormBound` estimate. The strain growth bound
remains an explicit hypothesis of that estimate. The accompanying
`LocalMaterialVorticityAudit.lean` checks the theorem dependencies.

`LocalMaterialStrain.lean` constructs the real symmetric strain path and
proves its `C¹` regularity from the common third-moment envelope.
`LocalSpectralDefect.lean` applies the collision-safe integrated spectral
defect identity to this actual strain and vorticity, without assuming their
ODEs or regularity as extra input. `LocalSpectralDefectSources.lean` exposes
the nonnegative spin contribution and the signed pressure/viscosity terms.

`LocalSpectralResidual.lean` derives the almost-everywhere equation

```text
z = λω - Sω,       R = -W² - Hess(p) + νΔS,       f = νΔω
z' = -λz + source
source = <e,Re>ω - Rω + (λI-S)f,       λ = λ_max(S) ≥ 0
```

Here `e` is a selected top unit eigenvector. No regularity of that selection
is assumed. `LocalSpectralResidualBudget.lean` proves absolute continuity of
`z`, integrability of the actual source, and
`‖z(b)‖ ≤ ‖z(a)‖ + ∫ a..b, ‖source(t)‖` on compact local intervals. It uses
the almost-everywhere extension of the OpenAI-derived dissipative ODE
comparison. There is no exponential factor or spectral-gap assumption.
`LocalSpectralDefectAudit.lean` checks the dependencies of these results.

`InfiniteFilteredEquation.lean` derives the static-filter equation of this
same infinite solution, including the absolutely convergent subgrid fiber
with multiplier `χ(q) - χ(k)χ(q-k)`. It identifies the resolved finite algebra
without assuming autonomous Galerkin evolution. The pressure-corrected
subgrid force is `gχ = Leray(-2πi subgridConvection)`.

`LocalFilteredStrain.lean` derives the resolved strain equation along the
**full** velocity's material path. Writing `v = χu`, it retains the
coefficient reconstructions of

```text
D_u S_v = -S_v² - W_v² - Hess(p_v) + νΔS_v
          + sym ∇gχ + (u-v)·∇S_v.
```

Here `p_v` is resolved pressure; the difference from the filtered full
pressure is included in the Leray-projected `gχ`. Nonlinear output sets
include every resolved pair output. Both the matrix equation and its real
self-adjoint operator form are proved from the local solution's equation.
The static filter has no time derivative; a moving filter would add one.

`InfiniteConvectionEnergy.lean` proves, for `E = ∑ k, |u_k|²`, the all-input
bounds `|convection_q| ≤ |q|E`, `|p_q| ≤ E`, and
`|gχ_q| ≤ 2π|q|E` at a retained sharp-filter output. Square summability is
proved for the actual local solution. Reconstructing finitely many output
modes gives the spatially uniform bound `2π(∑ q, |q|)E`, with the output
cutoff cost explicit. This is not an estimate uniform over all output scales;
the local bound `E ≤ B` is not promoted to a global initial-energy estimate.

`FilteredHighHighExample.lean` supplies real, transverse, zero-mean finite
Fourier data whose retained velocity vanishes while its retained subgrid
force does not. The input squared frequencies are five and two; the output
squared frequency is one. This rules out discarding unresolved quadratic
feedback, not unforced global regularity. `LocalFilteredStrainAudit.lean`
checks the dependencies of the filtering identities, witness and estimates.

### Forced-construction pressure test

The [OpenAI forced blowup construction](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
claims bounded-energy singular solutions with smooth compactly supported
forcing (Theorem 1.1 and Corollary 10.6). If correct, this excludes a complete
regularity argument that would also cover those solutions. Its oscillatory
pulses have nonzero mean quadratic stresses despite zero angular mean;
mean-zero oscillation alone cannot justify discarding their feedback.

This does not refute the local identities above or automatically refute the
unforced misalignment-budget conjecture. An external body force adds
`sym ∇F` to the strain rate and `curl F` to the vorticity rate, with pressure
still determined by the actual equation. Setting `F = 0` removes these direct
inputs, not `R` or `νΔω`. Any proposed uniform closure must control the
surviving terms and identify its genuinely unforced mechanism. Integrability
on each compact local interval is not a bound uniform up to a singular time.

None of this closes the scale-critical dynamical misalignment budget,
the remaining field-transfer estimates, or unconditional BKM continuation.
The older route-audit summary below describes earlier layers, not the full
extent of the current local PDE construction.

### Earlier route-audit layers

The directory is best read as a route audit and obstruction library. It has
concrete theorem surfaces and some fully checked toy or boundary cases, but it
does not solve global regularity or blowup.

Current high-signal status:

- `BenH1Break.lean` refutes the original SG--Cole--Hopf H1 adjoint hypothesis
  in the normalized Fourier-mode shear model.
- The July stochastic-Lagrangian repair lane checks the conditional
  pushdown-to-BKM skeleton, dyadic absorption algebra, frozen-strain
  obstruction, and plane-wave pancake null structure.
- The live analytic pin is `ScaleLocalPancakeStrainBudget`: a pointwise,
  scale-local pancake strain budget for the self-consistent Navier-Stokes
  Biot-Savart strain. Until that is proved, the repaired route remains
  conditional.

Before moving files, keep the flat layout stable until the 4.31 stream is
settled, then prefer small import aggregators by cluster:

1. target surfaces;
2. finite-mode work;
3. Cole-Hopf/Fefferman interfaces;
4. witness-construction and obstruction regressions.

Each actual file move should be followed by import rewrites and a Lean build.
